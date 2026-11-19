import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import HolonicsResearch.Physics.HarperChain

/-!
# Chambers' identity for every period: `det(E − H(k)) = Δ(E) − 2cos k`, with multiplicities

[proved-standard; formal-checked] Source: #410's box "A library constitution equal to the
Harper/almost-Mathieu operator, with gap labels `N = s + tα` read from `CarryWord` and an edge
receiver whose channel count is `t`", part done in #1033 by `Physics/HarperChain`, whose "What is
not claimed" opens: "Chambers' polynomial identity `det(E − H(k)) = Δ(E) − 2cos k` for general
`q`: it is proved at `q = 2` and `q = 3`; for every `q` the two polynomials have the same roots
(item 4), but their multiplicities, and so the identity of the two monic polynomials of degree `q`,
are not written." This module writes it for every `q ≥ 1` and reads what follows. Records:
`research/records/2026-10-05_THE_GHOST_LIVES_IN_THE_GAP_THE_JOINTS_OF_THE_LENS.md` (joint J1) and
the record of #1033 (November 19, titled from "Legendre's local moves fix Γ(2)" to "a ring chain is
Harper's operator, in Lean"), whose §3 leaves "Chambers' polynomial identity for general `q` (the
multiplicities)" unstated.
Owner extended: `Physics/HarperChain` (`blochMatrix`, `blochMatrix_isHermitian`, `harperBloch`,
`harperPotential`, `transfer`, `monodromy`, `discriminant`, `exp_add_exp_neg`). Atlas rows read:
`gap.harper-ring-chain` (whose limits name the identity for general `q` as not stated),
`gap.label-chern-edge`, `trace.site-classification`, `winding.circulant-inertia` and
`wave.density-long-wave-reading`. Classical sources: W. G. Chambers, Phys. Rev. 140 (1965) A135
(the relation for Harper's matrix); the periodic Jacobi matrix and its Floquet discriminant
(van Moerbeke, Invent. Math. 37 (1976)); the continuant (Euler).

Notation: `a = (E − v_0, E − v_1, …)` the diagonal of `E − H`, `a↑ = (a_1, a_2, …)` its shift, and
`D_n(a)` the determinant of the open chain of `n` columns (`continuant`).

What is proved.

1. [proved-standard; formal-checked] **The open chain and its continuant.** `openChain a n` is the
   `n × n` matrix with `a` on the diagonal and `−1` beside it (`E − H` with open ends), and
   `continuant a n` its determinant. Laplace along row `0` and then column `0` gives the front
   recursion `D_(n+2)(a) = a_0 D_(n+1)(a↑) − D_n(a↑↑)` (`continuant_succ_succ`), with `D_0 = 1`
   and `D_1 = a_0` (`continuant_zero`, `continuant_one`; the shift by `openChain_submatrix_succ`).
2. [proved-standard; formal-checked] **The transfer reads the continuants.** `transferProd a n` is
   `T(a_(n−1)) ⋯ T(a_0)` with the owner's `transfer`, and the owner's `monodromy v E n` is
   `transferProd (E − v) n` (`monodromy_eq_transferProd`). It peels from the front,
   `transferProd a (n + 1) = transferProd a↑ n · T(a_0)` (`transferProd_succ'`,
   `transferProd_succ_zero_zero`, `transferProd_succ_zero_one`), so its upper-left entry is `D_n(a)`
   (`transferProd_zero_zero`) and its lower-right entry over `m + 2` columns is `−D_m(a↑)`
   (`transferProd_one_one`): for `q ≥ 2`, `Δ(E) = D_q(a) − D_(q−2)(a↑)`
   (`discriminant_eq_continuant`).
3. [proved-standard; formal-checked] **The corners enter affinely.** One entry changes a
   determinant by its cofactor, `det(A − c·e_ij) = det A − c·adj(A)_ji` (`det_sub_smul_single`), and
   a row update passes an entry in another row (`updateRow_sub_smul_single`). The open chain's two
   corner cofactors are one (`adjugate_openChain_last_zero`, `adjugate_openChain_zero_last`: each
   minor is triangular with `−1` on its diagonal), and the cofactor of both corners together is
   `−D_(q−2)(a↑)` (`adjugate_updateRow_openChain`, through `det_eq_adjugate_of_row`). Hence for every
   `q ≥ 2`, every complex diagonal `a` and every complex `c` and `d`, the open chain less `c` at
   `(q − 1, 0)` and less `d` at `(0, q − 1)` has
   `det = D_q(a) − c − d − c d D_(q−2)(a↑)` (`det_cornered`). For every `q ≥ 1`, `E − H(k)` is the
   open chain less the corners `e^(ik)` and `e^(−ik)` (`blochMatrix_eq_openChain`; at `q = 2` the
   corners lie on the hopping entries, at `q = 1` on the one entry).
4. [proved-standard; formal-checked] **Chambers' identity for every `q ≥ 1`.**
   `det(E − H(k)) = Δ(E) − 2cos k` for every real potential `v`, every real `k` and every complex
   `E` (`chambers`): at `q = 1` from the one entry, for `q ≥ 2` from item 3 with `c d = 1` and
   `c + d = 2cos k`. The owner's `chambers_two` and `chambers_three` are its cases `q = 2, 3`.
5. [proved-standard; formal-checked] **The polynomial form and the multiplicities.**
   `transferPoly v n` is the transfer with `X − v_j` in place of `E − v_j`, and `discriminantPoly v q`
   its trace `Δ_poly`, with `eval E Δ_poly = Δ(E)` (`transferPoly_eval`, `eval_discriminantPoly`).
   Chambers as polynomials: `charpoly H(k) = Δ_poly − C(2cos k)` (`charpoly_blochMatrix`, by
   `Polynomial.funext` from item 4), so `Δ_poly = charpoly H(k) + C(2cos k)` (`discriminantPoly_eq`)
   is monic (`discriminantPoly_monic`) of degree `q` (`discriminantPoly_natDegree`). The roots of
   `Δ_poly − 2cos k`, counted with multiplicity, are the eigenvalues of the Hermitian `H(k)`
   (`roots_level`): `Δ_poly − 2cos k = ∏_i (X − λ_i(k))` (`level_eq_prod`), and the multiplicity of
   `E` as a root is the number of eigenvalues equal to `E` (`rootMultiplicity_level`). This completes
   item 4 of the owner, which had the zero sets.
6. [proved-standard; formal-checked] **Readings.** (a) The Bloch phase is one term:
   `det(E − H(k)) − det(E − H(k′)) = 2cos k′ − 2cos k` (`det_sub_det`; as polynomials,
   `charpoly_sub_charpoly`), so a change of `k` moves only the level `2cos k` and the bands are the
   preimages of one function `Δ`: `E` is an eigenvalue of `H(k)` iff `Δ(E) = 2cos k`, for every
   potential, periodic or not (`det_eq_zero_iff_level`; the owner's `det_eq_zero_iff_discriminant`
   asked for periodicity, which only its route through the infinite chain needs); `E` is an
   eigenvalue of some `H(k)` iff `Δ(E)` is a real number in `[−2, 2]` (`exists_det_eq_zero_iff`); and
   every complex solution of `Δ(E) = 2cos k` is real (`real_of_level`). (b) The transfer commutes
   with conjugation (`monodromy_map_conj`), so `Δ(Ē) = conj Δ(E)` (`discriminant_conj`), `Δ(x)` is
   real for real `x` (`discriminant_real`), and so is `det(x − H(k))` (`det_real`). (c) For Harper's
   potential, `det(E − H(θ, k)) = Δ_θ(E) − 2cos k` (`harper_chambers`) and
   `charpoly H(θ, k) = Δ_θ,poly − C(2cos k)` (`harper_charpoly`).
7. [proved-standard; formal-checked] **Witnesses: the free chain at `q = 4`.** With `v = 0`,
   `Δ(E) = E⁴ − 4E² + 2` (`discriminant_free_four`, `discriminantPoly_free_four`) and
   `det(E − H(k)) = E⁴ − 4E² + 2 − 2cos k` (`chambers_free_four`). At `k = 0`, `H(0)` is the
   4-cycle and `charpoly H(0) = X·X·(X − 2)(X + 2)` (`charpoly_free_four_zero`), whose roots are
   `{0, 0, 2, −2}` (`roots_free_four_zero`), the eigenvalues of `H(0)` (`eigenvalues_free_four_zero`),
   with `0` a double root (`rootMultiplicity_free_four_zero`), while the zero set is `{0, 2, −2}`
   (`zeros_free_four_zero`): three points for a polynomial of degree four, the multiplicity a
   root-set statement does not see. At `k = π`, `det(E − H(π)) = (E² − 2)²` (`chambers_free_four_pi`),
   double at `±√2`. The double roots sit where `Δ` touches `±2` at an extremum
   (`Δ′(E) = 4E(E² − 2)`, `Δ(0) = 2`, `Δ(±√2) = −2`): the free chain's closed gaps.

What is not claimed.

- The integrated density of states as a spectral count: that each band carries one eigenvalue of
  `H(k)` for each `k`, so that `N = r/q` is the share below the `r`-th gap, needs the oscillation
  of `Δ` (for `|t| < 2`, `Δ − t` has `q` simple real roots, one in each band). Item 6 gives that every
  root is real; that the roots are simple inside the bands is not stated.
- The derivative of `Δ`, the band edges as the points where `Δ = ±2`, and which gaps are open:
  the extremum reading of item 7 is stated in prose, not as a theorem.
- The Cantor spectrum at irrational `α` (Avila–Jitomirskaya), the open gaps (Avila, You and Zhou),
  the Hall conductance and Chern number of the filled bands (TKNN, Středa's `t = ∂N/∂α`), the edge
  receiver with `t` channels (Hatsugai) and the Thouless pump (`pump.thouless-integer`). The box
  stays part done.
- A Bloch matrix with a complex phase: `det_cornered` holds for every complex pair of corners, so
  `det = Δ(E) − z − z⁻¹` follows for corners `z`, `z⁻¹`, but the owner's `blochMatrix` takes a real
  `k` and no complex form is defined here.

The computational object is the helical pair interaction read on the Bloch cell: the `q` columns
are a tube of `q` ticks whose transfer over one column is a move of determinant one, the hopping
bonds are the pair contacts that carry the current from column to column, and the Bloch condition
closes the tube by one more pair contact across its seam, the corners `e^(ik)` and `e^(−ik)`, a turn
and its conjugate. The identity says that the closed chain's determinant is the open tube's trace
less the seam's contact, which enters only through its sum `c + d` and its product `c d`; on the
circle the product is one and the sum is the level `2cos k`. Of the winding guide's six general
objects this touches the tube (the transfer over the cell, its trace, and the continuants as its
entries), the pair (the seam's conjugate corners, whose product one is the pairing), faces and
placement (the level `2cos k` as the face of the seam's turn, and the eigenvalues placed as the
roots of `Δ − 2cos k` with their multiplicities) and the helix (the Bloch phase read on the circle
through its cosine alone, its whole windings unseen). The cell holonomy and the tower thread stay
attached.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.Physics.HarperChambers

open Complex (exp I)
open scoped Matrix
open Holonics.Physics.HarperChain
open Polynomial (X C)

/-! ## 1. The open chain and its continuant -/

/-- [definition] **The open chain** of `n` columns: `a` on the diagonal, `−1` beside it. -/
def openChain (a : ℕ → ℂ) (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => (if i = j then a i else 0) - (if (i : ℕ) + 1 = j then 1 else 0) -
    (if (j : ℕ) + 1 = i then 1 else 0)

/-- [definition] **The continuant** `D_n(a)`: the determinant of the open chain. -/
def continuant (a : ℕ → ℂ) (n : ℕ) : ℂ := (openChain a n).det

/-- [proved-standard; formal-checked] Removing the first column of the chain shifts its diagonal. -/
theorem openChain_submatrix_succ (a : ℕ → ℂ) (n : ℕ) :
    (openChain a (n + 1)).submatrix Fin.succ Fin.succ = openChain (fun j => a (j + 1)) n := by
  ext i j
  simp [openChain, Fin.succ_inj]

/-- [proved-standard; formal-checked] The empty chain's continuant is one. -/
theorem continuant_zero (a : ℕ → ℂ) : continuant a 0 = 1 := by
  simp [continuant]

/-- [proved-standard; formal-checked] One column's continuant is its diagonal entry. -/
theorem continuant_one (a : ℕ → ℂ) : continuant a 1 = a 0 := by
  simp [continuant, openChain, Matrix.det_unique]

/-- [proved-standard; formal-checked] **The front recursion** `D_(n+2)(a) = a₀D_(n+1)(a↑) − D_n(a↑↑)`. -/
theorem continuant_succ_succ (a : ℕ → ℂ) (n : ℕ) :
    continuant a (n + 2) =
      a 0 * continuant (fun j => a (j + 1)) (n + 1) - continuant (fun j => a (j + 2)) n := by
  unfold continuant
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.sum_univ_succ]
  have hrest : ∑ i : Fin n, (-1 : ℂ) ^ ((i.succ.succ : Fin (n + 2)) : ℕ) *
      openChain a (n + 2) 0 i.succ.succ *
      ((openChain a (n + 2)).submatrix Fin.succ (i.succ.succ).succAbove).det = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    have : openChain a (n + 2) 0 i.succ.succ = 0 := by
      simp [openChain, Fin.ext_iff]
    rw [this, mul_zero, zero_mul]
  rw [hrest, add_zero, Fin.succAbove_zero, openChain_submatrix_succ]
  have hminor : ((openChain a (n + 2)).submatrix Fin.succ (Fin.succ 0).succAbove).det =
      -(openChain (fun j => a (j + 2)) n).det := by
    rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
    have hrest' : ∑ i : Fin n, (-1 : ℂ) ^ ((i.succ : Fin (n + 1)) : ℕ) *
        ((openChain a (n + 2)).submatrix Fin.succ (Fin.succ 0).succAbove) i.succ 0 *
        (((openChain a (n + 2)).submatrix Fin.succ (Fin.succ 0).succAbove).submatrix
          i.succ.succAbove Fin.succ).det = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      have : ((openChain a (n + 2)).submatrix Fin.succ (Fin.succ 0).succAbove) i.succ 0 = 0 := by
        simp [openChain, Fin.ext_iff]
      rw [this, mul_zero, zero_mul]
    rw [hrest', add_zero]
    have hsub : (((openChain a (n + 2)).submatrix Fin.succ (Fin.succ 0).succAbove).submatrix
        (0 : Fin (n + 1)).succAbove Fin.succ) = openChain (fun j => a (j + 2)) n := by
      ext i j
      simp [openChain, Fin.succ_inj]
    rw [hsub]
    simp [openChain]
  rw [hminor]
  simp [openChain]
  ring

/-! ## 2. The transfer reads the continuants -/

/-- [definition] **The transfer over `n` columns** with diagonal `a`: `T(a_(n−1)) ⋯ T(a_0)`. -/
def transferProd (a : ℕ → ℂ) : ℕ → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => 1
  | j + 1 => transfer (a j) * transferProd a j

/-- [proved-standard; formal-checked] The owner's monodromy is the transfer with diagonal `E − v`. -/
theorem monodromy_eq_transferProd (v : ℤ → ℝ) (E : ℂ) (n : ℕ) :
    monodromy v E n = transferProd (fun j => E - v j) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [monodromy, transferProd, ih]

/-- [proved-standard; formal-checked] The transfer peels its first column from the right. -/
theorem transferProd_succ' (a : ℕ → ℂ) (n : ℕ) :
    transferProd a (n + 1) = transferProd (fun j => a (j + 1)) n * transfer (a 0) := by
  induction n with
  | zero => simp [transferProd]
  | succ n ih => rw [transferProd, ih, transferProd, Matrix.mul_assoc]

/-- [proved-standard; formal-checked] The upper-left entry after peeling one column. -/
theorem transferProd_succ_zero_zero (a : ℕ → ℂ) (n : ℕ) :
    transferProd a (n + 1) 0 0 =
      a 0 * transferProd (fun j => a (j + 1)) n 0 0 + transferProd (fun j => a (j + 1)) n 0 1 := by
  rw [transferProd_succ']
  simp [transfer, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- [proved-standard; formal-checked] The upper-right entry is minus the shifted upper-left one. -/
theorem transferProd_succ_zero_one (a : ℕ → ℂ) (n : ℕ) :
    transferProd a (n + 1) 0 1 = -transferProd (fun j => a (j + 1)) n 0 0 := by
  rw [transferProd_succ']
  simp [transfer, Matrix.mul_apply, Fin.sum_univ_two]

/-- [proved-standard; formal-checked] **The upper-left entry of the transfer is the continuant.** -/
theorem transferProd_zero_zero (n : ℕ) : ∀ a : ℕ → ℂ, transferProd a n 0 0 = continuant a n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a
    match n with
    | 0 => simp [transferProd, continuant_zero]
    | 1 => simp [transferProd, transfer, continuant_one]
    | m + 2 =>
      rw [transferProd_succ_zero_zero, transferProd_succ_zero_one, continuant_succ_succ,
        ih (m + 1) (by omega), ih m (by omega)]
      ring

/-- [proved-standard; formal-checked] The lower-right entry over `m + 2` columns is `−D_m(a↑)`. -/
theorem transferProd_one_one (a : ℕ → ℂ) (m : ℕ) :
    transferProd a (m + 2) 1 1 = -continuant (fun j => a (j + 1)) m := by
  rw [transferProd, transferProd_succ', ← transferProd_zero_zero]
  simp [transfer, Matrix.mul_apply, Fin.sum_univ_two]

/-- [proved-standard; formal-checked] **The discriminant in continuants**: `Δ = D_q(a) − D_(q−2)(a↑)`. -/
theorem discriminant_eq_continuant (v : ℤ → ℝ) (E : ℂ) (m : ℕ) :
    discriminant v (m + 2) E = continuant (fun j => E - v j) (m + 2) -
      continuant (fun j => E - v ((j + 1 : ℕ) : ℤ)) m := by
  rw [discriminant, Matrix.trace_fin_two, monodromy_eq_transferProd, transferProd_zero_zero,
    transferProd_one_one]
  ring

/-! ## 3. The corners enter affinely -/

/-- [proved-standard; formal-checked] One entry changes a determinant by its cofactor. -/
theorem det_sub_smul_single {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) (i j : ι)
    (c : ℂ) : (A - c • Matrix.single i j 1).det = A.det - c * A.adjugate j i := by
  have h : A - c • Matrix.single i j 1 = A.updateRow i (A i + (-c) • Pi.single j 1) := by
    ext r s
    by_cases hr : r = i
    · subst hr
      by_cases hs : s = j
      · subst hs; simp; ring
      · simp [hs, Ne.symm hs]
    · simp [hr, Ne.symm hr]
  rw [h, Matrix.det_updateRow_add, Matrix.updateRow_eq_self, Matrix.det_updateRow_smul,
    Matrix.adjugate_apply]
  ring

/-- [proved-standard; formal-checked] A row update passes an entry in another row. -/
theorem updateRow_sub_smul_single {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ)
    {i l : ι} (hil : i ≠ l) (j : ι) (c : ℂ) (w : ι → ℂ) :
    (A - c • Matrix.single i j 1).updateRow l w = A.updateRow l w - c • Matrix.single i j 1 := by
  ext r s
  by_cases hr : r = l
  · subst hr; simp [hil]
  · simp [Matrix.single_apply, hr]

/-- [proved-standard; formal-checked] The open chain's cofactor at the corner `(q − 1, 0)` is one. -/
theorem adjugate_openChain_last_zero (a : ℕ → ℂ) (n : ℕ) :
    (openChain a (n + 1)).adjugate (Fin.last n) 0 = 1 := by
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix, Fin.succAbove_zero, Fin.succAbove_last,
    Matrix.det_of_isUpperTriangular]
  · have : ∀ i : Fin n, (openChain a (n + 1)).submatrix Fin.succ Fin.castSucc i i = -1 := by
      intro i
      simp [openChain, Fin.ext_iff]
      omega
    simp only [this, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Fin.val_zero,
      Fin.val_last, zero_add, ← mul_pow]
    norm_num
  · intro i j hij
    have hij' : (j : ℕ) < i := hij
    simp only [Matrix.submatrix_apply, openChain, Matrix.of_apply, Fin.ext_iff, Fin.val_succ,
      Fin.val_castSucc]
    split_ifs <;> first | omega | simp

/-- [proved-standard; formal-checked] The open chain's cofactor at the corner `(0, q − 1)` is one. -/
theorem adjugate_openChain_zero_last (a : ℕ → ℂ) (n : ℕ) :
    (openChain a (n + 1)).adjugate 0 (Fin.last n) = 1 := by
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix, Fin.succAbove_zero, Fin.succAbove_last,
    Matrix.det_of_isLowerTriangular]
  · have : ∀ i : Fin n, (openChain a (n + 1)).submatrix Fin.castSucc Fin.succ i i = -1 := by
      intro i
      simp [openChain, Fin.ext_iff]
      omega
    simp only [this, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Fin.val_zero,
      Fin.val_last, add_zero, ← mul_pow]
    norm_num
  · intro i j hij
    have hij' : (i : ℕ) < j := hij
    simp only [Matrix.submatrix_apply, openChain, Matrix.of_apply, Fin.ext_iff, Fin.val_succ,
      Fin.val_castSucc]
    split_ifs <;> first | omega | simp

/-- [proved-standard; formal-checked] A row that is a unit vector reads the determinant as a cofactor. -/
theorem det_eq_adjugate_of_row {ι : Type*} [Fintype ι] [DecidableEq ι] (P : Matrix ι ι ℂ)
    (i j : ι) (h : P i = Pi.single j 1) : P.det = P.adjugate j i := by
  rw [Matrix.adjugate_apply, ← h, Matrix.updateRow_eq_self]

/-- [proved-standard; formal-checked] **The cofactor of both corners** is `−D_(q−2)(a↑)`. -/
theorem adjugate_updateRow_openChain (a : ℕ → ℂ) (m : ℕ) :
    ((openChain a (m + 2)).updateRow (Fin.last (m + 1)) (Pi.single 0 1)).adjugate
      (Fin.last (m + 1)) 0 = -continuant (fun j => a (j + 1)) m := by
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix, Fin.succAbove_zero, Fin.succAbove_last,
    det_eq_adjugate_of_row _ (Fin.last m) 0, Matrix.adjugate_fin_succ_eq_det_submatrix,
    Fin.succAbove_zero, Fin.succAbove_last]
  · have hsub : (((openChain a (m + 2)).updateRow (Fin.last (m + 1)) (Pi.single 0 1)).submatrix
        Fin.succ Fin.castSucc).submatrix Fin.castSucc Fin.succ =
          openChain (fun j => a (j + 1)) m := by
      ext i j
      have hi : (Fin.castSucc i).succ ≠ Fin.last (m + 1) := by
        simp [Fin.ext_iff]
        omega
      simp only [Matrix.submatrix_apply, Matrix.updateRow_ne hi]
      simp [openChain, Fin.ext_iff]
    rw [hsub, continuant]
    simp only [Fin.val_zero, Fin.val_last, zero_add, add_zero, pow_succ]
    ring_nf
    simp
  · funext j
    simp only [Matrix.submatrix_apply, Fin.succ_last, Matrix.updateRow_self]
    by_cases hj : j = 0
    · subst hj; simp
    · rw [Pi.single_eq_of_ne hj, Pi.single_eq_of_ne]
      intro h
      exact hj (Fin.castSucc_eq_zero_iff.mp h)

/-- [proved-standard; formal-checked] **`E − H(k)` is the open chain less the corners `e^(±ik)`.** -/
theorem blochMatrix_eq_openChain (n : ℕ) (v : ℤ → ℝ) (k : ℝ) (E : ℂ) :
    E • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) - blochMatrix (n + 1) v k =
      openChain (fun j => E - v j) (n + 1) - exp (-(k * I)) • Matrix.single 0 (Fin.last n) 1 -
        exp (k * I) • Matrix.single (Fin.last n) 0 1 := by
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, blochMatrix, openChain,
    Matrix.of_apply, Matrix.single_apply, Fin.ext_iff, Fin.val_last, Fin.val_zero, smul_eq_mul]
  split_ifs <;> first | omega | ring

/-- [proved-standard; formal-checked] **The closed chain with corners `c`, `d`**:
`det = D_q(a) − c − d − c d D_(q−2)(a↑)` for every `q ≥ 2`. -/
theorem det_cornered (a : ℕ → ℂ) (m : ℕ) (c d : ℂ) :
    (openChain a (m + 2) - d • Matrix.single 0 (Fin.last (m + 1)) 1 -
        c • Matrix.single (Fin.last (m + 1)) 0 1).det =
      continuant a (m + 2) - c - d - c * d * continuant (fun j => a (j + 1)) m := by
  have h0L : (0 : Fin (m + 2)) ≠ Fin.last (m + 1) := by simp [Fin.ext_iff]
  have hA : (openChain a (m + 2) - d • Matrix.single 0 (Fin.last (m + 1)) 1).adjugate 0
      (Fin.last (m + 1)) = 1 + d * continuant (fun j => a (j + 1)) m := by
    rw [Matrix.adjugate_apply, updateRow_sub_smul_single _ h0L, det_sub_smul_single,
      ← Matrix.adjugate_apply, adjugate_updateRow_openChain, adjugate_openChain_zero_last]
    ring
  rw [det_sub_smul_single, hA, det_sub_smul_single, adjugate_openChain_last_zero]
  simp only [continuant]
  ring

/-! ## 4. Chambers' identity for every period -/

/-- [proved-standard; formal-checked] **Chambers' identity** for every `q ≥ 1`:
`det(E − H(k)) = Δ(E) − 2cos k`. -/
theorem chambers {q : ℕ} (hq : 0 < q) (v : ℤ → ℝ) (k : ℝ) (E : ℂ) :
    (E • (1 : Matrix (Fin q) (Fin q) ℂ) - blochMatrix q v k).det =
      discriminant v q E - ((2 * Real.cos k : ℝ) : ℂ) := by
  have he : exp (k * I) * exp (-(k * I)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, by omega⟩
  cases n with
  | zero =>
    rw [Matrix.det_fin_one, ← exp_add_exp_neg]
    simp [blochMatrix, discriminant, monodromy, transfer, Matrix.trace_fin_two]
    ring
  | succ m =>
    rw [blochMatrix_eq_openChain, det_cornered, discriminant_eq_continuant, ← exp_add_exp_neg, he]
    ring

/-! ## 5. The polynomial form and the multiplicities -/

/-- [definition] **The transfer with the energy `X`**: `[[X − v_j, −1], [1, 0]]` over `n` columns. -/
def transferPoly (v : ℤ → ℝ) : ℕ → Matrix (Fin 2) (Fin 2) (Polynomial ℂ)
  | 0 => 1
  | j + 1 => !![X - C (v j : ℂ), -1; 1, 0] * transferPoly v j

/-- [definition] **The discriminant polynomial** `Δ_poly`: the trace of the transfer over `q` columns. -/
def discriminantPoly (v : ℤ → ℝ) (q : ℕ) : Polynomial ℂ := (transferPoly v q).trace

/-- [proved-standard; formal-checked] Evaluating the polynomial transfer at `E` gives the monodromy. -/
theorem transferPoly_eval (v : ℤ → ℝ) (E : ℂ) (n : ℕ) :
    (Polynomial.evalRingHom E).mapMatrix (transferPoly v n) = monodromy v E n := by
  induction n with
  | zero => simp [transferPoly, monodromy]
  | succ n ih =>
    rw [transferPoly, map_mul, ih, monodromy]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [transfer]

/-- [proved-standard; formal-checked] `eval E Δ_poly = Δ(E)`. -/
theorem eval_discriminantPoly (v : ℤ → ℝ) (q : ℕ) (E : ℂ) :
    (discriminantPoly v q).eval E = discriminant v q E := by
  rw [discriminant, ← transferPoly_eval, discriminantPoly, Matrix.trace_fin_two,
    Matrix.trace_fin_two]
  simp

/-- [proved-standard; formal-checked] **Chambers as polynomials**: `charpoly H(k) = Δ_poly − C(2cos k)`. -/
theorem charpoly_blochMatrix {q : ℕ} (hq : 0 < q) (v : ℤ → ℝ) (k : ℝ) :
    (blochMatrix q v k).charpoly = discriminantPoly v q - C ((2 * Real.cos k : ℝ) : ℂ) := by
  refine Polynomial.funext fun E => ?_
  rw [Matrix.eval_charpoly, Polynomial.eval_sub, Polynomial.eval_C, eval_discriminantPoly,
    ← chambers hq v k E, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]

/-- [proved-standard; formal-checked] `Δ_poly = charpoly H(k) + C(2cos k)` at every `k`. -/
theorem discriminantPoly_eq {q : ℕ} (hq : 0 < q) (v : ℤ → ℝ) (k : ℝ) :
    discriminantPoly v q = (blochMatrix q v k).charpoly + C ((2 * Real.cos k : ℝ) : ℂ) := by
  rw [charpoly_blochMatrix hq]
  ring

/-- [proved-standard; formal-checked] **`Δ_poly` is monic** for every `q ≥ 1`. -/
theorem discriminantPoly_monic {q : ℕ} (hq : 0 < q) (v : ℤ → ℝ) : (discriminantPoly v q).Monic := by
  rw [discriminantPoly_eq hq v 0]
  refine (Matrix.charpoly_monic _).add_of_left ?_
  rw [Matrix.charpoly_degree_eq_dim, Fintype.card_fin]
  exact lt_of_le_of_lt Polynomial.degree_C_le (by exact_mod_cast hq)

/-- [proved-standard; formal-checked] **`Δ_poly` has degree `q`.** -/
theorem discriminantPoly_natDegree {q : ℕ} (hq : 0 < q) (v : ℤ → ℝ) :
    (discriminantPoly v q).natDegree = q := by
  rw [discriminantPoly_eq hq v 0, Polynomial.natDegree_add_C, Matrix.charpoly_natDegree_eq_dim,
    Fintype.card_fin]

/-- [proved-standard; formal-checked] **The roots of `Δ − 2cos k`, with multiplicity, are the
eigenvalues of `H(k)`.** -/
theorem roots_level {q : ℕ} (hq : 0 < q) (v : ℤ → ℝ) (k : ℝ) :
    (discriminantPoly v q - C ((2 * Real.cos k : ℝ) : ℂ)).roots =
      Multiset.map (fun i => ((blochMatrix_isHermitian q v k).eigenvalues i : ℂ))
        Finset.univ.val := by
  rw [← charpoly_blochMatrix hq, (blochMatrix_isHermitian q v k).roots_charpoly_eq_eigenvalues]
  rfl

/-- [proved-standard; formal-checked] `Δ_poly − C(2cos k) = ∏_i (X − λ_i(k))`. -/
theorem level_eq_prod {q : ℕ} (hq : 0 < q) (v : ℤ → ℝ) (k : ℝ) :
    discriminantPoly v q - C ((2 * Real.cos k : ℝ) : ℂ) =
      ∏ i, (X - C ((blochMatrix_isHermitian q v k).eigenvalues i : ℂ)) := by
  rw [← charpoly_blochMatrix hq, (blochMatrix_isHermitian q v k).charpoly_eq]
  rfl

/-- [proved-standard; formal-checked] A root's multiplicity is the number of eigenvalues at it. -/
theorem rootMultiplicity_level {q : ℕ} (hq : 0 < q) (v : ℤ → ℝ) (k : ℝ) (E : ℂ) :
    (discriminantPoly v q - C ((2 * Real.cos k : ℝ) : ℂ)).rootMultiplicity E =
      (Finset.univ.filter fun i => ((blochMatrix_isHermitian q v k).eigenvalues i : ℂ) = E).card := by
  classical
  rw [← Polynomial.count_roots, roots_level hq, Multiset.count_map]
  simp only [Finset.card, Finset.filter_val, eq_comm]

/-! ## 6. Readings -/

/-- [proved-standard; formal-checked] **The Bloch phase is one term**:
`det(E − H(k)) − det(E − H(k′)) = 2cos k′ − 2cos k`. -/
theorem det_sub_det {q : ℕ} (hq : 0 < q) (v : ℤ → ℝ) (k k' : ℝ) (E : ℂ) :
    (E • (1 : Matrix (Fin q) (Fin q) ℂ) - blochMatrix q v k).det -
        (E • (1 : Matrix (Fin q) (Fin q) ℂ) - blochMatrix q v k').det =
      ((2 * Real.cos k' - 2 * Real.cos k : ℝ) : ℂ) := by
  rw [chambers hq, chambers hq]
  push_cast
  ring

/-- [proved-standard; formal-checked] The characteristic polynomials differ by the constant
`2cos k′ − 2cos k`. -/
theorem charpoly_sub_charpoly {q : ℕ} (hq : 0 < q) (v : ℤ → ℝ) (k k' : ℝ) :
    (blochMatrix q v k).charpoly - (blochMatrix q v k').charpoly =
      C ((2 * Real.cos k' - 2 * Real.cos k : ℝ) : ℂ) := by
  rw [charpoly_blochMatrix hq, charpoly_blochMatrix hq, Complex.ofReal_sub, map_sub C]
  ring

/-- [proved-standard; formal-checked] **The bands are preimages of `Δ`**, for every potential. -/
theorem det_eq_zero_iff_level {q : ℕ} (hq : 0 < q) (v : ℤ → ℝ) (k : ℝ) (E : ℂ) :
    (E • (1 : Matrix (Fin q) (Fin q) ℂ) - blochMatrix q v k).det = 0 ↔
      discriminant v q E = ((2 * Real.cos k : ℝ) : ℂ) := by
  rw [chambers hq, sub_eq_zero]

/-- [proved-standard; formal-checked] `E` is an eigenvalue of some `H(k)` iff `Δ(E) ∈ [−2, 2]`. -/
theorem exists_det_eq_zero_iff {q : ℕ} (hq : 0 < q) (v : ℤ → ℝ) (E : ℂ) :
    (∃ k : ℝ, (E • (1 : Matrix (Fin q) (Fin q) ℂ) - blochMatrix q v k).det = 0) ↔
      ∃ t : ℝ, -2 ≤ t ∧ t ≤ 2 ∧ discriminant v q E = t := by
  simp_rw [det_eq_zero_iff_level hq]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨2 * Real.cos k, by linarith [Real.neg_one_le_cos k], by linarith [Real.cos_le_one k], hk⟩
  · rintro ⟨t, ht0, ht1, ht⟩
    refine ⟨Real.arccos (t / 2), ?_⟩
    rw [Real.cos_arccos (by linarith) (by linarith), ht]
    congr 1
    ring

/-- [proved-standard; formal-checked] Every complex solution of `Δ(E) = 2cos k` is real. -/
theorem real_of_level {q : ℕ} (hq : 0 < q) (v : ℤ → ℝ) (k : ℝ) {E : ℂ}
    (hE : discriminant v q E = ((2 * Real.cos k : ℝ) : ℂ)) : ∃ r : ℝ, E = r := by
  have hp : (blochMatrix q v k).charpoly ≠ 0 := (Matrix.charpoly_monic _).ne_zero
  have hroot : E ∈ (blochMatrix q v k).charpoly.roots := by
    rw [Polynomial.mem_roots hp, Polynomial.IsRoot.def, Matrix.eval_charpoly, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal, det_eq_zero_iff_level hq]
    exact hE
  rw [(blochMatrix_isHermitian q v k).roots_charpoly_eq_eigenvalues] at hroot
  obtain ⟨i, -, hi⟩ := Multiset.mem_map.mp hroot
  exact ⟨_, hi.symm⟩

/-- [proved-standard; formal-checked] The transfer commutes with conjugation of the energy. -/
theorem monodromy_map_conj (v : ℤ → ℝ) (E : ℂ) (n : ℕ) :
    (starRingEnd ℂ).mapMatrix (monodromy v E n) = monodromy v (starRingEnd ℂ E) n := by
  induction n with
  | zero => simp [monodromy]
  | succ n ih =>
    rw [monodromy, map_mul, ih, monodromy]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [transfer]

/-- [proved-standard; formal-checked] `Δ(Ē) = conj Δ(E)`. -/
theorem discriminant_conj (v : ℤ → ℝ) (q : ℕ) (E : ℂ) :
    starRingEnd ℂ (discriminant v q E) = discriminant v q (starRingEnd ℂ E) := by
  rw [discriminant, discriminant, ← monodromy_map_conj, Matrix.trace_fin_two, Matrix.trace_fin_two]
  simp

/-- [proved-standard; formal-checked] **`Δ` is real at a real energy.** -/
theorem discriminant_real (v : ℤ → ℝ) (q : ℕ) (x : ℝ) : ∃ r : ℝ, discriminant v q x = r :=
  Complex.conj_eq_iff_real.mp (by rw [discriminant_conj, Complex.conj_ofReal])

/-- [proved-standard; formal-checked] `det(x − H(k))` is real at a real energy. -/
theorem det_real {q : ℕ} (hq : 0 < q) (v : ℤ → ℝ) (k x : ℝ) :
    ∃ r : ℝ, ((x : ℂ) • (1 : Matrix (Fin q) (Fin q) ℂ) - blochMatrix q v k).det = r := by
  obtain ⟨r, hr⟩ := discriminant_real v q x
  exact ⟨r - 2 * Real.cos k, by rw [chambers hq, hr]; push_cast; ring⟩

/-- [proved-standard; formal-checked] **Chambers for Harper's matrix**:
`det(E − H(θ, k)) = Δ_θ(E) − 2cos k`. -/
theorem harper_chambers {q : ℕ} (hq : 0 < q) (p : ℤ) (θ k : ℝ) (E : ℂ) :
    (E • (1 : Matrix (Fin q) (Fin q) ℂ) - harperBloch p q θ k).det =
      discriminant (harperPotential 1 ((p : ℝ) / q) θ) q E - ((2 * Real.cos k : ℝ) : ℂ) :=
  chambers hq _ k E

/-- [proved-standard; formal-checked] Harper's characteristic polynomial is `Δ_θ,poly − C(2cos k)`. -/
theorem harper_charpoly {q : ℕ} (hq : 0 < q) (p : ℤ) (θ k : ℝ) :
    (harperBloch p q θ k).charpoly =
      discriminantPoly (harperPotential 1 ((p : ℝ) / q) θ) q - C ((2 * Real.cos k : ℝ) : ℂ) :=
  charpoly_blochMatrix hq _ k

/-! ## 7. Witnesses: the free chain at `q = 4` -/

/-- [proved-standard; formal-checked] At `v = 0`, `q = 4`: `Δ(E) = E⁴ − 4E² + 2`. -/
theorem discriminant_free_four (E : ℂ) : discriminant (fun _ => 0) 4 E = E ^ 4 - 4 * E ^ 2 + 2 := by
  simp [discriminant, monodromy, transfer, Matrix.trace_fin_two]
  ring

/-- [proved-standard; formal-checked] At `v = 0`, `q = 4`: `det(E − H(k)) = E⁴ − 4E² + 2 − 2cos k`. -/
theorem chambers_free_four (k : ℝ) (E : ℂ) :
    (E • (1 : Matrix (Fin 4) (Fin 4) ℂ) - blochMatrix 4 (fun _ => 0) k).det =
      E ^ 4 - 4 * E ^ 2 + 2 - ((2 * Real.cos k : ℝ) : ℂ) := by
  rw [chambers (by norm_num), discriminant_free_four]

/-- [proved-standard; formal-checked] At `v = 0`, `q = 4`: `Δ_poly = X⁴ − 4X² + 2`. -/
theorem discriminantPoly_free_four : discriminantPoly (fun _ => 0) 4 = X ^ 4 - 4 * X ^ 2 + 2 := by
  refine Polynomial.funext fun E => ?_
  rw [eval_discriminantPoly, discriminant_free_four]
  simp

/-- [proved-standard; formal-checked] The 4-cycle's characteristic polynomial is `X·X·(X − 2)(X + 2)`. -/
theorem charpoly_free_four_zero :
    (blochMatrix 4 (fun _ => 0) 0).charpoly =
      (({0, 0, 2, -2} : Multiset ℂ).map fun a => X - C a).prod := by
  have h2 : C (2 : ℂ) = 2 := map_ofNat C 2
  rw [charpoly_blochMatrix (by norm_num), discriminantPoly_free_four]
  simp [h2]
  ring

/-- [proved-standard; formal-checked] Its roots, with multiplicity, are `{0, 0, 2, −2}`. -/
theorem roots_free_four_zero :
    (blochMatrix 4 (fun _ => 0) 0).charpoly.roots = {0, 0, 2, -2} := by
  rw [charpoly_free_four_zero, Polynomial.roots_multiset_prod_X_sub_C]

/-- [proved-standard; formal-checked] The eigenvalues of the 4-cycle are `0, 0, 2, −2`. -/
theorem eigenvalues_free_four_zero :
    Multiset.map (fun i => ((blochMatrix_isHermitian 4 (fun _ => 0) 0).eigenvalues i : ℂ))
      Finset.univ.val = {0, 0, 2, -2} := by
  rw [← roots_free_four_zero,
    (blochMatrix_isHermitian 4 (fun _ => 0) 0).roots_charpoly_eq_eigenvalues]
  rfl

/-- [proved-standard; formal-checked] **`0` is a double root** at `k = 0`. -/
theorem rootMultiplicity_free_four_zero :
    (blochMatrix 4 (fun _ => 0) 0).charpoly.rootMultiplicity 0 = 2 := by
  classical
  rw [← Polynomial.count_roots, roots_free_four_zero]
  simp

/-- [proved-standard; formal-checked] **The zero set at `k = 0` is `{0, 2, −2}`**: three points. -/
theorem zeros_free_four_zero :
    {E : ℂ | (E • (1 : Matrix (Fin 4) (Fin 4) ℂ) - blochMatrix 4 (fun _ => 0) 0).det = 0} =
      {0, 2, -2} := by
  ext E
  simp only [Set.mem_ofPred_eq, chambers_free_four, Real.cos_zero, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · intro h
    have h' : E * E * ((E - 2) * (E + 2)) = 0 := by
      push_cast at h
      linear_combination h
    rcases mul_eq_zero.mp h' with h1 | h1
    · left; exact mul_self_eq_zero.mp h1
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · right; left; linear_combination h2
      · right; right; linear_combination h2
  · rintro (rfl | rfl | rfl) <;> push_cast <;> ring

/-- [proved-standard; formal-checked] At `k = π`: `det(E − H(π)) = (E² − 2)²`, double at `±√2`. -/
theorem chambers_free_four_pi (E : ℂ) :
    (E • (1 : Matrix (Fin 4) (Fin 4) ℂ) - blochMatrix 4 (fun _ => 0) Real.pi).det =
      (E ^ 2 - 2) ^ 2 := by
  rw [chambers_free_four, Real.cos_pi]
  push_cast
  ring

end Holonics.Physics.HarperChambers
