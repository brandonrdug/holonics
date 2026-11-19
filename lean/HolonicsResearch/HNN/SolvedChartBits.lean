import Holonics.HNN.LatticeDeposit
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Data.Nat.Size
import Mathlib.Data.Int.NatAbs
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Topology.Algebra.Order.Archimedean

/-!
# HNN.SolvedChartBits: the solved chart's bits follow the Hadamard bound of the carried Gram

The #410 box reads: "The solved charts' bits: `H⁻¹` follows the Hadamard bound of the carried
Grams; a factored `H′` or prime images verified over ℚ are owed before long exposures
(`HNN/{Normal,Retention}`)". It carries the `[open]` paragraphs of `Holonics/HNN/Normal.lean` ("the
bits of the solved charts `H⁻¹`, which follow the Hadamard bound of the carried Grams") and
`Holonics/HNN/Retention.lean` ("the solved charts `H⁻¹` of the carried Grams, whose bits follow the
Hadamard bound as the Grams fill in"). A bit count is stated in the house form of
`HNN/LatticeDeposit` (`lattice_bits_bounded`, `remainder_rat_bits_bounded`): `Nat.size` of a reduced
rational's numerator's `Int.natAbs` and of its denominator.

Sources: the box and the two open paragraphs; the record of September 25,
`2026-09-25_THE_CLASSICAL_LOSS_IS_THE_PERCEIVED_DIFFERENCE_AND_THE_DEPOSITION_REMAINDER_IS_A_REPRESENTATION_RESIDUAL.md`
(the normal laws carried unrounded solved charts `H⁻¹` whose bits grew by the Hadamard bound, which
Decision 22 bounded); the tower record of October 24,
`2026-10-24_THE_TOWER_HEARS_THE_HOLONICS_TEXT_AND_EVERY_LOOK_IS_READ_BY_ITS_LOCK.md` (a minor's
determinant and its Cramer kernel read by the Chinese remainder theorem past twice Hadamard's
bound); the record of October 22
(`2026-10-22_NATIVE_RATIONAL_WORKING_SET_AND_PORT_REFERENCE_BOUNDARY.md`, a stored minor bounded by
Hadamard). Atlas rows served: `hnn.normal-prox-step` and `hnn.certified-normal-step` (the chart
`H′⁻¹` the deposit moves through), `hnn.carried-gram-posdef` and `hnn.lattice-prox` (the carried
Gram on its lattice), `hnn.solved-chart-refinement` (the running chart `X̂ ≈ H⁻¹`, whose target this
file sizes), `linalg.prime-image-certificate` and `linalg.prime-image-injective` (bounded prime
charts, CRT and verification over ℚ), `radix.residue-address` (CRT on a bank of rings),
`radix.two-place-reconstruction` and `hnn.l1-carrier` (an integer read whole from a wrapping
register under a declared bound). No atlas row states Hadamard's inequality itself
(`rg -n -i hadamard docs/atlas/` finds only `rh.hadamard-foster-form`, a different Hadamard).

[proved-standard; formal-checked] What is proved, classical.

1. **Hadamard's inequality for a Gram** (`det_le_prod_diag`): a real positive semidefinite `H` has
   `det H ≤ Π_i H_ii`. A zero diagonal entry zeroes its column (`det_eq_zero_of_diag_eq_zero`);
   otherwise `D H D` with `D = diag(H_ii^(−1/2))` has unit diagonal, and its eigenvalues `λ ≥ 0`
   with `Σ λ = n` give `Π λ ≤ Π e^(λ−1) = 1` (`det_le_one_of_diag_eq_one`). A principal submatrix
   likewise (`det_submatrix_le_prod_diag`), and every entry has `H_ij² ≤ H_ii H_jj`
   (`sq_entry_le_diag_mul_diag`). On `ℤ` through the cast: `int_det_le_prod_diag`; for a Gram
   `XᵀX` of an integer `X`, `0 ≤ det(XᵀX) ≤ Π_i Σ_k X_ki²` (`gram_det_le_prod_diag`), and
   `det(XᵀX) ≠ 0` makes its real cast positive definite (`gram_map_posDef`).
2. **The solved chart's numerator and denominator** (`adjugate_eq_det_smul_inv`, `rat_inv_eq`,
   `rat_inv_apply`): `H⁻¹ = (det H)⁻¹ · adj H`; over `ℚ` an integer `H` has
   `(H⁻¹)_ij = adj(H)_ij / det H`. For a positive definite `H` the adjugate is positive definite
   (`adjugate_posDef`), its diagonal is a principal minor with `0 ≤ adj(H)_ii ≤ Π_(k≠i) H_kk`
   (`adjugate_diag_le_prod_erase`, through the reindexing `prod_erase_eq_prod_succAbove`), and every
   cofactor has `adj(H)_ij² ≤ Π_(k≠i) H_kk · Π_(k≠j) H_kk` (`sq_adjugate_le`). For an integer
   positive definite `H`: `0 < det H ≤ Π_k H_kk` (`int_det_pos_le`) and
   `|adj(H)_ij| ≤ Π_k H_kk` (`int_abs_adjugate_le`, each `H_kk ≥ 1` by `int_diag_pos`).
3. **Prime images verified over ℚ** (the reading of "prime images verified over ℚ" is
   `agent-inferred`): two integers of magnitude at most `B` that agree modulo `m > 2B` are equal
   (`eq_of_modEq_of_abs_le`), and the symmetric representative of the residue reads the integer
   (`valMinAbs_intCast_eq`); agreement modulo pairwise coprime moduli is agreement modulo their
   product (`modEq_prod_of_modEq`), distinct primes are pairwise coprime
   (`primes_pairwise_coprime`), so images modulo primes whose product passes `2B` fix the integer
   (`eq_of_prime_images`). The cheap certificate: `H Y = d · 1` over `ℤ` with `d ≠ 0` gives
   `H⁻¹ = d⁻¹ Y` over `ℚ` (`inv_eq_of_mul_eq_smul_one`).
4. **A factored `H′`** (`det_ldl`, `ldl_leading_block`, `ldl_leading_minor`, `ldl_pivot`): for
   `H = L D Lᵀ` with `L` unit lower triangular, `det H = Π_i D_i`, the leading `k × k` block of `H`
   is `L_k D_k L_kᵀ`, so the leading minor is `Δ_k = Π_(a<k) D_a` and `Δ_(k+1) = Δ_k D_k`.
5. **A rational margin is a real one** (`posDef_of_rat_margin`): a symmetric rational `H` with
   `c |v|² ≤ vᵀHv` on every rational `v`, `c > 0`, has a positive definite real cast. Both sides are
   continuous on `ℝⁿ` and `ℚⁿ` is dense, so the margin holds on `ℝⁿ`.

[proved-derived; formal-checked] What is proved, the house's joins.

6. **The solved chart's bits** (`solved_chart_num_den_le`, `solved_chart_bits`,
   `solved_chart_size_le`): for an integer positive definite Gram `H` with `P = Π_k H_kk`, every
   entry of `H⁻¹`, reduced over `ℚ`, has numerator and denominator of magnitude at most `P`
   (`rat_div_num_den_le`), so each takes at most `Σ_k log₂ H_kk + 1` bits (`size_le_logb_add_one`,
   `size_diag_prod_le_logb`), and on a nonempty index the two together at most
   `2 Σ_k size(H_kk)` bits (`size_mul_le`, `size_prod_le`, `size_diag_prod_le_sum_size`). All
   entries share the denominator `det H ≤ P`.
7. **On the carried lattice** (`lattice_inv_eq`, `lattice_inv_apply`, `lattice_solved_chart_bits`):
   the carried Gram `H = u_L · N` on the lattice of `HNN/LatticeDeposit.unit` (`u_L = 2^(−L)`, `N`
   integer) has `H⁻¹ = 2^L N⁻¹`, so its entries are `2^L adj(N)_ij / det N`, with numerators of at
   most `L + size(P)` bits and denominators of at most `size(P)` bits, `P = Π_k N_kk`.
8. **A multimodular solve is certified by the Hadamard bound** (`solved_chart_of_prime_images`):
   candidates `d`, `Y` of magnitude at most `P` that agree with `det H` and `adj H` modulo primes
   whose product passes `2P` are `det H` and `adj H`, and `H⁻¹ = d⁻¹ Y` over `ℚ`.
9. **The factored chart's pivots** (`int_leading_minor_pos_le`, `ldl_pivot_ratio`,
   `ldl_pivot_num_den_le`): for an integer positive definite `H = L D Lᵀ` over `ℚ`, each pivot is
   `D_k = Δ_(k+1) / Δ_k`, a ratio of integer leading minors with `0 < Δ_j ≤ Π_(a<j) H_aa`, so its
   reduced numerator and denominator are bounded by Hadamard on the leading blocks.
10. **The carried Gram needs no hypothesis beyond the lattice rule** (`carried_gram_map_posDef`,
   `carried_lattice_map_posDef`, `carried_lattice_solved_chart_bits`): item 5 composed with
   `HNN/LatticeDeposit.carried_gram_posDef_rule` (each entry within `u_L` of an unrounded Gram that
   dominates the unit prior, `0 < L_R`, `2 L_R n ≤ 2^L`) gives the positive definite real cast of a
   symmetric carried Gram, and of its integer coordinates `N` when the carried Gram is `u_L · N`, so
   items 6 and 7 hold for the carried chart under the rule's own hypotheses and its symmetry.

What is not claimed. The bound is an envelope: the realized lengths of a chart are read by a
ruler, and Hadamard's product is reached by a diagonal Gram (orthogonal features). The bound grows
with the diagonal, as the self-pairings accumulate, and the off-diagonal fill stands beneath it.
No solver is built: no choice of primes, no elimination over `𝔽_p`, no Bareiss or `LDLᵀ` routine
and no proof that one terminates; the theorems certify candidates once found, and the cheap
certificate verifies any candidate however it was found. The cofactor bound is stated for positive
definite `H` (the adjugate's positivity is read through `det H · H⁻¹`); Hadamard itself covers the
semidefinite boundary. The carried Gram's symmetry is a hypothesis of item 10 (the lattice rule
bounds entries, not their mirror), and the owner's statements on the function form `σ → σ → ℚ` are
read here on `Matrix n n ℚ`. The length of exposure at which these bits pass a
declared carrier width is not read. The word-level certificate of the lattice rule and the
value-level kernel of a frozen aeon (the other open items of the two paragraphs) are untouched.

The computational object is the helical pair interaction read on the carried Gram:
`H = Σ w f fᵀ` is the pairing of the features with themselves, its diagonal entries are each
coordinate's self-pairing, and Hadamard's inequality says the joint volume of the pairing is at
most the product of the self-pairings, so the solved chart `adj H / det H`, which reads the pair
back, is carried at a width those self-pairings set. Of the winding guide's six general objects
this touches the pair (the Gram as the pairing) and faces and placement (the solved chart as a face
of the Gram at a declared width, its residues read in prime charts and placed by the Chinese
remainder theorem, the integer read at its symmetric representative); the helix, the cell
holonomy, the tube and the tower thread stay attached.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.HNN.SolvedChartBits

open Matrix
open Holonics.HNN.LatticeDeposit (unit carried_gram_posDef_rule)

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## 1. Hadamard's inequality for a Gram -/

/-- [proved-standard; formal-checked] A positive semidefinite matrix with a zero diagonal entry has
a zero column there, so its determinant vanishes. -/
theorem det_eq_zero_of_diag_eq_zero {H : Matrix n n ℝ} (hH : H.PosSemidef) {i : n} (hi : H i i = 0) :
    H.det = 0 := by
  have h0 : star (Pi.single i (1 : ℝ)) ⬝ᵥ (H *ᵥ Pi.single i 1) = 0 := by
    simpa [mulVec_single_one] using hi
  have hcol := (hH.dotProduct_mulVec_zero_iff (Pi.single i 1)).1 h0
  refine det_eq_zero_of_column_eq_zero i fun k => ?_
  simpa [mulVec_single_one] using congrFun hcol k

/-- [proved-standard; formal-checked] A positive semidefinite matrix with unit diagonal has
`det ≤ 1`: its eigenvalues sum to `n` and `λ ≤ e^(λ − 1)`. -/
theorem det_le_one_of_diag_eq_one {A : Matrix n n ℝ} (hA : A.PosSemidef) (h : ∀ i, A i i = 1) :
    A.det ≤ 1 := by
  have hdet : A.det = ∏ i, hA.1.eigenvalues i := by simpa using hA.1.det_eq_prod_eigenvalues
  have htr : ∑ i, hA.1.eigenvalues i = Fintype.card n := by
    have := hA.1.trace_eq_sum_eigenvalues
    simp only [RCLike.ofReal_real_eq_id, id_eq] at this
    rw [← this, trace]
    simp [diag, h]
  rw [hdet]
  calc ∏ i, hA.1.eigenvalues i ≤ ∏ i, Real.exp (hA.1.eigenvalues i - 1) := by
        refine Finset.prod_le_prod (fun i _ => hA.eigenvalues_nonneg i) fun i _ => ?_
        linarith [Real.add_one_le_exp (hA.1.eigenvalues i - 1)]
    _ = 1 := by
        rw [← Real.exp_sum, Finset.sum_sub_distrib, htr]
        simp

/-- [proved-standard; formal-checked] **Hadamard's inequality for a Gram:** a real positive
semidefinite `H` has `det H ≤ Π_i H_ii`. -/
theorem det_le_prod_diag {H : Matrix n n ℝ} (hH : H.PosSemidef) : H.det ≤ ∏ i, H i i := by
  by_cases h0 : ∃ i, H i i = 0
  · obtain ⟨i, hi⟩ := h0
    rw [det_eq_zero_of_diag_eq_zero hH hi]
    exact (Finset.prod_eq_zero (f := fun j => H j j) (Finset.mem_univ i) hi).ge
  · push Not at h0
    have hpos : ∀ i, 0 < H i i := fun i => lt_of_le_of_ne hH.diag_nonneg (h0 i).symm
    let d : n → ℝ := fun i => (Real.sqrt (H i i))⁻¹
    have hd : ∀ i, d i * d i * H i i = 1 := by
      intro i
      have hs := Real.mul_self_sqrt (hpos i).le
      have hs0 : Real.sqrt (H i i) ≠ 0 := (Real.sqrt_pos.2 (hpos i)).ne'
      simp only [d]
      field_simp
      linarith
    have hA : ((diagonal d)ᴴ * H * diagonal d).PosSemidef := hH.conjTranspose_mul_mul_same _
    have hdiag : ∀ i, ((diagonal d)ᴴ * H * diagonal d) i i = 1 := by
      intro i
      simp only [conjTranspose_eq_transpose_of_trivial, diagonal_transpose, diagonal_mul,
        mul_diagonal]
      linear_combination hd i
    have hle := det_le_one_of_diag_eq_one hA hdiag
    have hdetA : ((diagonal d)ᴴ * H * diagonal d).det = (∏ i, d i) * (∏ i, d i) * H.det := by
      simp [det_mul, det_diagonal]
      ring
    have hprod : (∏ i, d i) * (∏ i, d i) * ∏ i, H i i = 1 := by
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      simp [hd]
    have hP : 0 ≤ ∏ i, H i i := Finset.prod_nonneg fun i _ => (hpos i).le
    calc H.det = (∏ i, H i i) * ((∏ i, d i) * (∏ i, d i) * H.det) := by
          linear_combination (-H.det) * hprod
      _ ≤ (∏ i, H i i) * 1 := by rw [← hdetA]; exact mul_le_mul_of_nonneg_left hle hP
      _ = ∏ i, H i i := mul_one _

omit [Fintype n] [DecidableEq n] in
/-- [proved-standard; formal-checked] **Hadamard on a principal submatrix:** the minor of a
positive semidefinite `H` on the rows and columns `e` is at most the product of their diagonal. -/
theorem det_submatrix_le_prod_diag {m : Type*} [Fintype m] [DecidableEq m] {H : Matrix n n ℝ}
    (hH : H.PosSemidef) (e : m → n) : (H.submatrix e e).det ≤ ∏ k, H (e k) (e k) :=
  det_le_prod_diag (hH.submatrix e)

omit [Fintype n] [DecidableEq n] in
/-- [proved-standard; formal-checked] Every entry of a positive semidefinite `H` has
`H_ij² ≤ H_ii H_jj` (the `2 × 2` principal minor is nonnegative). -/
theorem sq_entry_le_diag_mul_diag {H : Matrix n n ℝ} (hH : H.PosSemidef) (i j : n) :
    H i j ^ 2 ≤ H i i * H j j := by
  have h2 := (hH.submatrix ![i, j]).det_nonneg
  rw [det_fin_two] at h2
  have hs : H j i = H i j := by simpa using hH.1.apply i j
  simp only [submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at h2
  rw [hs] at h2
  rw [sq]
  linarith

/-- [proved-standard; formal-checked] **Hadamard on `ℤ`:** an integer matrix whose real cast is
positive semidefinite has `0 ≤ det H ≤ Π_i H_ii`. -/
theorem int_det_le_prod_diag {H : Matrix n n ℤ} (hH : (H.map (Int.cast : ℤ → ℝ)).PosSemidef) :
    0 ≤ H.det ∧ H.det ≤ ∏ i, H i i := by
  have h1 := det_le_prod_diag hH
  have h0 := hH.det_nonneg
  rw [← Int.cast_det] at h1 h0
  simp only [map_apply] at h1
  exact ⟨by exact_mod_cast h0, by exact_mod_cast h1⟩

omit [DecidableEq n] in
/-- [proved-standard; formal-checked] The real cast of an integer Gram `XᵀX` is positive
semidefinite. -/
theorem gram_map_posSemidef {m : Type*} [Fintype m] (X : Matrix m n ℤ) :
    ((Xᵀ * X).map (Int.cast : ℤ → ℝ)).PosSemidef := by
  have h := posSemidef_conjTranspose_mul_self (X.map (Int.cast : ℤ → ℝ))
  convert h using 1
  ext i j
  simp [mul_apply]

/-- [proved-standard; formal-checked] **Hadamard for an integer Gram:**
`0 ≤ det(XᵀX) ≤ Π_i Σ_k X_ki²`, the product of the columns' squared lengths. -/
theorem gram_det_le_prod_diag {m : Type*} [Fintype m] (X : Matrix m n ℤ) :
    0 ≤ (Xᵀ * X).det ∧ (Xᵀ * X).det ≤ ∏ i, ∑ k, X k i ^ 2 := by
  obtain ⟨h0, h1⟩ := int_det_le_prod_diag (gram_map_posSemidef X)
  refine ⟨h0, h1.trans_eq (Finset.prod_congr rfl fun i _ => ?_)⟩
  simp [mul_apply, sq]

/-- [proved-standard; formal-checked] An integer Gram with nonzero determinant has a positive
definite real cast. -/
theorem gram_map_posDef {m : Type*} [Fintype m] {X : Matrix m n ℤ} (h : (Xᵀ * X).det ≠ 0) :
    ((Xᵀ * X).map (Int.cast : ℤ → ℝ)).PosDef := by
  refine (gram_map_posSemidef X).posDef_iff_det_ne_zero.2 ?_
  rw [← Int.cast_det]
  exact_mod_cast h

/-! ## 2. The solved chart's numerator and denominator -/

omit [DecidableEq n] in
/-- [proved-standard; formal-checked] Reindexing a product over all but `i` by an equivalence with
`Fin (k + 1)`: it is the product over the places that `e i` skips. -/
theorem prod_erase_eq_prod_succAbove [DecidableEq n] {M : Type*} [CommMonoid M] {k : ℕ}
    (e : n ≃ Fin (k + 1)) (g : n → M) (i : n) :
    ∏ b ∈ Finset.univ.erase i, g b = ∏ a : Fin k, g (e.symm ((e i).succAbove a)) := by
  let g' : n → M := fun b => if b = i then 1 else g b
  have h1 : ∏ b ∈ Finset.univ.erase i, g b = ∏ b ∈ Finset.univ.erase i, g' b :=
    Finset.prod_congr rfl fun b hb => by simp [g', Finset.ne_of_mem_erase hb]
  have h2 : ∏ b ∈ Finset.univ.erase i, g' b = ∏ b, g' b := Finset.prod_erase _ (by simp [g'])
  have h3 : ∏ b, g' b = ∏ c, g' (e.symm c) := (Equiv.prod_comp e.symm g').symm
  rw [h1, h2, h3, Fin.prod_univ_succAbove _ (e i)]
  simp only [g', Equiv.symm_apply_apply, if_pos rfl, one_mul]
  refine Finset.prod_congr rfl fun a _ => ?_
  have : e.symm ((e i).succAbove a) ≠ i := by
    intro h
    have h' := congrArg e h
    rw [Equiv.apply_symm_apply] at h'
    exact Fin.succAbove_ne (e i) a h'
  simp [this]

/-- [proved-standard; formal-checked] The adjugate's diagonal entry of a positive semidefinite `H`
is its principal minor off `i`: `0 ≤ adj(H)_ii ≤ Π_(k≠i) H_kk`. -/
theorem adjugate_diag_le_prod_erase {H : Matrix n n ℝ} (hH : H.PosSemidef) (i : n) :
    0 ≤ adjugate H i i ∧ adjugate H i i ≤ ∏ k ∈ Finset.univ.erase i, H k k := by
  have : Nonempty n := ⟨i⟩
  obtain ⟨k, hk⟩ : ∃ k, Fintype.card n = k + 1 :=
    Nat.exists_eq_succ_of_ne_zero Fintype.card_ne_zero
  let e : n ≃ Fin (k + 1) := (Fintype.equivFin n).trans (finCongr hk)
  have hadj : adjugate H i i =
      det (H.submatrix (e.symm ∘ (e i).succAbove) (e.symm ∘ (e i).succAbove)) := by
    have h := adjugate_fin_succ_eq_det_submatrix (reindex e e H) (e i) (e i)
    rw [adjugate_reindex] at h
    simp only [reindex_apply, submatrix_apply, Equiv.symm_apply_apply, submatrix_submatrix] at h
    rw [h]
    have hsign : ((-1 : ℝ)) ^ ((e i : ℕ) + (e i : ℕ)) = 1 := by
      rw [← two_mul, pow_mul]
      norm_num
    rw [hsign, one_mul]
  have hP := hH.submatrix (e.symm ∘ (e i).succAbove)
  rw [hadj, prod_erase_eq_prod_succAbove e]
  exact ⟨hP.det_nonneg, det_le_prod_diag hP⟩

/-- [proved-standard; formal-checked] **The chart's numerator over its denominator:**
`adj A = det A · A⁻¹` when `det A ≠ 0`. -/
theorem adjugate_eq_det_smul_inv {K : Type*} [Field K] {A : Matrix n n K} (h : A.det ≠ 0) :
    adjugate A = A.det • A⁻¹ := by
  rw [inv_def, Ring.inverse_eq_inv', smul_smul, mul_inv_cancel₀ h, one_smul]

/-- [proved-standard; formal-checked] The adjugate of a positive definite matrix is positive
definite. -/
theorem adjugate_posDef {H : Matrix n n ℝ} (hH : H.PosDef) : (adjugate H).PosDef := by
  rw [adjugate_eq_det_smul_inv hH.det_pos.ne']
  exact hH.inv.smul hH.det_pos

/-- [proved-standard; formal-checked] **The cofactor bound:** a positive definite `H` has
`adj(H)_ij² ≤ Π_(k≠i) H_kk · Π_(k≠j) H_kk`. -/
theorem sq_adjugate_le {H : Matrix n n ℝ} (hH : H.PosDef) (i j : n) :
    adjugate H i j ^ 2 ≤
      (∏ k ∈ Finset.univ.erase i, H k k) * ∏ k ∈ Finset.univ.erase j, H k k := by
  have h := sq_entry_le_diag_mul_diag (adjugate_posDef hH).posSemidef i j
  obtain ⟨hi0, hi⟩ := adjugate_diag_le_prod_erase hH.posSemidef i
  obtain ⟨hj0, hj⟩ := adjugate_diag_le_prod_erase hH.posSemidef j
  exact h.trans (mul_le_mul hi hj hj0 (hi0.trans hi))

/-- [proved-standard; formal-checked] The adjugate commutes with the cast of an integer matrix. -/
theorem adjugate_map_intCast {R : Type*} [CommRing R] (H : Matrix n n ℤ) (i j : n) :
    adjugate (H.map (Int.cast : ℤ → R)) i j = ((adjugate H i j : ℤ) : R) := by
  have h := (Int.castRingHom R).map_adjugate H
  rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply] at h
  simp only [Int.coe_castRingHom] at h
  rw [← h, map_apply]

omit [Fintype n] [DecidableEq n] in
/-- [proved-standard; formal-checked] An integer matrix with positive definite real cast has
positive diagonal entries, so each is at least `1`. -/
theorem int_diag_pos {H : Matrix n n ℤ} (hH : (H.map (Int.cast : ℤ → ℝ)).PosDef) (k : n) :
    0 < H k k := by
  have := hH.diag_pos (i := k)
  simp only [map_apply] at this
  exact_mod_cast this

/-- [proved-standard; formal-checked] An integer matrix with positive definite real cast has
`0 < det H ≤ Π_k H_kk`. -/
theorem int_det_pos_le {H : Matrix n n ℤ} (hH : (H.map (Int.cast : ℤ → ℝ)).PosDef) :
    0 < H.det ∧ H.det ≤ ∏ k, H k k := by
  refine ⟨?_, (int_det_le_prod_diag hH.posSemidef).2⟩
  have := hH.det_pos
  rw [← Int.cast_det] at this
  exact_mod_cast this

omit [DecidableEq n] in
/-- [proved-standard; formal-checked] With positive integer diagonal entries, the product off `i`
is at most the whole product. -/
theorem prod_erase_le_prod [DecidableEq n] {H : Matrix n n ℤ} (hpos : ∀ k, 0 < H k k) (i : n) :
    ∏ k ∈ Finset.univ.erase i, H k k ≤ ∏ k, H k k := by
  rw [← Finset.mul_prod_erase Finset.univ (fun k => H k k) (Finset.mem_univ i)]
  have h0 : 0 ≤ ∏ k ∈ Finset.univ.erase i, H k k := Finset.prod_nonneg fun k _ => (hpos k).le
  have h1 : 1 ≤ H i i := hpos i
  nlinarith

/-- [proved-standard; formal-checked] **The integer cofactor bound:** an integer matrix with
positive definite real cast has `|adj(H)_ij| ≤ Π_k H_kk`. -/
theorem int_abs_adjugate_le {H : Matrix n n ℤ} (hH : (H.map (Int.cast : ℤ → ℝ)).PosDef)
    (i j : n) : |adjugate H i j| ≤ ∏ k, H k k := by
  have h := sq_adjugate_le hH i j
  simp only [adjugate_map_intCast, map_apply] at h
  have hZ : adjugate H i j ^ 2 ≤
      (∏ k ∈ Finset.univ.erase i, H k k) * ∏ k ∈ Finset.univ.erase j, H k k := by
    exact_mod_cast h
  have hpos := int_diag_pos hH
  have hi := prod_erase_le_prod hpos i
  have hj := prod_erase_le_prod hpos j
  have hi0 : 0 ≤ ∏ k ∈ Finset.univ.erase i, H k k := Finset.prod_nonneg fun k _ => (hpos k).le
  have hj0 : 0 ≤ ∏ k ∈ Finset.univ.erase j, H k k := Finset.prod_nonneg fun k _ => (hpos k).le
  have hP0 : 0 ≤ ∏ k, H k k := hi0.trans hi
  have hsq : |adjugate H i j| ^ 2 ≤ (∏ k, H k k) ^ 2 := by
    rw [sq_abs, sq (∏ k, H k k)]
    exact hZ.trans (mul_le_mul hi hj hj0 hP0)
  exact (sq_le_sq₀ (abs_nonneg _) hP0).1 hsq

/-- [proved-standard; formal-checked] **The solved chart over `ℚ`:** an integer `H` has
`H⁻¹ = (det H)⁻¹ · adj H`, one common denominator over integer numerators. -/
theorem rat_inv_eq (H : Matrix n n ℤ) :
    (H.map (Int.cast : ℤ → ℚ))⁻¹ = (H.det : ℚ)⁻¹ • (adjugate H).map (Int.cast : ℤ → ℚ) := by
  ext i j
  rw [inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, Matrix.smul_apply, adjugate_map_intCast,
    ← Int.cast_det, map_apply]

/-- [proved-standard; formal-checked] Each entry of the solved chart is `adj(H)_ij / det H`. -/
theorem rat_inv_apply (H : Matrix n n ℤ) (i j : n) :
    (H.map (Int.cast : ℤ → ℚ))⁻¹ i j = ((adjugate H i j : ℤ) : ℚ) / (H.det : ℚ) := by
  rw [rat_inv_eq, Matrix.smul_apply, map_apply, smul_eq_mul, div_eq_inv_mul]

/-! ## 3. The bits -/

/-- [proved-standard; formal-checked] Reducing `a / d` (`d > 0`) only shrinks: the reduced
numerator is at most `|a|` and the reduced denominator at most `d`. -/
theorem rat_div_num_den_le {a d : ℤ} (hd : 0 < d) {A B : ℕ} (ha : a.natAbs ≤ A)
    (hdB : d.natAbs ≤ B) : ((a : ℚ) / d).num.natAbs ≤ A ∧ ((a : ℚ) / d).den ≤ B := by
  rw [← Rat.divInt_eq_div]
  constructor
  · by_cases ha0 : a = 0
    · subst ha0
      simp
    · exact (Int.natAbs_le_of_dvd_ne_zero (Rat.num_dvd a hd.ne') ha0).trans ha
  · have h := Int.le_of_dvd hd (Rat.den_dvd a d)
    have hn : (d.natAbs : ℤ) = d := Int.natAbs_of_nonneg hd.le
    omega

/-- [proved-standard; formal-checked] `|a| ≤ P` gives `a.natAbs ≤ P.natAbs`. -/
theorem natAbs_le_of_abs_le {a P : ℤ} (h : |a| ≤ P) : a.natAbs ≤ P.natAbs := by
  have h1 : (a.natAbs : ℤ) = |a| := Int.natCast_natAbs a
  have h2 : (P.natAbs : ℤ) = P := Int.natAbs_of_nonneg ((abs_nonneg a).trans h)
  omega

/-- [proved-derived; formal-checked] **The solved chart's magnitudes:** for an integer positive
definite Gram, every reduced entry of `H⁻¹` has numerator and denominator at most `Π_k H_kk`. -/
theorem solved_chart_num_den_le {H : Matrix n n ℤ} (hH : (H.map (Int.cast : ℤ → ℝ)).PosDef)
    (i j : n) :
    ((H.map (Int.cast : ℤ → ℚ))⁻¹ i j).num.natAbs ≤ (∏ k, H k k).natAbs ∧
      ((H.map (Int.cast : ℤ → ℚ))⁻¹ i j).den ≤ (∏ k, H k k).natAbs := by
  obtain ⟨hd0, hdP⟩ := int_det_pos_le hH
  rw [rat_inv_apply]
  exact rat_div_num_den_le hd0 (natAbs_le_of_abs_le (int_abs_adjugate_le hH i j))
    (natAbs_le_of_abs_le (by rw [abs_of_pos hd0]; exact hdP))

/-- [proved-standard; formal-checked] A product takes at most the bits of its factors. -/
theorem size_mul_le (a b : ℕ) : Nat.size (a * b) ≤ Nat.size a + Nat.size b := by
  rw [Nat.size_le, pow_add]
  exact Nat.mul_lt_mul'' (Nat.lt_size_self a) (Nat.lt_size_self b)

/-- [proved-standard; formal-checked] A nonempty product takes at most the sum of its factors'
bits. -/
theorem size_prod_le {ι : Type*} {s : Finset ι} (hs : s.Nonempty) (f : ι → ℕ) :
    Nat.size (∏ i ∈ s, f i) ≤ ∑ i ∈ s, Nat.size (f i) := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a => simp
  | cons a s ha hs ih =>
    rw [Finset.prod_cons, Finset.sum_cons]
    exact (size_mul_le _ _).trans (by omega)

/-- [proved-standard; formal-checked] A natural number takes at most `log₂ m + 1` bits. -/
theorem size_le_logb_add_one (m : ℕ) : (Nat.size m : ℝ) ≤ Real.logb 2 m + 1 := by
  have h1 : Nat.size m ≤ Nat.log 2 m + 1 :=
    Nat.size_le.2 (Nat.lt_pow_succ_log_self (by norm_num) m)
  have h2 := Real.natLog_le_logb m 2
  have h1' : (Nat.size m : ℝ) ≤ (Nat.log 2 m : ℝ) + 1 := by exact_mod_cast h1
  simp only [Nat.cast_ofNat] at h2
  linarith

omit [DecidableEq n] in
/-- [proved-derived; formal-checked] The Hadamard product takes at most `Σ_k log₂ H_kk + 1`
bits. -/
theorem size_diag_prod_le_logb {H : Matrix n n ℤ} (hpos : ∀ k, 0 < H k k) :
    (Nat.size (∏ k, H k k).natAbs : ℝ) ≤ ∑ k, Real.logb 2 (H k k) + 1 := by
  have h := size_le_logb_add_one (∏ k, H k k).natAbs
  have hP : (((∏ k, H k k).natAbs : ℕ) : ℝ) = ∏ k, (H k k : ℝ) := by
    rw [Nat.cast_natAbs, abs_of_pos (Finset.prod_pos fun k _ => hpos k)]
    push_cast
    rfl
  rw [hP, Real.logb_prod _ _ fun k _ => by exact_mod_cast (hpos k).ne'] at h
  exact h

omit [DecidableEq n] in
/-- [proved-derived; formal-checked] The Hadamard product takes at most the sum of the diagonal
entries' bits. -/
theorem size_diag_prod_le_sum_size [Nonempty n] (H : Matrix n n ℤ) :
    Nat.size (∏ k, H k k).natAbs ≤ ∑ k, Nat.size (H k k).natAbs := by
  rw [show (∏ k, H k k).natAbs = ∏ k, (H k k).natAbs from map_prod Int.natAbsHom _ _]
  exact size_prod_le Finset.univ_nonempty _

/-- [proved-derived; formal-checked] **The solved chart's bits:** for an integer positive definite
Gram, each reduced entry of `H⁻¹` has numerator and denominator of at most `Σ_k log₂ H_kk + 1`
bits. -/
theorem solved_chart_bits {H : Matrix n n ℤ} (hH : (H.map (Int.cast : ℤ → ℝ)).PosDef) (i j : n) :
    (Nat.size ((H.map (Int.cast : ℤ → ℚ))⁻¹ i j).num.natAbs : ℝ) ≤
        ∑ k, Real.logb 2 (H k k) + 1 ∧
      (Nat.size ((H.map (Int.cast : ℤ → ℚ))⁻¹ i j).den : ℝ) ≤ ∑ k, Real.logb 2 (H k k) + 1 := by
  obtain ⟨hnum, hden⟩ := solved_chart_num_den_le hH i j
  have hlog := size_diag_prod_le_logb (int_diag_pos hH)
  constructor
  · exact le_trans (by exact_mod_cast Nat.size_le_size hnum) hlog
  · exact le_trans (by exact_mod_cast Nat.size_le_size hden) hlog

/-- [proved-derived; formal-checked] **The solved chart's bits, the Rust count:** numerator and
denominator of each reduced entry of `H⁻¹` take together at most `2 Σ_k size(H_kk)` bits. -/
theorem solved_chart_size_le [Nonempty n] {H : Matrix n n ℤ}
    (hH : (H.map (Int.cast : ℤ → ℝ)).PosDef) (i j : n) :
    Nat.size ((H.map (Int.cast : ℤ → ℚ))⁻¹ i j).num.natAbs +
        Nat.size ((H.map (Int.cast : ℤ → ℚ))⁻¹ i j).den ≤
      2 * ∑ k, Nat.size (H k k).natAbs := by
  obtain ⟨hnum, hden⟩ := solved_chart_num_den_le hH i j
  have hs := size_diag_prod_le_sum_size H
  have h1 := Nat.size_le_size hnum
  have h2 := Nat.size_le_size hden
  omega

/-! ## 4. On the carried lattice -/

/-- [proved-derived; formal-checked] The carried Gram `u_L · N` on the lattice of
`HNN/LatticeDeposit.unit` has the chart `2^L N⁻¹`. -/
theorem lattice_inv_eq {N : Matrix n n ℤ} (hN : N.det ≠ 0) (L : ℕ) :
    (unit L • N.map (Int.cast : ℤ → ℚ))⁻¹ = (2 : ℚ) ^ L • (N.map (Int.cast : ℤ → ℚ))⁻¹ := by
  apply inv_eq_right_inv
  have hu : IsUnit (N.map (Int.cast : ℤ → ℚ)).det := by
    rw [← Int.cast_det]
    exact isUnit_iff_ne_zero.2 (by exact_mod_cast hN)
  rw [Matrix.smul_mul, Matrix.mul_smul, mul_nonsing_inv _ hu, smul_smul, unit,
    inv_mul_cancel₀ (by positivity), one_smul]

/-- [proved-derived; formal-checked] Each entry of the carried Gram's chart is
`2^L adj(N)_ij / det N`. -/
theorem lattice_inv_apply {N : Matrix n n ℤ} (hN : N.det ≠ 0) (L : ℕ) (i j : n) :
    (unit L • N.map (Int.cast : ℤ → ℚ))⁻¹ i j =
      ((2 ^ L * adjugate N i j : ℤ) : ℚ) / (N.det : ℚ) := by
  rw [lattice_inv_eq hN, Matrix.smul_apply, rat_inv_apply, smul_eq_mul]
  push_cast
  ring

/-- [proved-derived; formal-checked] **The carried chart's bits:** each reduced entry of
`(u_L · N)⁻¹` has a numerator of at most `L + size(Π_k N_kk)` bits and a denominator of at most
`size(Π_k N_kk)` bits. -/
theorem lattice_solved_chart_bits {N : Matrix n n ℤ} (hN : (N.map (Int.cast : ℤ → ℝ)).PosDef)
    (L : ℕ) (i j : n) :
    Nat.size ((unit L • N.map (Int.cast : ℤ → ℚ))⁻¹ i j).num.natAbs ≤
        L + Nat.size (∏ k, N k k).natAbs ∧
      Nat.size ((unit L • N.map (Int.cast : ℤ → ℚ))⁻¹ i j).den ≤ Nat.size (∏ k, N k k).natAbs := by
  obtain ⟨hd0, hdP⟩ := int_det_pos_le hN
  rw [lattice_inv_apply hd0.ne' L]
  have ha := natAbs_le_of_abs_le (int_abs_adjugate_le hN i j)
  have hd := natAbs_le_of_abs_le (by rw [abs_of_pos hd0]; exact hdP : |N.det| ≤ ∏ k, N k k)
  have ha' : (2 ^ L * adjugate N i j).natAbs ≤ 2 ^ L * (∏ k, N k k).natAbs := by
    rw [Int.natAbs_mul, Int.natAbs_pow]
    exact Nat.mul_le_mul_left _ ha
  obtain ⟨hnum, hden⟩ := rat_div_num_den_le hd0 ha' hd
  refine ⟨(Nat.size_le_size hnum).trans ?_, Nat.size_le_size hden⟩
  rw [Nat.size_le, pow_add]
  exact Nat.mul_lt_mul_of_pos_left (Nat.lt_size_self _) (by positivity)

/-! ## 4b. The carried Gram's margin gives the positive definite cast -/

omit [DecidableEq n] in
/-- [proved-standard; formal-checked] **A rational margin is a real one:** a symmetric rational `H`
with `c |v|² ≤ vᵀHv` on every rational `v` (`c > 0`) has a positive definite real cast. -/
theorem posDef_of_rat_margin {H : Matrix n n ℚ} (hsym : Hᵀ = H) {c : ℚ} (hc : 0 < c)
    (hm : ∀ v : n → ℚ, c * ∑ i, v i ^ 2 ≤ ∑ i, ∑ j, v i * H i j * v j) :
    (H.map ((↑) : ℚ → ℝ)).PosDef := by
  have hmR : ∀ v : n → ℝ,
      (c : ℝ) * ∑ i, v i ^ 2 ≤ ∑ i, ∑ j, v i * (H i j : ℝ) * v j := by
    intro v
    have hd : DenseRange (Pi.map fun (_ : n) (r : ℚ) => (r : ℝ)) :=
      DenseRange.piMap fun _ => Rat.denseRange_cast
    refine hd.induction_on
      (p := fun v : n → ℝ => (c : ℝ) * ∑ i, v i ^ 2 ≤ ∑ i, ∑ j, v i * (H i j : ℝ) * v j) v ?_ ?_
    · exact isClosed_le (by fun_prop) (by fun_prop)
    · intro w
      simp only [Pi.map_apply]
      exact_mod_cast hm w
  refine PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
  · rw [IsHermitian, conjTranspose_eq_transpose_of_trivial]
    ext i j
    have h := congrFun (congrFun hsym i) j
    rw [transpose_apply] at h
    simp only [transpose_apply, map_apply, h]
  · have hq : star x ⬝ᵥ (H.map ((↑) : ℚ → ℝ) *ᵥ x) = ∑ i, ∑ j, x i * (H i j : ℝ) * x j := by
      simp only [star_trivial, dotProduct, mulVec, map_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hx
    have hpos : 0 < ∑ i, x i ^ 2 :=
      Finset.sum_pos' (fun j _ => sq_nonneg (x j))
        ⟨i, Finset.mem_univ i, lt_of_le_of_ne (sq_nonneg _) (pow_ne_zero 2 hi).symm⟩
    have hcR : (0 : ℝ) < c := by exact_mod_cast hc
    rw [hq]
    exact lt_of_lt_of_le (mul_pos hcR hpos) (hmR x)

/-- [proved-standard; formal-checked] The lattice rule's margin `1 − 1/(2 L_R)` is positive for
`L_R ≥ 1`. -/
theorem one_sub_inv_two_pos {LR : ℕ} (hLR : 0 < LR) : (0 : ℚ) < 1 - 1 / (2 * LR) := by
  have h1 : (1 : ℚ) ≤ LR := by exact_mod_cast hLR
  have h2 : 1 / (2 * (LR : ℚ)) < 1 := (div_lt_one (by positivity)).2 (by linarith)
  linarith

omit [DecidableEq n] in
/-- [proved-derived; formal-checked] **The carried Gram's cast is positive definite:** a symmetric
carried Gram under `carried_gram_posDef_rule`'s hypotheses has a positive definite real cast. -/
theorem carried_gram_map_posDef {L : ℕ} {H Hx : Matrix n n ℚ} (hsym : Hᵀ = H)
    (hclose : ∀ i j, |H i j - Hx i j| ≤ unit L)
    (hexact : ∀ v : n → ℚ, ∑ i, v i ^ 2 ≤ ∑ i, ∑ j, v i * Hx i j * v j) {LR : ℕ}
    (hLR : 0 < LR) (hL : 2 * LR * Fintype.card n ≤ 2 ^ L) :
    (H.map ((↑) : ℚ → ℝ)).PosDef :=
  posDef_of_rat_margin hsym (one_sub_inv_two_pos hLR)
    (carried_gram_posDef_rule H Hx hclose hexact hLR hL)

omit [DecidableEq n] in
/-- [proved-derived; formal-checked] **The carried coordinates' cast is positive definite:** when
the carried Gram is `u_L · N` with `N` symmetric integer coordinates, under the lattice rule the
real cast of `N` is positive definite. -/
theorem carried_lattice_map_posDef {L : ℕ} {N : Matrix n n ℤ} {Hx : Matrix n n ℚ} (hsym : Nᵀ = N)
    (hclose : ∀ i j, |(unit L • N.map (Int.cast : ℤ → ℚ)) i j - Hx i j| ≤ unit L)
    (hexact : ∀ v : n → ℚ, ∑ i, v i ^ 2 ≤ ∑ i, ∑ j, v i * Hx i j * v j) {LR : ℕ}
    (hLR : 0 < LR) (hL : 2 * LR * Fintype.card n ≤ 2 ^ L) :
    (N.map (Int.cast : ℤ → ℝ)).PosDef := by
  have hm := carried_gram_posDef_rule _ Hx hclose hexact hLR hL
  have hN : ((N.map (Int.cast : ℤ → ℚ)).map ((↑) : ℚ → ℝ)).PosDef := by
    refine posDef_of_rat_margin (c := (1 - 1 / (2 * LR)) * 2 ^ L) ?_
      (mul_pos (one_sub_inv_two_pos hLR) (by positivity)) fun v => ?_
    · ext i j
      have h := congrFun (congrFun hsym i) j
      rw [transpose_apply] at h
      simp only [transpose_apply, map_apply, h]
    · have h := hm v
      have heq : ∑ i, ∑ j, v i * (unit L • N.map (Int.cast : ℤ → ℚ)) i j * v j =
          unit L * ∑ i, ∑ j, v i * (N.map (Int.cast : ℤ → ℚ)) i j * v j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Matrix.smul_apply, smul_eq_mul]
        ring
      rw [heq, unit] at h
      have h2 : (0 : ℚ) < 2 ^ L := by positivity
      calc (1 - 1 / (2 * (LR : ℚ))) * 2 ^ L * ∑ i, v i ^ 2
          = 2 ^ L * ((1 - 1 / (2 * (LR : ℚ))) * ∑ i, v i ^ 2) := by ring
        _ ≤ 2 ^ L * (((2 : ℚ) ^ L)⁻¹ * ∑ i, ∑ j, v i * (N.map (Int.cast : ℤ → ℚ)) i j * v j) :=
            mul_le_mul_of_nonneg_left h h2.le
        _ = ∑ i, ∑ j, v i * (N.map (Int.cast : ℤ → ℚ)) i j * v j := by field_simp
  rw [Matrix.map_map] at hN
  convert hN using 2
  funext x
  simp

/-- [proved-derived; formal-checked] **The carried chart's bits under the lattice rule alone:**
`lattice_solved_chart_bits` for the carried Gram `u_L · N`, with no positivity hypothesis beyond
the rule's own and the coordinates' symmetry. -/
theorem carried_lattice_solved_chart_bits {L : ℕ} {N : Matrix n n ℤ} {Hx : Matrix n n ℚ}
    (hsym : Nᵀ = N)
    (hclose : ∀ i j, |(unit L • N.map (Int.cast : ℤ → ℚ)) i j - Hx i j| ≤ unit L)
    (hexact : ∀ v : n → ℚ, ∑ i, v i ^ 2 ≤ ∑ i, ∑ j, v i * Hx i j * v j) {LR : ℕ}
    (hLR : 0 < LR) (hL : 2 * LR * Fintype.card n ≤ 2 ^ L) (i j : n) :
    Nat.size ((unit L • N.map (Int.cast : ℤ → ℚ))⁻¹ i j).num.natAbs ≤
        L + Nat.size (∏ k, N k k).natAbs ∧
      Nat.size ((unit L • N.map (Int.cast : ℤ → ℚ))⁻¹ i j).den ≤ Nat.size (∏ k, N k k).natAbs :=
  lattice_solved_chart_bits (carried_lattice_map_posDef hsym hclose hexact hLR hL) L i j

/-! ## 5. Prime images verified over `ℚ` -/

/-- [proved-standard; formal-checked] Two integers of magnitude at most `B` that agree modulo
`m > 2B` are equal. -/
theorem eq_of_modEq_of_abs_le {x y B m : ℤ} (hx : |x| ≤ B) (hy : |y| ≤ B) (hm : 2 * B < m)
    (h : x ≡ y [ZMOD m]) : x = y := by
  have hd : m ∣ y - x := Int.ModEq.dvd h
  have hlt : |y - x| < m := by
    rw [abs_lt]
    constructor <;> linarith [(abs_le.1 hx).1, (abs_le.1 hx).2, (abs_le.1 hy).1, (abs_le.1 hy).2]
  linarith [Int.eq_zero_of_abs_lt_dvd hd hlt]

/-- [proved-standard; formal-checked] **The symmetric representative reads the integer:** for
`|x| ≤ B` and `2B < m`, the residue of `x` modulo `m` read at its least absolute value is `x`. -/
theorem valMinAbs_intCast_eq {m : ℕ} [NeZero m] {x B : ℤ} (hx : |x| ≤ B) (hm : 2 * B < m) :
    (x : ZMod m).valMinAbs = x := by
  rw [ZMod.valMinAbs_spec]
  refine ⟨rfl, ?_, ?_⟩
  · linarith [(abs_le.1 hx).1]
  · linarith [(abs_le.1 hx).2]

open Function in
/-- [proved-standard; formal-checked] **The Chinese remainder theorem, read as agreement:**
agreement modulo pairwise coprime moduli is agreement modulo their product. -/
theorem modEq_prod_of_modEq {ι : Type*} {s : Finset ι} {p : ι → ℤ}
    (hp : (s : Set ι).Pairwise (IsCoprime on p)) {x y : ℤ} (h : ∀ i ∈ s, x ≡ y [ZMOD p i]) :
    x ≡ y [ZMOD ∏ i ∈ s, p i] :=
  Int.modEq_iff_dvd.2 (Finset.prod_dvd_of_coprime hp fun i hi => Int.modEq_iff_dvd.1 (h i hi))

open Function in
/-- [proved-standard; formal-checked] Distinct primes are pairwise coprime in `ℤ`. -/
theorem primes_pairwise_coprime {ι : Type*} {s : Finset ι} {p : ι → ℕ}
    (hp : ∀ i ∈ s, (p i).Prime) (hinj : Set.InjOn p s) :
    (s : Set ι).Pairwise (IsCoprime on fun i => (p i : ℤ)) := by
  intro i hi j hj hij
  simp only [Function.onFun]
  rw [Nat.isCoprime_iff_coprime]
  exact (Nat.coprime_primes (hp i hi) (hp j hj)).2 fun h => hij (hinj hi hj h)

/-- [proved-standard; formal-checked] **Prime images fix a bounded integer:** two integers of
magnitude at most `B` that agree modulo distinct primes whose product passes `2B` are equal. -/
theorem eq_of_prime_images {ι : Type*} {s : Finset ι} {p : ι → ℕ} (hp : ∀ i ∈ s, (p i).Prime)
    (hinj : Set.InjOn p s) {x y B : ℤ} (hx : |x| ≤ B) (hy : |y| ≤ B)
    (hB : 2 * B < ∏ i ∈ s, (p i : ℤ)) (h : ∀ i ∈ s, x ≡ y [ZMOD p i]) : x = y :=
  eq_of_modEq_of_abs_le hx hy hB (modEq_prod_of_modEq (primes_pairwise_coprime hp hinj) h)

/-- [proved-standard; formal-checked] **The cheap certificate, verified over `ℚ`:** `H Y = d · 1`
over `ℤ` with `d ≠ 0` gives `H⁻¹ = d⁻¹ Y` over `ℚ`. -/
theorem inv_eq_of_mul_eq_smul_one {H Y : Matrix n n ℤ} {d : ℤ} (hd : d ≠ 0)
    (h : H * Y = d • (1 : Matrix n n ℤ)) :
    (H.map (Int.cast : ℤ → ℚ))⁻¹ = (d : ℚ)⁻¹ • Y.map (Int.cast : ℤ → ℚ) := by
  apply inv_eq_right_inv
  have hm : H.map (Int.cast : ℤ → ℚ) * Y.map (Int.cast : ℤ → ℚ) =
      (d : ℚ) • (1 : Matrix n n ℚ) := by
    ext a b
    have := congrFun (congrFun h a) b
    simp only [mul_apply, map_apply, Matrix.smul_apply, smul_eq_mul, one_apply] at this ⊢
    by_cases hab : a = b
    · simp only [hab, if_true, mul_one] at this ⊢
      exact_mod_cast this
    · simp only [hab, if_false, mul_zero] at this ⊢
      exact_mod_cast this
  rw [mul_smul_comm, hm, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hd), one_smul]

/-- [proved-derived; formal-checked] **A multimodular solve is certified by the Hadamard bound:**
candidates of magnitude at most `Π_k H_kk` that agree with `det H` and `adj H` modulo distinct
primes whose product passes `2 Π_k H_kk` are `det H` and `adj H`, and they give `H⁻¹` over `ℚ`. -/
theorem solved_chart_of_prime_images {H : Matrix n n ℤ} (hH : (H.map (Int.cast : ℤ → ℝ)).PosDef)
    {ι : Type*} {s : Finset ι} {p : ι → ℕ} (hp : ∀ i ∈ s, (p i).Prime) (hinj : Set.InjOn p s)
    (hB : 2 * ∏ k, H k k < ∏ i ∈ s, (p i : ℤ)) {d : ℤ} {Y : Matrix n n ℤ}
    (hd : |d| ≤ ∏ k, H k k) (hY : ∀ a b, |Y a b| ≤ ∏ k, H k k)
    (hdp : ∀ i ∈ s, d ≡ H.det [ZMOD p i])
    (hYp : ∀ i ∈ s, ∀ a b, Y a b ≡ adjugate H a b [ZMOD p i]) :
    d = H.det ∧ Y = adjugate H ∧
      (H.map (Int.cast : ℤ → ℚ))⁻¹ = (d : ℚ)⁻¹ • Y.map (Int.cast : ℤ → ℚ) := by
  obtain ⟨hd0, hdP⟩ := int_det_pos_le hH
  have hdet : d = H.det :=
    eq_of_prime_images hp hinj hd (by rw [abs_of_pos hd0]; exact hdP) hB hdp
  have hadj : Y = adjugate H := by
    ext a b
    exact eq_of_prime_images hp hinj (hY a b) (int_abs_adjugate_le hH a b) hB
      fun i hi => hYp i hi a b
  refine ⟨hdet, hadj, ?_⟩
  subst hdet hadj
  exact inv_eq_of_mul_eq_smul_one hd0.ne' (mul_adjugate H)

/-! ## 6. A factored `H′` -/

omit [Fintype n] [DecidableEq n] in
/-- [proved-standard; formal-checked] **The factored determinant:** `H = L D Lᵀ` with `L` unit
lower triangular has `det H = Π_i D_i`. -/
theorem det_ldl {K : Type*} [CommRing K] {m : Type*} [Fintype m] [DecidableEq m] [LinearOrder m]
    {L : Matrix m m K} (hL : L.IsLowerTriangular) (h1 : ∀ i, L i i = 1) (D : m → K) :
    (L * diagonal D * Lᵀ).det = ∏ i, D i := by
  rw [det_mul, det_mul, det_transpose, det_of_isLowerTriangular L hL, det_diagonal]
  simp [h1]

/-- [proved-standard; formal-checked] The leading `k × k` block of `L D Lᵀ`, `L` lower
triangular, is `L_k D_k L_kᵀ`. -/
theorem ldl_leading_block {K : Type*} [CommRing K] {N k : ℕ} (hk : k ≤ N)
    {L : Matrix (Fin N) (Fin N) K} (hL : L.IsLowerTriangular) (D : Fin N → K) :
    (L * diagonal D * Lᵀ).submatrix (Fin.castLE hk) (Fin.castLE hk) =
      L.submatrix (Fin.castLE hk) (Fin.castLE hk) * diagonal (D ∘ Fin.castLE hk) *
        (L.submatrix (Fin.castLE hk) (Fin.castLE hk))ᵀ := by
  ext a b
  rw [submatrix_apply, mul_apply, mul_apply]
  simp only [mul_diagonal, transpose_apply, Function.comp_apply, submatrix_apply]
  have hz : ∀ c : Fin N, c ∉ Finset.univ.image (Fin.castLE hk) → L (Fin.castLE hk a) c = 0 := by
    intro c hc
    apply hL
    rw [OrderDual.toDual_lt_toDual, Fin.lt_def, Fin.val_castLE]
    by_contra hcon
    apply hc
    exact Finset.mem_image.2 ⟨⟨c, by omega⟩, Finset.mem_univ _, Fin.ext rfl⟩
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image (Fin.castLE hk)))
    (fun c _ hc => by rw [hz c hc]; ring),
    Finset.sum_image (fun x _ y _ h => Fin.castLE_injective hk h)]

/-- [proved-standard; formal-checked] **The leading minors of a factored `H′`:**
`Δ_k = Π_(a<k) D_a`. -/
theorem ldl_leading_minor {K : Type*} [CommRing K] {N k : ℕ} (hk : k ≤ N)
    {L : Matrix (Fin N) (Fin N) K} (hL : L.IsLowerTriangular) (h1 : ∀ i, L i i = 1)
    (D : Fin N → K) :
    ((L * diagonal D * Lᵀ).submatrix (Fin.castLE hk) (Fin.castLE hk)).det =
      ∏ a : Fin k, D (Fin.castLE hk a) := by
  have hsub : (L.submatrix (Fin.castLE hk) (Fin.castLE hk)).IsLowerTriangular := by
    intro i j hij
    apply hL
    rw [OrderDual.toDual_lt_toDual] at hij ⊢
    rw [Fin.lt_def, Fin.val_castLE, Fin.val_castLE]
    exact hij
  rw [ldl_leading_block hk hL D, det_ldl hsub (fun i => h1 _)]
  rfl

/-- [proved-standard; formal-checked] **Each pivot is a ratio of leading minors:**
`Δ_(k+1) = Δ_k D_k`. -/
theorem ldl_pivot {K : Type*} [CommRing K] {N k : ℕ} (hk : k + 1 ≤ N)
    {L : Matrix (Fin N) (Fin N) K} (hL : L.IsLowerTriangular) (h1 : ∀ i, L i i = 1)
    (D : Fin N → K) :
    ((L * diagonal D * Lᵀ).submatrix (Fin.castLE hk) (Fin.castLE hk)).det =
      ((L * diagonal D * Lᵀ).submatrix (Fin.castLE (Nat.le_of_succ_le hk))
        (Fin.castLE (Nat.le_of_succ_le hk))).det * D ⟨k, hk⟩ := by
  rw [ldl_leading_minor _ hL h1, ldl_leading_minor _ hL h1, Fin.prod_univ_castSucc]
  rfl

/-- [proved-derived; formal-checked] The leading minors of an integer positive definite `H` are
positive and bounded by Hadamard on their blocks: `0 < Δ_k ≤ Π_(a<k) H_aa`. -/
theorem int_leading_minor_pos_le {N : ℕ} {H : Matrix (Fin N) (Fin N) ℤ}
    (hH : (H.map (Int.cast : ℤ → ℝ)).PosDef) {k : ℕ} (hk : k ≤ N) :
    0 < (H.submatrix (Fin.castLE hk) (Fin.castLE hk)).det ∧
      (H.submatrix (Fin.castLE hk) (Fin.castLE hk)).det ≤
        ∏ a : Fin k, H (Fin.castLE hk a) (Fin.castLE hk a) :=
  int_det_pos_le (hH.submatrix (Fin.castLE_injective hk))

/-- [proved-derived; formal-checked] **The factored chart's pivots:** for an integer positive
definite `H = L D Lᵀ` over `ℚ`, `D_k = Δ_(k+1) / Δ_k` with integer leading minors `Δ`. -/
theorem ldl_pivot_ratio {N k : ℕ} (hk : k + 1 ≤ N) {H : Matrix (Fin N) (Fin N) ℤ}
    (hH : (H.map (Int.cast : ℤ → ℝ)).PosDef) {L : Matrix (Fin N) (Fin N) ℚ}
    (hL : L.IsLowerTriangular) (h1 : ∀ i, L i i = 1) {D : Fin N → ℚ}
    (hLDL : H.map (Int.cast : ℤ → ℚ) = L * diagonal D * Lᵀ) :
    D ⟨k, hk⟩ = ((H.submatrix (Fin.castLE hk) (Fin.castLE hk)).det : ℚ) /
      ((H.submatrix (Fin.castLE (Nat.le_of_succ_le hk))
        (Fin.castLE (Nat.le_of_succ_le hk))).det : ℚ) := by
  have hp := ldl_pivot hk hL h1 D
  rw [← hLDL] at hp
  simp only [submatrix_map, ← Int.cast_det] at hp
  have hpos := (int_leading_minor_pos_le hH (Nat.le_of_succ_le hk)).1
  rw [hp, mul_div_cancel_left₀]
  exact_mod_cast hpos.ne'

/-- [proved-derived; formal-checked] **The factored chart's bits:** each pivot `D_k` of an integer
positive definite `H = L D Lᵀ`, reduced, has numerator at most `Π_(a≤k) H_aa` and denominator at
most `Π_(a<k) H_aa`. -/
theorem ldl_pivot_num_den_le {N k : ℕ} (hk : k + 1 ≤ N) {H : Matrix (Fin N) (Fin N) ℤ}
    (hH : (H.map (Int.cast : ℤ → ℝ)).PosDef) {L : Matrix (Fin N) (Fin N) ℚ}
    (hL : L.IsLowerTriangular) (h1 : ∀ i, L i i = 1) {D : Fin N → ℚ}
    (hLDL : H.map (Int.cast : ℤ → ℚ) = L * diagonal D * Lᵀ) :
    (D ⟨k, hk⟩).num.natAbs ≤ (∏ a : Fin (k + 1), H (Fin.castLE hk a) (Fin.castLE hk a)).natAbs ∧
      (D ⟨k, hk⟩).den ≤
        (∏ a : Fin k, H (Fin.castLE (Nat.le_of_succ_le hk) a)
          (Fin.castLE (Nat.le_of_succ_le hk) a)).natAbs := by
  obtain ⟨hn0, hnP⟩ := int_leading_minor_pos_le hH hk
  obtain ⟨hd0, hdP⟩ := int_leading_minor_pos_le hH (Nat.le_of_succ_le hk)
  rw [ldl_pivot_ratio hk hH hL h1 hLDL]
  exact rat_div_num_den_le hd0 (natAbs_le_of_abs_le (by rw [abs_of_pos hn0]; exact hnP))
    (natAbs_le_of_abs_le (by rw [abs_of_pos hd0]; exact hdP))

end Holonics.HNN.SolvedChartBits
