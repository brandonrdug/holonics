import Mathlib
import HolonicsResearch.Landmarks.IharaBass

/-!
# Ihara–Bass with a connection: holonomy enters the determinant, a gauge leaves it, and a double cover factors

`Landmarks/IharaBass` proves the determinant identity for the dart operator of a finite complex of
contacts.  This owner carries an abelian connection through the same block argument: every dart
`d` holds a transport `g d` in a commutative ring, and the reversed dart holds its inverse,
`g d * g d.swap = 1`.  The model is the plain file's (cells `V`, contacts `E`, ends `a b : E → V`,
darts `E ⊕ E`, reversal `Sum.swap`; loops and parallel contacts allowed), and nothing is divided.

* [definition] `startMatrixC` `S_g` (`S_g v d = g d` when `d` leaves `v`), `startMatrixC'` `S'_g`
  (`g d.swap` in its place), `reversalC` `J_g` (`J_g d f = g f` when `f` is `d` reversed),
  `hashimotoC` `B_g` (`B_g d f = g f` when `f` leaves the cell `d` enters and is not `d`
  reversed) and `adjacencyC` `A_g = S_g Tᵀ` (`A_g v w` sums the transports of the darts from `v`
  to `w`).  The degree operator is the plain file's `degree`, which no connection changes.
* [proved-derived; formal-checked] the twisted laws: `endMatrix_transpose_mul_startMatrixC`
  (`Tᵀ S_g = B_g + J_g`), `reversalC_mul_endMatrix_transpose` (`J_g Tᵀ = S'_gᵀ`),
  `reversalC_mul_startMatrixC'_transpose` (`J_g S'_gᵀ = Tᵀ`),
  `startMatrixC_mul_startMatrixC'_transpose` (`S_g S'_gᵀ = D`), `reversalC_mul_reversalC`
  (`J_g J_g = 1`), `det_one_add_smul_reversalC` (`det (1 + u J_g) = (1 − u²)^|E|`) and
  `bass_block_identity_connection`.
* [proved-derived; formal-checked] **`ihara_bass_connection`** (T1):
  `(1 − u²)^|V| · det (1 − u B_g) = det (1 − u A_g + u² (D − 1)) · (1 − u²)^|E|`, for every
  connection and every `u` in every commutative ring; with its forms
  `ihara_bass_connection_regular`, `ihara_bass_connection_cancel` and
  `det_hashimotoC_eq_zero_iff`.
* [proved-derived; formal-checked] the trivial connection (T2): at `g = 1` each twisted operator is
  the plain one (`startMatrixC_one`, `startMatrixC'_one`, `reversalC_one`, `hashimotoC_one`,
  `adjacencyC_one`), and `ihara_bass_of_connection` reads the plain theorem off T1.
* [proved-derived; formal-checked] the gauge (T3): for `h hinv : V → R` with `h v * hinv v = 1`,
  `gauge` is `g' d = h (src d) * g d * hinv (tgt d)`; `gauge_connection` (it is a connection),
  `gaugeDiag_mul_hashimotoC` (`Δ B_g = B_{g'} Δ` with `Δ = diag (h ∘ tgt)`),
  `gaugeDiag_mul_gaugeDiag` (`Δ` is invertible), `adjacencyC_gauge`
  (`A_{g'} = diag h · A_g · diag hinv`) and **`det_hashimotoC_gauge`**:
  `det (1 − u B_{g'}) = det (1 − u B_g)`.
* [interpretation] The gauge theorem says the determinant reads the connection only through what
  no change of frame at the cells removes: its holonomy around closed walks.  On a tree every
  connection is a gauge of the trivial one; that statement, and the Euler product that would
  display the holonomies, are not in this file.
* [proved-derived; formal-checked] a closed chain (T4): `det_hashimotoC_loop`, one cell and one
  contact that is a loop with transports `h`, `hinv` on its two darts:
  `det (1 − u B_g) = (1 − h u)(1 − hinv u)`, the two senses of the one closed walk, each read with
  its holonomy.
* [definition] the double cover of a sheet function `σ : darts → Bool`: cells `V × Bool`, darts
  `(E ⊕ E) × Bool`; the dart `(d, s)` leaves `src d` on sheet `s` and enters `tgt d` on sheet
  `s xor σ d`, and its reversal is `(d.swap, s xor σ d)`.  `coverHashimoto` is its dart operator,
  `sign σ` the connection `d ↦ if σ d then −1 else 1`.
* [proved-derived; formal-checked] **`artin_double_cover`** (T5):
  `det (1 − u B_Y) = det (1 − u B) · det (1 − u B_{sign σ})` over every commutative ring, with no
  division by two (`det_fromBlocks_swap`: `det [[X, Y], [Y, X]] = det (X + Y) · det (X − Y)` by two
  unimodular block operations).  `artin_double_cover_of_sign` states it for a connection `g` with
  values `±1`.  `sign_connection` and `swap_eq_of_sign` relate the two hypotheses
  (`σ d.swap = σ d`, and `g d * g d.swap = 1` with `g d = ±1`).
* [proved-derived; formal-checked] the cover is a complex of the plain kind:
  `hashimoto_cover` identifies `coverHashimoto` with the plain file's `hashimoto` of the contacts
  `E × Bool` with ends `coverA`, `coverB`, through `dartEquiv`; so
  **`artin_double_cover_hashimoto`**: the plain dart determinant of the cover is the base's times
  the sign connection's.
* [interpretation] T5 is Artin's factorization in its smallest case: the cover's zeta is the base's
  zeta times the L-function of the sign character.  A closed walk of the base lifts to two closed
  walks of its length or to one of twice its length, by its holonomy `±1` (split or inert).  That
  reading needs the Euler product over primitive closed walks, which is not proved here.

**What this does not state.**  No Euler product, `det (1 − u B_g) = ∏ (1 − hol(P) u^len P)`, is
proved, so the holonomy is displayed only by the gauge theorem and the closed chain.  The
connection is abelian (values in a commutative ring, one scalar a dart); a connection with values
in matrices, and Artin's factorization for a non-abelian group, are not here; the cover of any
number of sheets with abelian voltages is `Landmarks/IharaAbelianCover`.  The converse of the gauge theorem (two connections with equal holonomies
differ by a gauge) is not stated.  Nothing spectral is said.

Every theorem is discharged and none depends on `sorryAx`.
-/

open Matrix

namespace Holonics.Landmarks.IharaBassConnection

open Holonics.Landmarks.IharaBass

/-! ## The twisted operators -/

section Operators

variable {V E : Type*} [DecidableEq V] [DecidableEq E]
variable {R : Type*} [CommRing R] (a b : E → V) (g : E ⊕ E → R)

/-- [definition] The twisted start incidence `S_g`: `S_g v d = g d` when the dart `d` leaves `v`. -/
def startMatrixC : Matrix V (E ⊕ E) R :=
  Matrix.of fun v d => if src a b d = v then g d else 0

/-- [definition] The start incidence with the reversed dart's transport: `S'_g v d = g d.swap` when
`d` leaves `v`. -/
def startMatrixC' : Matrix V (E ⊕ E) R :=
  Matrix.of fun v d => if src a b d = v then g d.swap else 0

/-- [definition] The twisted reversal `J_g`: `J_g d f = g f` when `f` is `d` reversed. -/
def reversalC : Matrix (E ⊕ E) (E ⊕ E) R :=
  Matrix.of fun d f => if f = d.swap then g f else 0

/-- [definition] The twisted dart operator `B_g`: `B_g d f = g f` when `f` leaves the cell that `d`
enters and `f` is not `d` reversed. -/
def hashimotoC : Matrix (E ⊕ E) (E ⊕ E) R :=
  Matrix.of fun d f => if tgt a b d = src a b f ∧ f ≠ d.swap then g f else 0

omit [DecidableEq E] in
@[simp] theorem startMatrixC_apply (v : V) (d : E ⊕ E) :
    startMatrixC a b g v d = if src a b d = v then g d else 0 := rfl

omit [DecidableEq E] in
@[simp] theorem startMatrixC'_apply (v : V) (d : E ⊕ E) :
    startMatrixC' a b g v d = if src a b d = v then g d.swap else 0 := rfl

omit [DecidableEq V] in
@[simp] theorem reversalC_apply (d f : E ⊕ E) :
    reversalC g d f = if f = d.swap then g f else 0 := rfl

@[simp] theorem hashimotoC_apply (d f : E ⊕ E) :
    hashimotoC a b g d f = if tgt a b d = src a b f ∧ f ≠ d.swap then g f else 0 := rfl

end Operators

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {R : Type*} [CommRing R] (a b : E → V) (g : E ⊕ E → R)

/-- [definition] The twisted cell operator `A_g = S_g Tᵀ`: `A_g v w` sums the transports of the
darts from `v` to `w`. -/
def adjacencyC : Matrix V V R := startMatrixC a b g * (endMatrix R a b)ᵀ

/-! ## The twisted laws -/

omit [Fintype E] in
/-- [proved-derived; formal-checked] `Tᵀ S_g = B_g + J_g`: the darts leaving the cell that `d`
enters, each with its transport, are the non-backtracking continuations and the one reversal. -/
theorem endMatrix_transpose_mul_startMatrixC :
    (endMatrix R a b)ᵀ * startMatrixC a b g = hashimotoC a b g + reversalC g := by
  ext d f
  simp only [Matrix.mul_apply, Matrix.transpose_apply, endMatrix_apply, startMatrixC_apply,
    Matrix.add_apply, hashimotoC_apply, reversalC_apply, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq Finset.univ (tgt a b d)]
  simp only [Finset.mem_univ, if_true]
  by_cases hf : f = d.swap
  · have hs : src a b f = tgt a b d := by rw [hf, src_swap]
    rw [if_pos hs, if_neg (fun h => h.2 hf), if_pos hf, zero_add]
  · by_cases ht : tgt a b d = src a b f
    · rw [if_pos ht.symm, if_pos ⟨ht, hf⟩, if_neg hf, add_zero]
    · rw [if_neg (fun h => ht h.symm), if_neg (fun h => ht h.1), if_neg hf, add_zero]

omit [Fintype V] in
/-- [proved-derived; formal-checked] `J_g Tᵀ = S'_gᵀ`. -/
theorem reversalC_mul_endMatrix_transpose :
    reversalC g * (endMatrix R a b)ᵀ = (startMatrixC' a b g)ᵀ := by
  ext d v
  simp only [Matrix.mul_apply, reversalC_apply, Matrix.transpose_apply, endMatrix_apply,
    startMatrixC'_apply, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq' Finset.univ d.swap]
  simp only [Finset.mem_univ, if_true, tgt_swap, mul_ite, mul_one, mul_zero]

omit [Fintype V] in
/-- [proved-derived; formal-checked] `J_g S'_gᵀ = Tᵀ`: the reversed transport undoes the
transport. -/
theorem reversalC_mul_startMatrixC'_transpose (hg : ∀ d, g d * g d.swap = 1) :
    reversalC g * (startMatrixC' a b g)ᵀ = (endMatrix R a b)ᵀ := by
  ext d v
  simp only [Matrix.mul_apply, reversalC_apply, Matrix.transpose_apply, endMatrix_apply,
    startMatrixC'_apply, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq' Finset.univ d.swap]
  simp only [Finset.mem_univ, if_true, src_swap, Sum.swap_swap, mul_ite, mul_zero]
  rw [mul_comm, hg]

omit [Fintype V] [DecidableEq E] in
/-- [proved-derived; formal-checked] `S_g S'_gᵀ = D`: a dart's transport against its reversal's is
one, so the degree operator is the plain one. -/
theorem startMatrixC_mul_startMatrixC'_transpose (hg : ∀ d, g d * g d.swap = 1) :
    startMatrixC a b g * (startMatrixC' a b g)ᵀ = degree R a b := by
  ext v w
  simp only [degree, Matrix.mul_apply, Matrix.transpose_apply, startMatrixC_apply,
    startMatrixC'_apply, startMatrix_apply]
  refine Finset.sum_congr rfl fun d _ => ?_
  by_cases hv : src a b d = v
  · by_cases hw : src a b d = w
    · rw [if_pos hv, if_pos hw, if_pos hv, if_pos hw, hg, mul_one]
    · rw [if_neg hw, if_neg hw, mul_zero, mul_zero]
  · rw [if_neg hv, if_neg hv, zero_mul, zero_mul]

omit [Fintype V] [DecidableEq V] in
/-- [proved-derived; formal-checked] `J_g J_g = 1`. -/
theorem reversalC_mul_reversalC (hg : ∀ d, g d * g d.swap = 1) :
    reversalC g * reversalC g = 1 := by
  ext d f
  simp only [Matrix.mul_apply, reversalC_apply, Matrix.one_apply, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq' Finset.univ d.swap]
  simp only [Finset.mem_univ, if_true, Sum.swap_swap, mul_ite, mul_zero]
  by_cases h : d = f
  · subst h
    rw [if_pos rfl, if_pos rfl, mul_comm, hg]
  · rw [if_neg (Ne.symm h), if_neg h]

omit [Fintype V] [DecidableEq V] [Fintype E] in
/-- [proved-derived; formal-checked] In the two halves of the darts, `1 + u J_g` is the block matrix
`[[1, u g⁻], [u g⁺, 1]]` with the two halves' transports on the diagonals. -/
theorem one_add_smul_reversalC (u : R) :
    (1 : Matrix (E ⊕ E) (E ⊕ E) R) + u • reversalC g =
      Matrix.fromBlocks 1 (u • Matrix.diagonal fun i => g (Sum.inr i))
        (u • Matrix.diagonal fun i => g (Sum.inl i)) 1 := by
  ext (i | i) (j | j)
  · simp [Matrix.one_apply]
  · rcases eq_or_ne i j with rfl | h
    · simp
    · simp [h, Ne.symm h]
  · rcases eq_or_ne i j with rfl | h
    · simp
    · simp [h, Ne.symm h]
  · simp [Matrix.one_apply]

omit [Fintype V] [DecidableEq V] in
/-- [proved-derived; formal-checked] `det (1 + u J_g) = (1 − u²)^|E|`: each contact's two darts make
one block `[[1, u g⁻], [u g⁺, 1]]` of determinant `1 − u² g⁺ g⁻ = 1 − u²`. -/
theorem det_one_add_smul_reversalC (hg : ∀ d, g d * g d.swap = 1) (u : R) :
    ((1 : Matrix (E ⊕ E) (E ⊕ E) R) + u • reversalC g).det = (1 - u ^ 2) ^ Fintype.card E := by
  rw [one_add_smul_reversalC, Matrix.det_fromBlocks_one₁₁]
  have hd : (Matrix.diagonal fun i : E => g (Sum.inl i) * g (Sum.inr i)) = (1 : Matrix E E R) := by
    rw [← Matrix.diagonal_one]
    congr 1
    funext i
    exact hg (Sum.inl i)
  have h : (1 : Matrix E E R) - (u • Matrix.diagonal fun i => g (Sum.inl i)) *
      (u • Matrix.diagonal fun i => g (Sum.inr i)) = (1 - u ^ 2) • (1 : Matrix E E R) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.diagonal_mul_diagonal, hd, smul_smul, sub_smul,
      one_smul, pow_two]
  rw [h, Matrix.det_smul, Matrix.det_one, mul_one]

/-! ## Bass's block identity and the determinant formula, with a connection -/

/-- [proved-derived; formal-checked] Bass's block identity on `V ⊕ darts` with a connection.  It
divides by nothing. -/
theorem bass_block_identity_connection (hg : ∀ d, g d * g d.swap = 1) (u : R) :
    Matrix.fromBlocks (1 : Matrix V V R) 0 (endMatrix R a b)ᵀ 1 *
        Matrix.fromBlocks ((1 - u ^ 2) • (1 : Matrix V V R)) (u • startMatrixC a b g) 0
          (1 - u • hashimotoC a b g) =
      Matrix.fromBlocks (1 - u • adjacencyC a b g + u ^ 2 • (degree R a b - 1))
          (u • startMatrixC a b g) 0 (1 + u • reversalC g) *
        Matrix.fromBlocks 1 0 ((endMatrix R a b)ᵀ - u • (startMatrixC' a b g)ᵀ) 1 := by
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply,
    ← startMatrixC_mul_startMatrixC'_transpose a b g hg]
  congr 1
  · -- the cells' block: `(1 − u²) = 1 − u A_g + u² (D − 1) + u S_g (Tᵀ − u S'_gᵀ)`
    simp only [Matrix.mul_one, Matrix.zero_mul, add_zero, Matrix.mul_sub,
      Matrix.smul_mul, Matrix.mul_smul, adjacencyC]
    module
  · -- the upper right block: `u S_g` on both sides
    simp only [Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, add_zero,
      zero_add]
  · -- the lower left block: `Tᵀ (1 − u²) = (1 + u J_g)(Tᵀ − u S'_gᵀ)`
    simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, add_zero,
      zero_add, Matrix.mul_sub, Matrix.add_mul, Matrix.smul_mul, Matrix.mul_smul,
      reversalC_mul_endMatrix_transpose, reversalC_mul_startMatrixC'_transpose a b g hg]
    module
  · -- the darts' block: `Tᵀ (u S_g) + 1 − u B_g = 1 + u J_g`
    simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, zero_add,
      Matrix.mul_smul, endMatrix_transpose_mul_startMatrixC]
    module

/-- [proved-derived; formal-checked] **Ihara–Bass with a connection.**  For every finite multigraph,
every connection `g` (`g d * g d.swap = 1`) and every `u` in every commutative ring,
`(1 − u²)^|V| · det (1 − u B_g) = det (1 − u A_g + u² (D − 1)) · (1 − u²)^|E|`. -/
theorem ihara_bass_connection (hg : ∀ d, g d * g d.swap = 1) (u : R) :
    (1 - u ^ 2) ^ Fintype.card V * (1 - u • hashimotoC a b g).det =
      (1 - u • adjacencyC a b g + u ^ 2 • (degree R a b - 1)).det *
        (1 - u ^ 2) ^ Fintype.card E := by
  have h := congrArg Matrix.det (bass_block_identity_connection a b g hg u)
  simp only [Matrix.det_mul, Matrix.det_fromBlocks_zero₁₂, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_one, Matrix.det_smul, one_mul, mul_one, det_one_add_smul_reversalC g hg] at h
  exact h

/-- [proved-derived; formal-checked] The regular case with a connection: when every cell has `q + 1`
darts, `(1 − u²)^|V| · det (1 − u B_g) = det ((1 + q u²) − u A_g) · (1 − u²)^|E|`. -/
theorem ihara_bass_connection_regular (hg : ∀ d, g d * g d.swap = 1) {q : ℕ}
    (hreg : ∀ v : V, (Finset.univ.filter fun d : E ⊕ E => src a b d = v).card = q + 1) (u : R) :
    (1 - u ^ 2) ^ Fintype.card V * (1 - u • hashimotoC a b g).det =
      ((1 + (q : R) * u ^ 2) • (1 : Matrix V V R) - u • adjacencyC a b g).det *
        (1 - u ^ 2) ^ Fintype.card E := by
  rw [ihara_bass_connection a b g hg, degree_eq_smul_one_of_regular R a b hreg]
  congr 2
  module

/-- [proved-derived; formal-checked] In a domain with `u² ≠ 1` and `|V| ≤ |E|`,
`det (1 − u B_g) = (1 − u²)^(|E| − |V|) · det (1 − u A_g + u² (D − 1))`. -/
theorem ihara_bass_connection_cancel [IsDomain R] (hg : ∀ d, g d * g d.swap = 1) {u : R}
    (hu : u ^ 2 ≠ 1) (hVE : Fintype.card V ≤ Fintype.card E) :
    (1 - u • hashimotoC a b g).det =
      (1 - u ^ 2) ^ (Fintype.card E - Fintype.card V) *
        (1 - u • adjacencyC a b g + u ^ 2 • (degree R a b - 1)).det := by
  have hne : (1 - u ^ 2) ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
  have h := ihara_bass_connection a b g hg u
  refine mul_left_cancel₀ (pow_ne_zero (Fintype.card V) hne) ?_
  rw [h, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hVE, mul_comm]

/-- [proved-derived; formal-checked] In a domain, away from `u² = 1`, the twisted dart determinant
and the twisted cell determinant vanish together. -/
theorem det_hashimotoC_eq_zero_iff [IsDomain R] (hg : ∀ d, g d * g d.swap = 1) {u : R}
    (hu : u ^ 2 ≠ 1) :
    (1 - u • hashimotoC a b g).det = 0 ↔
      (1 - u • adjacencyC a b g + u ^ 2 • (degree R a b - 1)).det = 0 := by
  have hne : (1 - u ^ 2) ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
  have h := ihara_bass_connection a b g hg u
  constructor
  · intro h0
    rw [h0, mul_zero] at h
    exact (mul_eq_zero.mp h.symm).resolve_right (pow_ne_zero _ hne)
  · intro h0
    rw [h0, zero_mul] at h
    exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ hne)

/-! ## The trivial connection -/

omit [Fintype V] [Fintype E] [DecidableEq E] in
/-- [proved-derived; formal-checked] At `g = 1`, `S_g` is the plain start incidence. -/
theorem startMatrixC_one : startMatrixC a b (fun _ => (1 : R)) = startMatrix R a b := rfl

omit [Fintype V] [Fintype E] [DecidableEq E] in
/-- [proved-derived; formal-checked] At `g = 1`, `S'_g` is the plain start incidence. -/
theorem startMatrixC'_one : startMatrixC' a b (fun _ => (1 : R)) = startMatrix R a b := rfl

omit [Fintype V] [DecidableEq V] [Fintype E] in
/-- [proved-derived; formal-checked] At `g = 1`, `J_g` is the plain reversal. -/
theorem reversalC_one : reversalC (fun _ : E ⊕ E => (1 : R)) = reversal R E := rfl

omit [Fintype V] [Fintype E] in
/-- [proved-derived; formal-checked] At `g = 1`, `B_g` is the plain dart operator. -/
theorem hashimotoC_one : hashimotoC a b (fun _ => (1 : R)) = hashimoto R a b := rfl

omit [Fintype V] [DecidableEq E] in
/-- [proved-derived; formal-checked] At `g = 1`, `A_g` is the plain cell operator. -/
theorem adjacencyC_one : adjacencyC a b (fun _ => (1 : R)) = adjacency R a b := rfl

/-- [proved-derived; formal-checked] The plain Ihara–Bass identity, read off the twisted one at the
trivial connection. -/
theorem ihara_bass_of_connection (u : R) :
    (1 - u ^ 2) ^ Fintype.card V * (1 - u • hashimoto R a b).det =
      (1 - u • adjacency R a b + u ^ 2 • (degree R a b - 1)).det *
        (1 - u ^ 2) ^ Fintype.card E := by
  have h := ihara_bass_connection a b (fun _ => (1 : R)) (fun _ => mul_one 1) u
  rwa [hashimotoC_one, adjacencyC_one] at h

/-! ## The gauge -/

section Gauge

variable (h hinv : V → R)

/-- [definition] A change of frame at the cells: `g' d = h (src d) * g d * hinv (tgt d)`. -/
def gauge : E ⊕ E → R := fun d => h (src a b d) * g d * hinv (tgt a b d)

/-- [definition] The diagonal `Δ = diag (h ∘ tgt)` on darts. -/
def gaugeDiag : Matrix (E ⊕ E) (E ⊕ E) R := Matrix.diagonal fun d => h (tgt a b d)

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
/-- [proved-derived; formal-checked] A gauge of a connection is a connection. -/
theorem gauge_connection (hg : ∀ d, g d * g d.swap = 1) (hh : ∀ v, h v * hinv v = 1)
    (d : E ⊕ E) : gauge a b g h hinv d * gauge a b g h hinv d.swap = 1 := by
  simp only [gauge, src_swap, tgt_swap]
  calc h (src a b d) * g d * hinv (tgt a b d) * (h (tgt a b d) * g d.swap * hinv (src a b d))
      = (h (src a b d) * hinv (src a b d)) * (h (tgt a b d) * hinv (tgt a b d)) *
          (g d * g d.swap) := by ring
    _ = 1 := by rw [hh, hh, hg, mul_one, mul_one]

omit [Fintype V] in
/-- [proved-derived; formal-checked] `Δ B_g = B_{g'} Δ`: the gauge conjugates the dart operator by
the diagonal of the frames at the darts' ends. -/
theorem gaugeDiag_mul_hashimotoC (hh : ∀ v, h v * hinv v = 1) :
    gaugeDiag a b h * hashimotoC a b g = hashimotoC a b (gauge a b g h hinv) * gaugeDiag a b h := by
  ext d f
  rw [gaugeDiag, Matrix.diagonal_mul, Matrix.mul_diagonal]
  simp only [hashimotoC_apply, gauge]
  by_cases hc : tgt a b d = src a b f ∧ f ≠ d.swap
  · rw [if_pos hc, if_pos hc, hc.1]
    calc h (src a b f) * g f
        = h (src a b f) * g f * (h (tgt a b f) * hinv (tgt a b f)) := by rw [hh, mul_one]
      _ = h (src a b f) * g f * hinv (tgt a b f) * h (tgt a b f) := by ring
  · rw [if_neg hc, if_neg hc, mul_zero, zero_mul]

omit [Fintype V] [DecidableEq V] in
/-- [proved-derived; formal-checked] `Δ` is invertible, with inverse the diagonal of `hinv ∘ tgt`. -/
theorem gaugeDiag_mul_gaugeDiag (hh : ∀ v, h v * hinv v = 1) :
    gaugeDiag a b h * gaugeDiag a b hinv = (1 : Matrix (E ⊕ E) (E ⊕ E) R) := by
  rw [gaugeDiag, gaugeDiag, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext d
  exact hh _

omit [Fintype V] in
/-- [proved-derived; formal-checked] **The gauge leaves the determinant.**  For frames `h` with
inverses `hinv`, `det (1 − u B_{g'}) = det (1 − u B_g)`: the dart determinant reads a connection
only up to a change of frame at the cells. -/
theorem det_hashimotoC_gauge (hh : ∀ v, h v * hinv v = 1) (u : R) :
    (1 - u • hashimotoC a b (gauge a b g h hinv)).det = (1 - u • hashimotoC a b g).det := by
  have h1 : gaugeDiag a b h * (1 - u • hashimotoC a b g) =
      (1 - u • hashimotoC a b (gauge a b g h hinv)) * gaugeDiag a b h := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_smul,
      Matrix.smul_mul, gaugeDiag_mul_hashimotoC a b g h hinv hh]
  have hdet : (gaugeDiag a b h).det * (gaugeDiag a b hinv).det = 1 := by
    rw [← Matrix.det_mul, gaugeDiag_mul_gaugeDiag a b h hinv hh, Matrix.det_one]
  have h2 := congrArg Matrix.det h1
  rw [Matrix.det_mul, Matrix.det_mul] at h2
  calc (1 - u • hashimotoC a b (gauge a b g h hinv)).det
      = (1 - u • hashimotoC a b (gauge a b g h hinv)).det *
          ((gaugeDiag a b h).det * (gaugeDiag a b hinv).det) := by rw [hdet, mul_one]
    _ = ((1 - u • hashimotoC a b (gauge a b g h hinv)).det * (gaugeDiag a b h).det) *
          (gaugeDiag a b hinv).det := by ring
    _ = ((gaugeDiag a b h).det * (1 - u • hashimotoC a b g).det) *
          (gaugeDiag a b hinv).det := by rw [← h2]
    _ = (1 - u • hashimotoC a b g).det *
          ((gaugeDiag a b h).det * (gaugeDiag a b hinv).det) := by ring
    _ = (1 - u • hashimotoC a b g).det := by rw [hdet, mul_one]

omit [DecidableEq E] in
/-- [proved-derived; formal-checked] On the cells the gauge is `A_{g'} = diag h · A_g · diag hinv`. -/
theorem adjacencyC_gauge :
    adjacencyC a b (gauge a b g h hinv) =
      Matrix.diagonal h * adjacencyC a b g * Matrix.diagonal hinv := by
  ext v w
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [adjacencyC, Matrix.mul_apply, Matrix.transpose_apply, startMatrixC_apply,
    endMatrix_apply, gauge]
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d _ => ?_
  by_cases hv : src a b d = v
  · by_cases hw : tgt a b d = w
    · rw [if_pos hv, if_pos hw, if_pos hv, hv, hw]
      ring
    · rw [if_neg hw, mul_zero, mul_zero, mul_zero, zero_mul]
  · rw [if_neg hv, if_neg hv, zero_mul, mul_zero, zero_mul]

end Gauge

/-! ## A closed chain of one contact -/

/-- [proved-derived; formal-checked] One cell and one contact that is a loop.  Its two darts are the
two senses of the one closed walk, and `det (1 − u B_g) = (1 − g⁺ u)(1 − g⁻ u)`: each sense is read
with its own transport. -/
theorem det_hashimotoC_loop (g : Unit ⊕ Unit → R) (u : R) :
    (1 - u • hashimotoC (fun _ : Unit => ()) (fun _ : Unit => ()) g).det =
      (1 - g (Sum.inl ()) * u) * (1 - g (Sum.inr ()) * u) := by
  have h : (1 - u • hashimotoC (fun _ : Unit => ()) (fun _ : Unit => ()) g) =
      Matrix.fromBlocks (Matrix.of fun _ _ => 1 - g (Sum.inl ()) * u) 0 0
        (Matrix.of fun _ _ => 1 - g (Sum.inr ()) * u) := by
    ext (i | i) (j | j) <;> simp [mul_comm]
  rw [h, Matrix.det_fromBlocks_zero₁₂, Matrix.det_unique, Matrix.det_unique]
  rfl

/-- [proved-derived; formal-checked] The closed chain with holonomy `h` and its inverse named:
`det (1 − u B_g) = (1 − h u)(1 − hinv u)`. -/
theorem det_hashimotoC_loop_holonomy (g : Unit ⊕ Unit → R) (h hinv : R)
    (hl : g (Sum.inl ()) = h) (hr : g (Sum.inr ()) = hinv) (u : R) :
    (1 - u • hashimotoC (fun _ : Unit => ()) (fun _ : Unit => ()) g).det =
      (1 - h * u) * (1 - hinv * u) := by
  rw [det_hashimotoC_loop, hl, hr]

/-! ## A double cover: Artin's factorization -/

section DoubleCover

/-- [proved-derived; formal-checked] `det [[X, Y], [Y, X]] = det (X + Y) · det (X − Y)` over every
commutative ring: add the second block row to the first, then subtract the first block column from
the second.  Nothing is divided by two. -/
theorem det_fromBlocks_swap {n : Type*} [Fintype n] [DecidableEq n] (X Y : Matrix n n R) :
    (Matrix.fromBlocks X Y Y X).det = (X + Y).det * (X - Y).det := by
  have h : Matrix.fromBlocks (1 : Matrix n n R) 1 0 1 * Matrix.fromBlocks X Y Y X *
      Matrix.fromBlocks (1 : Matrix n n R) (-1) 0 1 = Matrix.fromBlocks (X + Y) 0 Y (X - Y) := by
    rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    congr 1
    · simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, add_zero]
    · simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_neg]
      abel
    · simp only [Matrix.one_mul, Matrix.zero_mul, Matrix.mul_one, Matrix.mul_zero, add_zero,
        zero_add]
    · simp only [Matrix.one_mul, Matrix.zero_mul, Matrix.mul_one, Matrix.mul_neg, zero_add]
      abel
  have hd := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_fromBlocks_zero₁₂, Matrix.det_one] at hd
  simpa using hd

variable (R)

/-- [definition] The sign connection of a sheet function: `−1` on the darts that change sheet. -/
def sign (σ : E ⊕ E → Bool) : E ⊕ E → R := fun d => if σ d then -1 else 1

/-- [definition] The dart operator of the double cover of `σ`.  The dart `(d, s)` leaves `src d` on
sheet `s` and enters `tgt d` on sheet `s xor σ d`; `(f, s')` continues it when `f` leaves the cell
`d` enters, `f` is not `d` reversed and `s'` is the sheet `(d, s)` ends on. -/
def coverHashimoto (σ : E ⊕ E → Bool) : Matrix ((E ⊕ E) × Bool) ((E ⊕ E) × Bool) R :=
  Matrix.of fun p p' =>
    if tgt a b p.1 = src a b p'.1 ∧ p'.1 ≠ p.1.swap ∧ p'.2 = Bool.xor p.2 (σ p.1) then 1 else 0

/-- [definition] The part of the dart operator whose first dart stays on its sheet. -/
def stay (σ : E ⊕ E → Bool) : Matrix (E ⊕ E) (E ⊕ E) R :=
  Matrix.of fun d f => if tgt a b d = src a b f ∧ f ≠ d.swap ∧ σ d = false then 1 else 0

/-- [definition] The part of the dart operator whose first dart crosses to the other sheet. -/
def cross (σ : E ⊕ E → Bool) : Matrix (E ⊕ E) (E ⊕ E) R :=
  Matrix.of fun d f => if tgt a b d = src a b f ∧ f ≠ d.swap ∧ σ d = true then 1 else 0

variable {R}

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
/-- [proved-derived; formal-checked] A sheet function equal on a dart and its reversal gives a
connection: `sign σ d * sign σ d.swap = 1`. -/
theorem sign_connection (σ : E ⊕ E → Bool) (hσ : ∀ d, σ d.swap = σ d) (d : E ⊕ E) :
    sign R σ d * sign R σ d.swap = 1 := by
  simp only [sign, hσ d]
  cases σ d <;> simp

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
/-- [proved-derived; formal-checked] A connection with values `±1` is equal on a dart and its
reversal. -/
theorem swap_eq_of_sign (hg : ∀ d, g d * g d.swap = 1) (hsign : ∀ d, g d = 1 ∨ g d = -1)
    (d : E ⊕ E) : g d.swap = g d := by
  have hsq : g d * g d = 1 := by
    rcases hsign d with h | h <;> rw [h] <;> ring
  calc g d.swap = (g d * g d) * g d.swap := by rw [hsq, one_mul]
    _ = g d * (g d * g d.swap) := by ring
    _ = g d := by rw [hg, mul_one]

omit [Fintype V] [Fintype E] in
/-- [proved-derived; formal-checked] The two parts sum to the dart operator. -/
theorem stay_add_cross (σ : E ⊕ E → Bool) : stay R a b σ + cross R a b σ = hashimoto R a b := by
  ext d f
  simp only [Matrix.add_apply, stay, cross, Matrix.of_apply, hashimoto_apply]
  by_cases hc : tgt a b d = src a b f ∧ f ≠ d.swap
  · cases hs : σ d <;> simp [hc]
  · have h1 : ¬ (tgt a b d = src a b f ∧ f ≠ d.swap ∧ σ d = false) := fun h => hc ⟨h.1, h.2.1⟩
    have h2 : ¬ (tgt a b d = src a b f ∧ f ≠ d.swap ∧ σ d = true) := fun h => hc ⟨h.1, h.2.1⟩
    rw [if_neg h1, if_neg h2, if_neg hc, add_zero]

omit [Fintype V] in
/-- [proved-derived; formal-checked] Their difference is the dart operator with the sign of the
first dart: `stay − cross = diag (sign σ) · B`. -/
theorem stay_sub_cross (σ : E ⊕ E → Bool) :
    stay R a b σ - cross R a b σ = Matrix.diagonal (sign R σ) * hashimoto R a b := by
  ext d f
  rw [Matrix.diagonal_mul]
  simp only [Matrix.sub_apply, stay, cross, Matrix.of_apply, hashimoto_apply, sign]
  by_cases hc : tgt a b d = src a b f ∧ f ≠ d.swap
  · cases hs : σ d <;> simp [hc]
  · have h1 : ¬ (tgt a b d = src a b f ∧ f ≠ d.swap ∧ σ d = false) := fun h => hc ⟨h.1, h.2.1⟩
    have h2 : ¬ (tgt a b d = src a b f ∧ f ≠ d.swap ∧ σ d = true) := fun h => hc ⟨h.1, h.2.1⟩
    rw [if_neg h1, if_neg h2, if_neg hc, sub_zero, mul_zero]

omit [Fintype V] in
/-- [proved-derived; formal-checked] `B · diag g = B_g`: weighing the second dart is the twisted
dart operator. -/
theorem hashimoto_mul_diagonal (g : E ⊕ E → R) :
    hashimoto R a b * Matrix.diagonal g = hashimotoC a b g := by
  ext d f
  rw [Matrix.mul_diagonal]
  simp only [hashimoto_apply, hashimotoC_apply]
  split_ifs <;> simp

/-- [definition] The two sheets as the two halves of a sum: `(d, false) ↦ inl d`,
`(d, true) ↦ inr d`. -/
def sheetEquiv (D : Type*) : D × Bool ≃ D ⊕ D where
  toFun p := if p.2 then Sum.inr p.1 else Sum.inl p.1
  invFun := Sum.elim (fun d => (d, false)) (fun d => (d, true))
  left_inv := by rintro ⟨d, _ | _⟩ <;> rfl
  right_inv := by rintro (d | d) <;> rfl

omit [Fintype V] [Fintype E] in
/-- [proved-derived; formal-checked] By sheets, `1 − u B_Y` is the block matrix
`[[1 − u stay, −u cross], [−u cross, 1 − u stay]]`. -/
theorem one_sub_smul_coverHashimoto_reindex (σ : E ⊕ E → Bool) (u : R) :
    Matrix.reindex (sheetEquiv (E ⊕ E)) (sheetEquiv (E ⊕ E)) (1 - u • coverHashimoto R a b σ) =
      Matrix.fromBlocks (1 - u • stay R a b σ) (-(u • cross R a b σ)) (-(u • cross R a b σ))
        (1 - u • stay R a b σ) := by
  ext (d | d) (f | f)
  · cases hs : σ d <;>
      simp [sheetEquiv, coverHashimoto, stay, Matrix.one_apply, hs]
  · cases hs : σ d <;>
      simp [sheetEquiv, coverHashimoto, cross, hs]
  · cases hs : σ d <;>
      simp [sheetEquiv, coverHashimoto, cross, hs]
  · cases hs : σ d <;>
      simp [sheetEquiv, coverHashimoto, stay, Matrix.one_apply, hs]

omit [Fintype V] in
/-- [proved-derived; formal-checked] **Artin's factorization for a double cover.**  For every sheet
function `σ` on the darts and every `u` in every commutative ring,
`det (1 − u B_Y) = det (1 − u B) · det (1 − u B_{sign σ})`: the cover's dart determinant is the
base's times the sign connection's.  (The identity needs no hypothesis on `σ`; `σ d.swap = σ d`
is what makes `B_Y` the dart operator of a complex, `hashimoto_cover`.) -/
theorem artin_double_cover (σ : E ⊕ E → Bool) (u : R) :
    (1 - u • coverHashimoto R a b σ).det =
      (1 - u • hashimoto R a b).det * (1 - u • hashimotoC a b (sign R σ)).det := by
  rw [← Matrix.det_reindex_self (sheetEquiv (E ⊕ E)) (1 - u • coverHashimoto R a b σ),
    one_sub_smul_coverHashimoto_reindex, det_fromBlocks_swap]
  have h1 : (1 - u • stay R a b σ) + (-(u • cross R a b σ)) = 1 - u • hashimoto R a b := by
    rw [← stay_add_cross a b σ]
    module
  have h2 : (1 - u • stay R a b σ) - (-(u • cross R a b σ)) =
      1 - (u • Matrix.diagonal (sign R σ)) * hashimoto R a b := by
    rw [Matrix.smul_mul, ← stay_sub_cross a b σ]
    module
  rw [h1, h2, Matrix.det_one_sub_mul_comm, Matrix.mul_smul, hashimoto_mul_diagonal]

omit [Fintype V] in
/-- [proved-derived; formal-checked] The factorization for a connection with values `±1`: the cover
is that of the sheet function `d ↦ (g d ≠ 1)`. -/
theorem artin_double_cover_of_sign [DecidableEq R] (hsign : ∀ d, g d = 1 ∨ g d = -1) (u : R) :
    (1 - u • coverHashimoto R a b (fun d => !decide (g d = 1))).det =
      (1 - u • hashimoto R a b).det * (1 - u • hashimotoC a b g).det := by
  have hg' : sign R (fun d => !decide (g d = 1)) = g := by
    funext d
    by_cases h1 : g d = 1
    · simp [sign, h1]
    · rcases hsign d with h | h
      · exact absurd h h1
      · have hd : (!decide (g d = 1)) = true := by simp [h1]
        change (if (!decide (g d = 1)) = true then (-1 : R) else 1) = g d
        rw [if_pos hd, h]
  rw [artin_double_cover, hg']

/-! ### The cover is a complex of the plain kind -/

/-- [definition] The cover's contacts are `E × Bool`; the first end of `(e, s)` is `a e` on sheet
`s`. -/
def coverA : E × Bool → V × Bool := fun p => (a p.1, p.2)

/-- [definition] The second end of `(e, s)` is `b e` on the sheet the dart `inl e` ends on. -/
def coverB (σ : E ⊕ E → Bool) : E × Bool → V × Bool :=
  fun p => (b p.1, Bool.xor p.2 (σ (Sum.inl p.1)))

/-- [definition] The cover's darts in the two models: `inl (e, s) ↦ (inl e, s)` and
`inr (e, s) ↦ (inr e, s xor σ (inl e))`, the sheet the reversed dart leaves. -/
def dartEquiv (σ : E ⊕ E → Bool) : (E × Bool) ⊕ (E × Bool) ≃ (E ⊕ E) × Bool where
  toFun := Sum.elim (fun p => (Sum.inl p.1, p.2))
    (fun p => (Sum.inr p.1, Bool.xor p.2 (σ (Sum.inl p.1))))
  invFun q := Sum.elim (fun e => Sum.inl (e, q.2))
    (fun e => Sum.inr (e, Bool.xor q.2 (σ (Sum.inl e)))) q.1
  left_inv := by
    rintro (⟨e, s⟩ | ⟨e, s⟩)
    · rfl
    · simp
  right_inv := by
    rintro ⟨e | e, s⟩
    · rfl
    · simp

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
/-- [proved-derived; formal-checked] A cover dart leaves the base dart's start on its own sheet. -/
theorem cover_src (σ : E ⊕ E → Bool) (y : (E × Bool) ⊕ (E × Bool)) :
    src (coverA a) (coverB b σ) y = (src a b (dartEquiv σ y).1, (dartEquiv σ y).2) := by
  rcases y with ⟨e, s⟩ | ⟨e, s⟩ <;> rfl

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
/-- [proved-derived; formal-checked] A cover dart enters the base dart's end on the sheet
`s xor σ d`. -/
theorem cover_tgt (σ : E ⊕ E → Bool) (hσ : ∀ d, σ d.swap = σ d) (x : (E × Bool) ⊕ (E × Bool)) :
    tgt (coverA a) (coverB b σ) x =
      (tgt a b (dartEquiv σ x).1,
        Bool.xor (dartEquiv σ x).2 (σ (dartEquiv σ x).1)) := by
  rcases x with ⟨e, s⟩ | ⟨e, s⟩
  · rfl
  · have h := hσ (Sum.inl e)
    simp only [Sum.swap_inl] at h
    simp [dartEquiv, coverA, h]

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] in
/-- [proved-derived; formal-checked] The reversal of a cover dart is `(d.swap, s xor σ d)`. -/
theorem dartEquiv_swap (σ : E ⊕ E → Bool) (hσ : ∀ d, σ d.swap = σ d)
    (x : (E × Bool) ⊕ (E × Bool)) :
    dartEquiv σ x.swap =
      ((dartEquiv σ x).1.swap, Bool.xor (dartEquiv σ x).2 (σ (dartEquiv σ x).1)) := by
  rcases x with ⟨e, s⟩ | ⟨e, s⟩
  · rfl
  · have h := hσ (Sum.inl e)
    simp only [Sum.swap_inl] at h
    simp [dartEquiv, h]

omit [Fintype V] [Fintype E] in
/-- [proved-derived; formal-checked] The cover's dart operator is the plain file's `hashimoto` of
the contacts `E × Bool` with ends `coverA`, `coverB`, through `dartEquiv`. -/
theorem hashimoto_cover (σ : E ⊕ E → Bool) (hσ : ∀ d, σ d.swap = σ d) :
    hashimoto R (coverA a) (coverB b σ) =
      (coverHashimoto R a b σ).submatrix (dartEquiv σ) (dartEquiv σ) := by
  ext x y
  simp only [hashimoto_apply, Matrix.submatrix_apply, coverHashimoto, Matrix.of_apply]
  refine if_congr ?_ rfl rfl
  rw [cover_tgt a b σ hσ, cover_src, ← (dartEquiv σ).injective.ne_iff, dartEquiv_swap σ hσ]
  generalize dartEquiv σ x = p
  generalize dartEquiv σ y = p'
  obtain ⟨d, s⟩ := p
  obtain ⟨f, s'⟩ := p'
  simp only [Prod.mk.injEq, ne_eq, not_and]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, fun hf => h3 hf h2.symm, h2.symm⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h3.symm⟩, fun hf => absurd hf h2⟩

omit [Fintype V] in
/-- [proved-derived; formal-checked] **Artin's factorization on the plain model.**  For a sheet
function with `σ d.swap = σ d`, the dart determinant of the cover (contacts `E × Bool`, ends
`coverA`, `coverB`) is the base's times the sign connection's. -/
theorem artin_double_cover_hashimoto (σ : E ⊕ E → Bool) (hσ : ∀ d, σ d.swap = σ d) (u : R) :
    (1 - u • hashimoto R (coverA a) (coverB b σ)).det =
      (1 - u • hashimoto R a b).det * (1 - u • hashimotoC a b (sign R σ)).det := by
  rw [hashimoto_cover a b σ hσ, ← artin_double_cover a b σ u,
    ← Matrix.det_submatrix_equiv_self (dartEquiv σ) (1 - u • coverHashimoto R a b σ)]
  congr 1
  ext x y
  simp [Matrix.one_apply, (dartEquiv σ).injective.eq_iff]

end DoubleCover

section Audit

#print axioms endMatrix_transpose_mul_startMatrixC
#print axioms reversalC_mul_reversalC
#print axioms det_one_add_smul_reversalC
#print axioms bass_block_identity_connection
#print axioms ihara_bass_connection
#print axioms ihara_bass_connection_regular
#print axioms ihara_bass_connection_cancel
#print axioms det_hashimotoC_eq_zero_iff
#print axioms ihara_bass_of_connection
#print axioms gauge_connection
#print axioms gaugeDiag_mul_hashimotoC
#print axioms det_hashimotoC_gauge
#print axioms adjacencyC_gauge
#print axioms det_hashimotoC_loop
#print axioms det_fromBlocks_swap
#print axioms sign_connection
#print axioms swap_eq_of_sign
#print axioms artin_double_cover
#print axioms artin_double_cover_of_sign
#print axioms hashimoto_cover
#print axioms artin_double_cover_hashimoto

end Audit

end Holonics.Landmarks.IharaBassConnection
