import HolonicsResearch.Landmarks.IharaBassConnection

/-!
# Ihara–Bass with a matrix connection: a dart determinant of non-commuting steps is a cell one

`Landmarks/IharaBass` proves Bass's determinant identity for the dart operator of a finite complex
of contacts, and `Landmarks/IharaBassConnection` carries one unit of a commutative ring on every
dart.  This owner carries one invertible `n × n` matrix on every dart, the reversed dart holding
its inverse: `G : E ⊕ E → Matrix n n R` with `G d * G d.swap = 1`, over every commutative ring
`R`.  The model is the plain file's (cells `V`, contacts `E`, ends `a b : E → V`, darts `E ⊕ E`,
reversal `Sum.swap`; loops and parallel contacts allowed).  Every operator is a matrix over `R` on
the block indices `V × n` and `(E ⊕ E) × n`, and nothing is divided.  The case `n = Fin 2` is a
carry step that reflects as well as turns (`HNN/PumpedCarry`).

Sources: `Landmarks/IharaBass` and `Landmarks/IharaBassConnection` (atlas
`trace.ihara-bass-determinant`, `trace.ihara-bass-connection`), `Landmarks/IharaAbelianCover`
(atlas `trace.abelian-cover-artin`); an outside reader's reply of November 19 (its blueprint for
this module); the record of the first Lean pass of November 19 (§7.2, item 3: the machine's own
zeta with a factor of rank two); Bass (1992) and Stark–Terras (the L-functions of a
representation).

**What is proved.**

1. [definition] `blk` (the matrix on `X × n` whose `(x, y)` block is `M x y`), with its laws
   `blk_mul`, `blk_add`, `blk_sub`, `blk_smul`, `blk_one`, `blk_transpose`.
2. [proved-derived; formal-checked] `bass_block_abstract` and `bass_det_abstract`: for matrices
   `S T : X × Y` and `J : Y × Y` over a commutative ring with `J J = 1` and `S J = T`, Bass's block
   identity and `(1 − u²)^|X| · det (1 − u (Tᵀ S − J)) = det (1 − u S Tᵀ + u² (T Tᵀ − 1)) ·
   det (1 + u J)`.  The abelian files' argument needs nothing else.
3. [definition] `startMatrixM` `S̃` (block `G d` at `(v, d)` when `d` leaves `v`), `endMatrixM` `T̃`
   (block `1` when `d` enters `v`), `reversalM` `J̃` (block `G f` when `f` is `d` reversed),
   `hashimotoM` `B_G` (block `G f` when `f` leaves the cell `d` enters and is not `d` reversed;
   `hashimotoM_apply` is the entry form, `hashimotoC`'s pattern at `n = Unit`) and `adjacencyM`
   `A_G = S̃ T̃ᵀ` (`adjacencyM_apply`: `A_G (v, i) (w, j) = ∑ G d i j` over the darts from `v` to
   `w`).
4. [proved-derived; formal-checked] the tilde laws, from `G d * G d.swap = 1` alone:
   `reversalM_mul_reversalM` (`J̃ J̃ = 1`), `startMatrixM_mul_reversalM` (`S̃ J̃ = T̃`),
   `endMatrixM_transpose_mul_startMatrixM` (`T̃ᵀ S̃ = B_G + J̃`), `hashimotoM_eq`,
   `endMatrixM_mul_transpose` (`T̃ T̃ᵀ = D ⊗ 1`), `kronecker_degree_sub_one`,
   `one_add_smul_reversalM_reindex` and `det_one_add_smul_reversalM`
   (`det (1 + u J̃) = (1 − u²)^(|E| |n|)`).
5. [proved-derived; formal-checked] **`ihara_bass_matrix`**:
   `(1 − u²)^(|V| |n|) · det (1 − u B_G) = det (1 − u A_G + u² ((D − 1) ⊗ 1)) · (1 − u²)^(|E| |n|)`
   for every matrix connection and every `u` in every commutative ring.  The exponents are written
   `Fintype.card V * Fintype.card n` and `Fintype.card E * Fintype.card n`, and the Kronecker factor
   is Mathlib's `⊗ₖ`.
6. [proved-derived; formal-checked] the trivial connection (the dart side only):
   `hashimotoM_one` (`B_1 = B ⊗ 1`) and `det_one_sub_smul_hashimotoM_one`
   (`det (1 − u B_1) = det (1 − u B)^|n|`).
7. [proved-derived; formal-checked] the gauge: `gaugeM`
   (`G' d = H (src d) * G d * Hinv (tgt d)`) and `gaugeDiagM` ([definition]); `gaugeM_connection`,
   `gaugeDiagM_mul_hashimotoM`
   (`Δ B_G = B_{G'} Δ`), `gaugeDiagM_mul_gaugeDiagM` and **`det_hashimotoM_gauge`**:
   `det (1 − u B_{G'}) = det (1 − u B_G)`.
8. [proved-derived; formal-checked] the closed chain: **`det_hashimotoM_loop`**, one cell and
   one contact that is a loop, `det (1 − u B_G) = det (1 − u G⁺) · det (1 − u G⁻)`, and
   `det_hashimotoM_loop_holonomy` with the two transports `H`, `Hinv` named.  Neither uses
   `H * Hinv = 1`, so they are stated without it.
9. [proved-standard; formal-checked] `det_one_sub_smul_two`: for `H : Matrix (Fin 2) (Fin 2) R`,
   `det (1 − u H) = 1 − tr H · u + det H · u²`; and [proved-derived; formal-checked]
   `det_hashimotoM_loop_two`: the loop with `2 × 2` transports reads
   `(1 − tr H · u + det H · u²) · (1 − tr Hinv · u + det Hinv · u²)`, the factor `1 − a T + b T²`
   of `Geometry/CellPassBand.scaled_factor` and of a prime of a curve (`Landmarks/HasseBand`).
   When the holonomy has determinant one and the reversed dart carries its inverse, the two
   directions of the walk give one factor and the loop reads its square,
   `(1 − tr H · u + u²)²` (`det_hashimotoM_loop_two_det_one`).

[interpretation] The identity needs the reversed dart to carry the inverse.  It is the determinant
form of a transport that can be walked both ways; a transport whose contacts carry one way has the
dart operator and its determinant but no cell-side form.  A closed chain with a `2 × 2` holonomy
contributes a quadratic factor, the shape of a prime's factor on a curve, where the abelian chain
contributes a linear one: the degree of the factor is the size of the step.

**Limits.**  No Euler product over primitive closed walks is proved.  No Artin factorization for a
non-abelian cover is stated (the `D₃` cover's `ζ_Y = ζ_X · L(sign) · L(std)²` needs the induced
representation's block form).  The converse of the gauge theorem (two connections with equal
holonomies differ by a gauge) is not stated.  The scalar case `n = Unit` is not reindexed onto
`ihara_bass_connection`, and at `G = 1` only the dart side is read.  Nothing spectral is said, and
nothing about an engine's transport, which is read by a ruler.

Computational object: the helical pair interaction; this module touches the pair (a dart and its
reversal), the cell holonomy (the closed chain's product) and the tower thread; the helix, the
faces and placement, and the tube stay attached.

**Consumers.**  The atlas row `trace.ihara-bass-matrix`.

No `sorry`, no `axiom`, no `native_decide`.
-/

open Matrix
open scoped Kronecker

namespace Holonics.Landmarks.IharaBassMatrix

open Holonics.Landmarks.IharaBass

/-! ## Block matrices -/

section Blocks

variable {n : Type*} {R : Type*}

/-- [definition] The matrix on `X × n` by `Y × n` whose `(x, y)` block is `M x y`. -/
def blk {X Y : Type*} (M : X → Y → Matrix n n R) : Matrix (X × n) (Y × n) R :=
  Matrix.of fun p q => M p.1 q.1 p.2 q.2

/-- [definition] The entry of a block matrix, by definition. -/
@[simp] theorem blk_apply {X Y : Type*} (M : X → Y → Matrix n n R) (p : X × n) (q : Y × n) :
    blk M p q = M p.1 q.1 p.2 q.2 := rfl

/-- [proved-derived; formal-checked] Blocks multiply as matrices with matrix entries: the `(x, z)`
block of a product is `∑ y, M x y * N y z`. -/
theorem blk_mul [Fintype n] [CommRing R] {X Y Z : Type*} [Fintype Y] (M : X → Y → Matrix n n R)
    (N : Y → Z → Matrix n n R) :
    blk M * blk N = blk fun x z => ∑ y, M x y * N y z := by
  ext ⟨x, i⟩ ⟨z, j⟩
  simp only [Matrix.mul_apply, blk_apply, Fintype.sum_prod_type, Matrix.sum_apply]

/-- [proved-derived; formal-checked] Blocks subtract blockwise. -/
theorem blk_sub [CommRing R] {X Y : Type*} (M N : X → Y → Matrix n n R) :
    blk M - blk N = blk fun x y => M x y - N x y := by
  ext ⟨x, i⟩ ⟨y, j⟩
  simp

/-- [proved-derived; formal-checked] Blocks add blockwise. -/
theorem blk_add [CommRing R] {X Y : Type*} (M N : X → Y → Matrix n n R) :
    blk M + blk N = blk fun x y => M x y + N x y := by
  ext ⟨x, i⟩ ⟨y, j⟩
  simp

/-- [proved-derived; formal-checked] A scalar multiplies every block. -/
theorem blk_smul [CommRing R] {X Y : Type*} (u : R) (M : X → Y → Matrix n n R) :
    u • blk M = blk fun x y => u • M x y := by
  ext ⟨x, i⟩ ⟨y, j⟩
  simp

/-- [proved-derived; formal-checked] The identity on `X × n` has the identity block on the diagonal
and zero elsewhere. -/
theorem blk_one [DecidableEq n] [CommRing R] {X : Type*} [DecidableEq X] :
    (1 : Matrix (X × n) (X × n) R) = blk fun x y => if x = y then 1 else 0 := by
  ext ⟨x, i⟩ ⟨y, j⟩
  by_cases h : x = y
  · subst h; simp [Matrix.one_apply]
  · simp [h]

/-- [proved-derived; formal-checked] The transpose transposes the block pattern and every block. -/
theorem blk_transpose {X Y : Type*} (M : X → Y → Matrix n n R) :
    (blk M)ᵀ = blk fun y x => (M x y)ᵀ := by
  ext ⟨y, i⟩ ⟨x, j⟩
  rfl

end Blocks

/-! ## The abstract block identity -/

section Abstract

variable {R : Type*} [CommRing R] {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X]
  [DecidableEq Y]

/-- [proved-derived; formal-checked] Bass's block identity on `X ⊕ Y` from two relations,
`J J = 1` and `S J = T`.  It divides by nothing. -/
theorem bass_block_abstract (S T : Matrix X Y R) (J : Matrix Y Y R) (hJ : J * J = 1)
    (hSJ : S * J = T) (u : R) :
    Matrix.fromBlocks (1 : Matrix X X R) 0 Tᵀ 1 *
        Matrix.fromBlocks ((1 - u ^ 2) • (1 : Matrix X X R)) (u • S) 0
          (1 - u • (Tᵀ * S - J)) =
      Matrix.fromBlocks (1 - u • (S * Tᵀ) + u ^ 2 • (T * Tᵀ - 1)) (u • S) 0 (1 + u • J) *
        Matrix.fromBlocks 1 0 (Tᵀ - u • (J * Tᵀ)) 1 := by
  have hSJT : S * (J * Tᵀ) = T * Tᵀ := by rw [← Matrix.mul_assoc, hSJ]
  have hJJT : J * (J * Tᵀ) = Tᵀ := by rw [← Matrix.mul_assoc, hJ, Matrix.one_mul]
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  congr 1
  · simp only [Matrix.mul_one, Matrix.zero_mul, add_zero, Matrix.mul_sub,
      Matrix.smul_mul, Matrix.mul_smul, hSJT]
    module
  · simp only [Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, add_zero,
      zero_add]
  · simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, add_zero,
      zero_add, Matrix.mul_sub, Matrix.add_mul, Matrix.smul_mul, Matrix.mul_smul, hJJT]
    module
  · simp only [Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, zero_add,
      Matrix.mul_smul, Matrix.mul_sub]
    module

/-- [proved-derived; formal-checked] The determinant form of the abstract identity:
`(1 − u²)^|X| · det (1 − u (Tᵀ S − J)) = det (1 − u S Tᵀ + u² (T Tᵀ − 1)) · det (1 + u J)`. -/
theorem bass_det_abstract (S T : Matrix X Y R) (J : Matrix Y Y R) (hJ : J * J = 1)
    (hSJ : S * J = T) (u : R) :
    (1 - u ^ 2) ^ Fintype.card X * (1 - u • (Tᵀ * S - J)).det =
      (1 - u • (S * Tᵀ) + u ^ 2 • (T * Tᵀ - 1)).det * (1 + u • J).det := by
  have h := congrArg Matrix.det (bass_block_abstract S T J hJ hSJ u)
  simp only [Matrix.det_mul, Matrix.det_fromBlocks_zero₁₂, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_one, Matrix.det_smul, one_mul, mul_one] at h
  exact h

end Abstract

/-! ## The operators with a matrix transport -/

section Operators

variable {V E n : Type*} [DecidableEq V] [DecidableEq E] [Fintype n] [DecidableEq n]
variable {R : Type*} [CommRing R] (a b : E → V) (G : E ⊕ E → Matrix n n R)

/-- [definition] The start incidence with the transport: block `G d` at `(v, d)` when `d` leaves
`v`. -/
def startMatrixM : Matrix (V × n) ((E ⊕ E) × n) R :=
  blk fun v d => if src a b d = v then G d else 0

variable (n R) in
/-- [definition] The end incidence tensored with the identity: block `1` at `(v, d)` when `d`
enters `v`. -/
def endMatrixM : Matrix (V × n) ((E ⊕ E) × n) R :=
  blk fun v d => if tgt a b d = v then 1 else 0

/-- [definition] The reversal with the transport: block `G f` at `(d, f)` when `f` is `d`
reversed. -/
def reversalM : Matrix ((E ⊕ E) × n) ((E ⊕ E) × n) R :=
  blk fun d f => if f = d.swap then G f else 0

/-- [definition] The dart operator with a matrix transport: block `G f` at `(d, f)` when `f` leaves
the cell `d` enters and `f` is not `d` reversed. -/
def hashimotoM : Matrix ((E ⊕ E) × n) ((E ⊕ E) × n) R :=
  blk fun d f => if tgt a b d = src a b f ∧ f ≠ d.swap then G f else 0

omit [Fintype n] [DecidableEq n] in
/-- [proved-derived; formal-checked] The entry form of the dart operator: `B_G (d, i) (f, j) = G f i
j` when `f` leaves the cell `d` enters and is not `d` reversed, else `0` (at `n = Unit` this is
`hashimotoC`'s pattern). -/
theorem hashimotoM_apply (d f : E ⊕ E) (i j : n) :
    hashimotoM a b G (d, i) (f, j) =
      if tgt a b d = src a b f ∧ f ≠ d.swap then G f i j else 0 := by
  simp only [hashimotoM, blk_apply]
  split_ifs <;> rfl

variable [Fintype V] [Fintype E]

/-- [definition] The cell operator with a matrix transport, `A_G = S_G Tᵀ`. -/
def adjacencyM : Matrix (V × n) (V × n) R := startMatrixM a b G * (endMatrixM n R a b)ᵀ

omit [DecidableEq E] [Fintype V] in
/-- [proved-derived; formal-checked] `A_G (v, i) (w, j)` is the sum over the darts from `v` to `w`
of `G d i j`. -/
theorem adjacencyM_apply (v w : V) (i j : n) :
    adjacencyM a b G (v, i) (w, j) =
      ∑ d : E ⊕ E, if src a b d = v ∧ tgt a b d = w then G d i j else 0 := by
  rw [adjacencyM, endMatrixM, blk_transpose, startMatrixM, blk_mul, blk_apply, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun d _ => ?_
  by_cases hv : src a b d = v
  · by_cases hw : tgt a b d = w
    · simp [hv, hw]
    · simp [hv, hw]
  · simp [hv]

/-- [proved-derived; formal-checked] `J̃ J̃ = 1`: a dart's transport followed by its reversal's is
`G d.swap * G d = 1`. -/
theorem reversalM_mul_reversalM (hG : ∀ d, G d * G d.swap = 1) :
    reversalM G * reversalM G = 1 := by
  rw [reversalM, blk_mul, blk_one]
  congr 1
  funext d f
  simp only [ite_mul, mul_ite, zero_mul, mul_zero]
  rw [Finset.sum_eq_single d.swap]
  · simp only [Sum.swap_swap, ↓reduceIte]
    by_cases h : d = f
    · subst h
      have := hG d.swap
      rw [Sum.swap_swap] at this
      rw [if_pos rfl, if_pos rfl, this]
    · rw [if_neg (Ne.symm h), if_neg h]
  · intro e _ he
    simp [he]
  · simp

omit [Fintype V] in
/-- [proved-derived; formal-checked] `S̃ J̃ = T̃`: the start incidence with transports, followed by
the reversal with transports, is the plain end incidence tensored with `1`. -/
theorem startMatrixM_mul_reversalM (hG : ∀ d, G d * G d.swap = 1) :
    startMatrixM a b G * reversalM G = endMatrixM n R a b := by
  rw [startMatrixM, reversalM, endMatrixM, blk_mul]
  congr 1
  funext v f
  simp only [ite_mul, mul_ite, zero_mul, mul_zero]
  rw [Finset.sum_eq_single f.swap]
  · have := hG f.swap
    rw [Sum.swap_swap] at this
    simp only [Sum.swap_swap, if_true, src_swap, this]
  · intro e _ he
    have : ¬ f = e.swap := fun h => he (by rw [h, Sum.swap_swap])
    simp [this]
  · simp

omit [Fintype E] in
/-- [proved-derived; formal-checked] `T̃ᵀ S̃ = B_G + J̃`: the darts leaving the cell `d` enters,
each with its block, are the non-backtracking continuations and the one reversal. -/
theorem endMatrixM_transpose_mul_startMatrixM :
    (endMatrixM n R a b)ᵀ * startMatrixM a b G = hashimotoM a b G + reversalM G := by
  rw [endMatrixM, blk_transpose, startMatrixM, blk_mul, hashimotoM, reversalM, blk_add]
  congr 1
  funext d f
  simp only [apply_ite Matrix.transpose, Matrix.transpose_one, Matrix.transpose_zero, ite_mul,
    one_mul, zero_mul]
  rw [Finset.sum_ite_eq Finset.univ (tgt a b d)]
  simp only [Finset.mem_univ, if_true]
  by_cases hf : f = d.swap
  · have hs : src a b f = tgt a b d := by rw [hf, src_swap]
    rw [if_pos hs, if_neg (fun h => h.2 hf), if_pos hf, zero_add]
  · by_cases ht : tgt a b d = src a b f
    · rw [if_pos ht.symm, if_pos ⟨ht, hf⟩, if_neg hf, add_zero]
    · rw [if_neg (fun h => ht h.symm), if_neg (fun h => ht h.1), if_neg hf, add_zero]

omit [Fintype V] in
/-- [proved-derived; formal-checked] `T̃ T̃ᵀ = D ⊗ 1`: no transport enters the degree. -/
theorem endMatrixM_mul_transpose :
    endMatrixM n R a b * (endMatrixM n R a b)ᵀ = degree R a b ⊗ₖ (1 : Matrix n n R) := by
  have hT : endMatrixM n R a b = endMatrix R a b ⊗ₖ (1 : Matrix n n R) := by
    ext ⟨v, i⟩ ⟨d, j⟩
    simp only [endMatrixM, blk_apply, Matrix.kronecker_apply, endMatrix_apply]
    split_ifs <;> simp
  rw [hT, ← Matrix.kroneckerMap_transpose, ← Matrix.mul_kronecker_mul, Matrix.transpose_one,
    Matrix.mul_one, degree_eq_end]

omit [Fintype n] [Fintype E] in
/-- [proved-derived; formal-checked] In the two halves of the darts, `1 + u J̃` is the block matrix
`[[1, u G⁻], [u G⁺, 1]]`, with `G⁻` and `G⁺` the block diagonals of the two halves' transports. -/
theorem one_add_smul_reversalM_reindex (u : R) :
    Matrix.reindex (Equiv.sumProdDistrib E E n) (Equiv.sumProdDistrib E E n)
        (1 + u • reversalM G) =
      Matrix.fromBlocks 1 (u • blk fun e e' : E => if e = e' then G (Sum.inr e) else 0)
        (u • blk fun e e' : E => if e = e' then G (Sum.inl e) else 0) 1 := by
  ext (⟨e, i⟩ | ⟨e, i⟩) (⟨f, j⟩ | ⟨f, j⟩)
  · simp [reversalM, Matrix.one_apply]
  · rcases eq_or_ne e f with rfl | h
    · simp [reversalM]
    · simp [reversalM, h, Ne.symm h]
  · rcases eq_or_ne e f with rfl | h
    · simp [reversalM]
    · simp [reversalM, h, Ne.symm h]
  · simp [reversalM, Matrix.one_apply]

/-- [proved-derived; formal-checked] `det (1 + u J̃) = (1 − u²)^(|E| |n|)`: each contact's pair
of darts gives the block `[[1, u G (inr e)], [u G (inl e), 1]]`, of determinant
`det ((1 − u²) · 1)`. -/
theorem det_one_add_smul_reversalM (hG : ∀ d, G d * G d.swap = 1) (u : R) :
    (1 + u • reversalM G).det = (1 - u ^ 2) ^ (Fintype.card E * Fintype.card n) := by
  rw [← Matrix.det_reindex_self (Equiv.sumProdDistrib E E n), one_add_smul_reversalM_reindex,
    Matrix.det_fromBlocks_one₁₁]
  have hQP : (blk fun e e' : E => if e = e' then G (Sum.inl e) else 0) *
      (blk fun e e' : E => if e = e' then G (Sum.inr e) else 0) =
        (1 : Matrix (E × n) (E × n) R) := by
    rw [blk_mul, blk_one]
    congr 1
    funext e e'
    simp only [ite_mul, mul_ite, zero_mul, mul_zero]
    rw [Finset.sum_eq_single e]
    · by_cases h : e = e'
      · subst h
        simp only [↓reduceIte]
        exact hG (Sum.inl e)
      · simp [h]
    · intro y _ hy
      simp [Ne.symm hy]
    · simp
  have h : (1 : Matrix (E × n) (E × n) R) -
      (u • blk fun e e' : E => if e = e' then G (Sum.inl e) else 0) *
        (u • blk fun e e' : E => if e = e' then G (Sum.inr e) else 0) =
      (1 - u ^ 2) • (1 : Matrix (E × n) (E × n) R) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, hQP, smul_smul, sub_smul, one_smul, pow_two]
  rw [h, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_prod]

omit [Fintype E] in
/-- [proved-derived; formal-checked] `B_G = T̃ᵀ S̃ − J̃`. -/
theorem hashimotoM_eq :
    hashimotoM a b G = (endMatrixM n R a b)ᵀ * startMatrixM a b G - reversalM G := by
  rw [endMatrixM_transpose_mul_startMatrixM, add_sub_cancel_right]

omit [DecidableEq E] [Fintype n] [Fintype V] in
/-- [proved-derived; formal-checked] `(D − 1) ⊗ 1 = D ⊗ 1 − 1`. -/
theorem kronecker_degree_sub_one :
    (degree R a b - 1) ⊗ₖ (1 : Matrix n n R) = degree R a b ⊗ₖ (1 : Matrix n n R) - 1 := by
  rw [eq_sub_iff_add_eq, ← Matrix.one_kronecker_one (α := R) (m := V) (n := n),
    ← Matrix.add_kronecker, sub_add_cancel]

/-- [proved-derived; formal-checked] **Ihara–Bass with a matrix connection.**  For every finite
multigraph, every transport `G` by `n × n` matrices with `G d * G d.swap = 1`, and every `u` in
every commutative ring,
`(1 − u²)^(|V| |n|) · det (1 − u B_G) = det (1 − u A_G + u² ((D − 1) ⊗ 1)) · (1 − u²)^(|E| |n|)`. -/
theorem ihara_bass_matrix (hG : ∀ d, G d * G d.swap = 1) (u : R) :
    (1 - u ^ 2) ^ (Fintype.card V * Fintype.card n) * (1 - u • hashimotoM a b G).det =
      (1 - u • adjacencyM a b G + u ^ 2 • ((degree R a b - 1) ⊗ₖ (1 : Matrix n n R))).det *
        (1 - u ^ 2) ^ (Fintype.card E * Fintype.card n) := by
  have h := bass_det_abstract (startMatrixM a b G) (endMatrixM n R a b) (reversalM G)
    (reversalM_mul_reversalM G hG) (startMatrixM_mul_reversalM a b G hG) u
  rw [← hashimotoM_eq, ← adjacencyM, endMatrixM_mul_transpose, det_one_add_smul_reversalM G hG,
    Fintype.card_prod, ← kronecker_degree_sub_one] at h
  exact h

/-! ## The trivial connection -/

omit [Fintype n] [Fintype V] [Fintype E] in
/-- [proved-derived; formal-checked] At the trivial connection `G = 1` the dart operator is
`B ⊗ 1`. -/
theorem hashimotoM_one :
    hashimotoM a b (fun _ => (1 : Matrix n n R)) = hashimoto R a b ⊗ₖ (1 : Matrix n n R) := by
  ext ⟨d, i⟩ ⟨f, j⟩
  rw [hashimotoM_apply, Matrix.kronecker_apply, hashimoto_apply]
  split_ifs <;> simp

omit [Fintype V] in
/-- [proved-derived; formal-checked] At `G = 1`, `det (1 − u B_G) = det (1 − u B)^|n|`
(`Matrix.det_kronecker`). -/
theorem det_one_sub_smul_hashimotoM_one (u : R) :
    (1 - u • hashimotoM a b (fun _ => (1 : Matrix n n R))).det =
      (1 - u • hashimoto R a b).det ^ Fintype.card n := by
  have h : 1 - u • hashimotoM a b (fun _ => (1 : Matrix n n R)) =
      (1 - u • hashimoto R a b) ⊗ₖ (1 : Matrix n n R) := by
    rw [hashimotoM_one]
    ext ⟨d, i⟩ ⟨f, j⟩
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.kronecker_apply, Matrix.one_apply,
      Prod.mk.injEq]
    by_cases hij : i = j <;> by_cases hdf : d = f <;> simp [hij, hdf]
  rw [h, Matrix.det_kronecker, Matrix.det_one, one_pow, mul_one]

/-! ## The gauge -/

section Gauge

variable (H Hinv : V → Matrix n n R)

/-- [definition] A change of frame at the cells: `G' d = H (src d) * G d * Hinv (tgt d)`. -/
def gaugeM : E ⊕ E → Matrix n n R := fun d => H (src a b d) * G d * Hinv (tgt a b d)

/-- [definition] The block diagonal of `H (tgt d)` on darts. -/
def gaugeDiagM : Matrix ((E ⊕ E) × n) ((E ⊕ E) × n) R :=
  blk fun d f => if d = f then H (tgt a b d) else 0

omit [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] in
/-- [proved-derived; formal-checked] A gauge of a matrix connection is a matrix connection (`Hinv v
* H v = 1` is read from `H v * Hinv v = 1` because the matrices are square). -/
theorem gaugeM_connection (hG : ∀ d, G d * G d.swap = 1) (hH : ∀ v, H v * Hinv v = 1)
    (d : E ⊕ E) : gaugeM a b G H Hinv d * gaugeM a b G H Hinv d.swap = 1 := by
  simp only [gaugeM, src_swap, tgt_swap]
  have h1 : Hinv (tgt a b d) * H (tgt a b d) = 1 := mul_eq_one_comm.mp (hH _)
  calc H (src a b d) * G d * Hinv (tgt a b d) * (H (tgt a b d) * G d.swap * Hinv (src a b d))
      = H (src a b d) * G d * (Hinv (tgt a b d) * H (tgt a b d)) * G d.swap *
          Hinv (src a b d) := by simp only [Matrix.mul_assoc]
    _ = H (src a b d) * (G d * G d.swap) * Hinv (src a b d) := by
        rw [h1, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hG, Matrix.mul_one, hH]

omit [Fintype V] in
/-- [proved-derived; formal-checked] `Δ B_G = B_{G'} Δ` with `Δ` the block diagonal of `H (tgt d)`:
the gauge conjugates the dart operator, on the same side as the abelian `gaugeDiag_mul_hashimotoC`.
-/
theorem gaugeDiagM_mul_hashimotoM (hH : ∀ v, H v * Hinv v = 1) :
    gaugeDiagM a b H * hashimotoM a b G =
      hashimotoM a b (gaugeM a b G H Hinv) * gaugeDiagM a b H := by
  rw [gaugeDiagM, hashimotoM, hashimotoM, blk_mul, blk_mul]
  congr 1
  funext d f
  rw [Finset.sum_eq_single d, Finset.sum_eq_single f]
  · simp only [↓reduceIte]
    split_ifs with hc
    · have h1 : Hinv (tgt a b f) * H (tgt a b f) = 1 := mul_eq_one_comm.mp (hH _)
      rw [gaugeM, hc.1, Matrix.mul_assoc _ (Hinv _), h1, Matrix.mul_one]
    · rw [Matrix.mul_zero, Matrix.zero_mul]
  · intro e _ he
    simp [he]
  · simp
  · intro e _ he
    simp [Ne.symm he]
  · simp

omit [DecidableEq V] [Fintype V] in
/-- [proved-derived; formal-checked] `Δ` is invertible, with inverse the block diagonal of `Hinv
(tgt d)`. -/
theorem gaugeDiagM_mul_gaugeDiagM (hH : ∀ v, H v * Hinv v = 1) :
    gaugeDiagM a b H * gaugeDiagM a b Hinv = 1 := by
  rw [gaugeDiagM, gaugeDiagM, blk_mul, blk_one]
  congr 1
  funext d f
  rw [Finset.sum_eq_single d]
  · by_cases h : d = f
    · subst h
      simp only [↓reduceIte]
      exact hH _
    · simp [h]
  · intro e _ he
    simp [Ne.symm he]
  · simp

omit [Fintype V] in
/-- [proved-derived; formal-checked] **The gauge leaves the determinant.**  For frames `H` at the
cells with right inverses `Hinv`, `det (1 − u B_{G'}) = det (1 − u B_G)`. -/
theorem det_hashimotoM_gauge (hH : ∀ v, H v * Hinv v = 1) (u : R) :
    (1 - u • hashimotoM a b (gaugeM a b G H Hinv)).det = (1 - u • hashimotoM a b G).det := by
  have h1 : gaugeDiagM a b H * (1 - u • hashimotoM a b G) =
      (1 - u • hashimotoM a b (gaugeM a b G H Hinv)) * gaugeDiagM a b H := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_smul,
      Matrix.smul_mul, gaugeDiagM_mul_hashimotoM a b G H Hinv hH]
  have hdet : (gaugeDiagM a b H).det * (gaugeDiagM a b Hinv).det = 1 := by
    rw [← Matrix.det_mul, gaugeDiagM_mul_gaugeDiagM a b H Hinv hH, Matrix.det_one]
  have h2 := congrArg Matrix.det h1
  rw [Matrix.det_mul, Matrix.det_mul] at h2
  calc (1 - u • hashimotoM a b (gaugeM a b G H Hinv)).det
      = (1 - u • hashimotoM a b (gaugeM a b G H Hinv)).det *
          ((gaugeDiagM a b H).det * (gaugeDiagM a b Hinv).det) := by rw [hdet, mul_one]
    _ = ((1 - u • hashimotoM a b (gaugeM a b G H Hinv)).det * (gaugeDiagM a b H).det) *
          (gaugeDiagM a b Hinv).det := by ring
    _ = ((gaugeDiagM a b H).det * (1 - u • hashimotoM a b G).det) *
          (gaugeDiagM a b Hinv).det := by rw [← h2]
    _ = (1 - u • hashimotoM a b G).det *
          ((gaugeDiagM a b H).det * (gaugeDiagM a b Hinv).det) := by ring
    _ = (1 - u • hashimotoM a b G).det := by rw [hdet, mul_one]

end Gauge

end Operators

/-! ## A closed chain of one contact -/

section Loop

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]

/-- [definition] The darts of one loop, with blocks in `n`, as the two halves `n ⊕ n`. -/
def loopEquiv (n : Type*) : (Unit ⊕ Unit) × n ≃ n ⊕ n :=
  (Equiv.sumProdDistrib Unit Unit n).trans
    (Equiv.sumCongr (Equiv.uniqueProd n Unit) (Equiv.uniqueProd n Unit))

/-- [proved-derived; formal-checked] One cell and one contact that is a loop.  A dart is followed by
itself and never by its reversal, so the dart operator is block diagonal and
`det (1 − u B_G) = det (1 − u G⁺) · det (1 − u G⁻)`: each sense of the one closed walk is read
with its own matrix holonomy. -/
theorem det_hashimotoM_loop (G : Unit ⊕ Unit → Matrix n n R) (u : R) :
    (1 - u • hashimotoM (fun _ : Unit => ()) (fun _ : Unit => ()) G).det =
      (1 - u • G (Sum.inl ())).det * (1 - u • G (Sum.inr ())).det := by
  have h : Matrix.reindex (loopEquiv n) (loopEquiv n)
      (1 - u • hashimotoM (fun _ : Unit => ()) (fun _ : Unit => ()) G) =
      Matrix.fromBlocks (1 - u • G (Sum.inl ())) 0 0 (1 - u • G (Sum.inr ())) := by
    ext (i | i) (j | j) <;>
      simp [loopEquiv, hashimotoM, Matrix.one_apply, Equiv.uniqueProd]
  rw [← Matrix.det_reindex_self (loopEquiv n), h, Matrix.det_fromBlocks_zero₁₂]

/-- [proved-derived; formal-checked] The closed chain with its two transports named: `det (1 − u B)
= det (1 − u H) · det (1 − u Hinv)`.  No relation between `H` and `Hinv` is used. -/
theorem det_hashimotoM_loop_holonomy (H Hinv : Matrix n n R) (u : R) :
    (1 - u • hashimotoM (fun _ : Unit => ()) (fun _ : Unit => ())
        (Sum.elim (fun _ => H) (fun _ => Hinv))).det =
      (1 - u • H).det * (1 - u • Hinv).det :=
  det_hashimotoM_loop _ u

end Loop

/-! ## A step of size two -/

section Two

variable {R : Type*} [CommRing R]

/-- [proved-standard; formal-checked] For a `2 × 2` matrix, `det (1 − u H) = 1 − tr H · u + det H ·
u²`. -/
theorem det_one_sub_smul_two (H : Matrix (Fin 2) (Fin 2) R) (u : R) :
    (1 - u • H).det = 1 - H.trace * u + H.det * u ^ 2 := by
  rw [Matrix.det_fin_two, Matrix.det_fin_two, Matrix.trace_fin_two]
  simp
  ring

/-- [proved-derived; formal-checked] The loop with `2 × 2` transports contributes two quadratic
factors: `(1 − tr H · u + det H · u²) · (1 − tr Hinv · u + det Hinv · u²)`. -/
theorem det_hashimotoM_loop_two (H Hinv : Matrix (Fin 2) (Fin 2) R) (u : R) :
    (1 - u • hashimotoM (fun _ : Unit => ()) (fun _ : Unit => ())
        (Sum.elim (fun _ => H) (fun _ => Hinv))).det =
      (1 - H.trace * u + H.det * u ^ 2) * (1 - Hinv.trace * u + Hinv.det * u ^ 2) := by
  rw [det_hashimotoM_loop_holonomy, det_one_sub_smul_two, det_one_sub_smul_two]

/-- [proved-derived; formal-checked] **A loop whose `2 × 2` holonomy has determinant one reads the
square of one quadratic factor.**  With the reversed dart carrying the inverse, the two directions
of the walk give the same factor `1 − tr H · u + u²`, the cell's. -/
theorem det_hashimotoM_loop_two_det_one (H Hinv : Matrix (Fin 2) (Fin 2) R) (hH : H * Hinv = 1)
    (hdet : H.det = 1) (u : R) :
    (1 - u • hashimotoM (fun _ : Unit => ()) (fun _ : Unit => ())
        (Sum.elim (fun _ => H) (fun _ => Hinv))).det =
      (1 - H.trace * u + u ^ 2) ^ 2 := by
  have hinv : Hinv = H.adjugate := by
    have h1 : H.adjugate * H = 1 := by rw [Matrix.adjugate_mul, hdet, one_smul]
    calc Hinv = (H.adjugate * H) * Hinv := by rw [h1, one_mul]
      _ = H.adjugate * (H * Hinv) := by rw [Matrix.mul_assoc]
      _ = H.adjugate := by rw [hH, mul_one]
  have htr : Hinv.trace = H.trace := by
    rw [hinv, Matrix.adjugate_fin_two, Matrix.trace_fin_two, Matrix.trace_fin_two]
    simp [add_comm]
  have hd : Hinv.det = 1 := by
    have h2 := congrArg Matrix.det hH
    rw [Matrix.det_mul, hdet, one_mul, Matrix.det_one] at h2
    exact h2
  rw [det_hashimotoM_loop_two, htr, hd, hdet]
  ring

end Two

section Audit

#print axioms bass_det_abstract
#print axioms reversalM_mul_reversalM
#print axioms startMatrixM_mul_reversalM
#print axioms endMatrixM_transpose_mul_startMatrixM
#print axioms det_one_add_smul_reversalM
#print axioms ihara_bass_matrix
#print axioms det_one_sub_smul_hashimotoM_one
#print axioms gaugeM_connection
#print axioms det_hashimotoM_gauge
#print axioms det_hashimotoM_loop
#print axioms det_one_sub_smul_two
#print axioms det_hashimotoM_loop_two
#print axioms det_hashimotoM_loop_two_det_one

end Audit

end Holonics.Landmarks.IharaBassMatrix
