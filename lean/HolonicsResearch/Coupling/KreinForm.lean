import Mathlib

/-!
# The half from a reversal: the reversal's own form, the similitude criterion and the cell

[definition] A move `B` on a space with a pairing `ω` is a **similitude by `q`** when
`ω (B x) (B y) = q · ω x y`.  The **reversal's own form** of the pair `(ω, B)` is

  `krein ω B x y = ω x (B y) + ω y (B x)`,

the symmetric part of `ω (·, B ·)`.  Nothing is chosen in it: the pairing and the move are its only
operands.  For an alternating `ω` its diagonal is `2 · ω x (B x)`, the pairing of a state with its
own image.

[proved-derived; formal-checked] What is proved here.

1. **The reversal gives a scaled form** (`krein_symm`, `krein_similitude`, `kreinPow_similitude`).
   Over any commutative ring, a similitude `B` of `ω` by `q` is a similitude by `q` of `krein ω B`,
   and of every member `ω x (Bᵏ y) + ω y (Bᵏ x)` of the pencil.  No positivity enters.
2. **The half** (`normSq_eigenvalue_of_similitude`, `norm_sq_iterate_of_similitude`,
   `no_jordan_block_of_similitude`, `pow_ker_of_similitude`).  On a complex inner product space a
   similitude by `q` has every mode at `|α|² = q`, carries `‖Bⁿ x‖² = qⁿ ‖x‖²`, and has no Jordan
   block at a mode on the circle: `(B − α)² x = 0` gives `(B − α) x = 0`.
3. **The indefinite reading** (`mode_off_circle_is_null`, `normSq_eigenvalue_of_posDef`).  For any
   complex matrix `G` with `Mᴴ G M = q G` and any mode `M v = α v`:
   `(|α|² − q) · (v† G v) = 0`.  A mode off the circle is a null vector of the scaled form, and a
   positive definite form leaves no null vector, so every mode sits at the half.
4. **Real moves, complex modes** (`normSq_eigenvalue_of_real_posDef`).  A real matrix `M` with
   `Mᵀ G M = q G` for a real positive definite `G` has every complex mode at `|α|² = q`.
5. **The converse** (`certificate_of_diagonalizable`).  A diagonalizable move whose modes all have
   `|d i|² = q` carries the certificate `G = (P⁻¹)ᴴ P⁻¹`: positive definite, with `Mᴴ G M = q G`.
6. **The cell** (`cell_det`, `cell_area_similitude`, `area_cell`, `normForm_similitude`,
   `normForm_pos_iff`, `normForm_null_of_eq`, `normForm_neg_of_lt`, `normForm_posDef_iff`,
   `cell_modes_on_circle`).  The companion cell `[[0, −1], [q, l]]` of `x² − l x + q` is an area
   similitude by its determinant `q`; the reversal's form of the area pairing and the cell is twice
   the norm form `q a² + l a b + b²` (`normForm_eq_symm_part`); that form is scaled by `q` under
   the cell for every `l`; it is
   positive definite iff `l² < 4 q`, has a null vector at `l² = 4 q` and a negative direction at
   `4 q < l²`.  So at `l² < 4 q` every complex mode of the cell has `|α|² = q`.

[interpretation] On the objects: the pairing `ω` is the reversal a functional equation supplies
(`α ↦ q / α`), the move is the step of scale, and the form whose definiteness places the modes is
read off the two (`key.scaled-form-places-modes`).  The cell's three cases are the Swing's three
kinds: a turn (`l² < 4 q`, a definite norm), a shear (`l² = 4 q`, a null direction) and a boost
(`4 q < l²`, an indefinite norm).

**What this does not state.**  Definiteness of the reversal's form is sufficient for the half and
is not necessary: modes of mixed Krein signature sit on the circle while `krein ω B` is indefinite
(two turns of opposite hand against one area pairing), and item 5's certificate is then a different
form.  Item 5 assumes the diagonalization; no spectral theorem is used to produce it.  Nothing here
constructs a pairing or a move for a zeta function; the statements are finite linear algebra.

Every `theorem` is discharged and none depends on `sorryAx`.
-/

noncomputable section

namespace Holonics.Coupling.KreinForm

open Matrix
open scoped ComplexConjugate ComplexOrder

/-! ## 1. The reversal's own form -/

section Reversal

variable {K : Type*} [CommRing K] {W : Type*} [AddCommGroup W] [Module K W]

/-- [definition] The reversal's own form of a pairing `ω` and a move `B`: the symmetric part of
`ω (·, B ·)`, as a bilinear map. -/
def krein (ω : W →ₗ[K] W →ₗ[K] K) (B : W →ₗ[K] W) : W →ₗ[K] W →ₗ[K] K :=
  ω.compl₂ B + (ω.compl₂ B).flip

@[simp]
theorem krein_apply (ω : W →ₗ[K] W →ₗ[K] K) (B : W →ₗ[K] W) (x y : W) :
    krein ω B x y = ω x (B y) + ω y (B x) := by
  simp [krein]

/-- [proved-derived; formal-checked] The reversal's form is symmetric. -/
theorem krein_symm (ω : W →ₗ[K] W →ₗ[K] K) (B : W →ₗ[K] W) (x y : W) :
    krein ω B x y = krein ω B y x := by
  simp only [krein_apply]
  ring

/-- [proved-derived; formal-checked] A similitude of the pairing by `q` is a similitude by `q` of
the reversal's own form.  No positivity and no alternation is used. -/
theorem krein_similitude {ω : W →ₗ[K] W →ₗ[K] K} {B : W →ₗ[K] W} {q : K}
    (hsim : ∀ x y, ω (B x) (B y) = q * ω x y) (x y : W) :
    krein ω B (B x) (B y) = q * krein ω B x y := by
  simp only [krein_apply, hsim]
  ring

/-- [proved-derived; formal-checked] For an alternating pairing the form's diagonal is twice the
pairing of a state with its own image. -/
theorem krein_self {ω : W →ₗ[K] W →ₗ[K] K} (B : W →ₗ[K] W) (x : W) :
    krein ω B x x = 2 * ω x (B x) := by
  simp only [krein_apply]
  ring

/-- [definition] The pencil of the reversal: the symmetric part of `ω (·, Bᵏ ·)`. -/
def kreinPow (ω : W →ₗ[K] W →ₗ[K] K) (B : W →ₗ[K] W) (k : ℕ) : W →ₗ[K] W →ₗ[K] K :=
  krein ω (B ^ k)

/-- [proved-derived; formal-checked] Every member of the pencil is scaled by `q` under the move. -/
theorem kreinPow_similitude {ω : W →ₗ[K] W →ₗ[K] K} {B : W →ₗ[K] W} {q : K}
    (hsim : ∀ x y, ω (B x) (B y) = q * ω x y) (k : ℕ) (x y : W) :
    kreinPow ω B k (B x) (B y) = q * kreinPow ω B k x y := by
  have hcomm : ∀ z : W, (B ^ k) (B z) = B ((B ^ k) z) := fun z => by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← pow_succ, ← pow_succ']
  simp only [kreinPow, krein_apply, hcomm, hsim]
  ring

/-- [proved-derived; formal-checked] The pencil at `k = 0` is twice the symmetric part of the
pairing, so it vanishes for an alternating pairing: the first form the reversal gives is at
`k = 1`. -/
theorem kreinPow_zero_of_alternating {ω : W →ₗ[K] W →ₗ[K] K}
    (halt : ∀ x y, ω x y = -ω y x) (B : W →ₗ[K] W) (x y : W) :
    kreinPow ω B 0 x y = 0 := by
  simp only [kreinPow, krein_apply, pow_zero, Module.End.one_apply]
  rw [halt x y]
  ring

end Reversal

/-! ## 2. The half on a complex inner product space -/

section Half

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- [proved-derived; formal-checked] The half: every mode of a similitude by `q` of a positive
pairing has `|α|² = q`. -/
theorem normSq_eigenvalue_of_similitude (B : E →ₗ[ℂ] E) (q : ℝ)
    (hB : ∀ x y, inner ℂ (B x) (B y) = (q : ℂ) * inner ℂ x y)
    {α : ℂ} {v : E} (hv : v ≠ 0) (hBv : B v = α • v) : Complex.normSq α = q := by
  have h := hB v v
  rw [hBv, inner_smul_left, inner_smul_right, ← mul_assoc] at h
  have hvv : (inner ℂ v v : ℂ) ≠ 0 := fun h0 => hv (inner_self_eq_zero.mp h0)
  have h2 : conj α * α = (q : ℂ) := mul_right_cancel₀ hvv h
  rw [← Complex.normSq_eq_conj_mul_self] at h2
  exact_mod_cast h2

/-- [proved-derived; formal-checked] One step scales the squared norm by `q`. -/
theorem norm_sq_apply_of_similitude (B : E →ₗ[ℂ] E) (q : ℝ)
    (hB : ∀ x y, inner ℂ (B x) (B y) = (q : ℂ) * inner ℂ x y) (x : E) :
    ‖B x‖ ^ 2 = q * ‖x‖ ^ 2 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ) (B x), norm_sq_eq_re_inner (𝕜 := ℂ) x, hB x x]
  simp

/-- [proved-derived; formal-checked] `n` steps scale the squared norm by `qⁿ`: the growth is the
count's square root at every length, with no polynomial factor. -/
theorem norm_sq_iterate_of_similitude (B : E →ₗ[ℂ] E) (q : ℝ)
    (hB : ∀ x y, inner ℂ (B x) (B y) = (q : ℂ) * inner ℂ x y) (n : ℕ) (x : E) :
    ‖(B ^ n) x‖ ^ 2 = q ^ n * ‖x‖ ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hstep : (B ^ (n + 1)) x = B ((B ^ n) x) := by
      rw [pow_succ', Module.End.mul_apply]
    rw [hstep, norm_sq_apply_of_similitude B q hB, ih]
    ring

/-- [definition] The move less a mode: `B − α`. -/
def shift (B : E →ₗ[ℂ] E) (α : ℂ) : E →ₗ[ℂ] E := B - α • LinearMap.id

@[simp]
theorem shift_apply (B : E →ₗ[ℂ] E) (α : ℂ) (x : E) : shift B α x = B x - α • x := by
  simp [shift]

/-- [proved-derived; formal-checked] No Jordan block at a mode on the circle: for a similitude by
`q ≠ 0` and `|α|² = q`, `(B − α)² x = 0` gives `(B − α) x = 0`. -/
theorem no_jordan_block_of_similitude (B : E →ₗ[ℂ] E) (q : ℝ)
    (hB : ∀ x y, inner ℂ (B x) (B y) = (q : ℂ) * inner ℂ x y) (hq : q ≠ 0)
    {α : ℂ} (hα : Complex.normSq α = q) {x : E}
    (hx : shift B α (shift B α x) = 0) : shift B α x = 0 := by
  have hBy : B (shift B α x) = α • shift B α x := by
    have h0 : B (shift B α x) - α • shift B α x = 0 := by
      rw [← shift_apply]
      exact hx
    exact sub_eq_zero.mp h0
  have hαα : conj α * α = (q : ℂ) := by
    rw [← Complex.normSq_eq_conj_mul_self, hα]
  have hα0 : α ≠ 0 := by
    intro h0
    apply hq
    rw [← hα, h0, map_zero]
  -- `q ⟪y, x⟫ = ⟪B y, B x⟫ = conj α ⟪y, B x⟫`
  have h1 : (q : ℂ) * inner ℂ (shift B α x) x = conj α * inner ℂ (shift B α x) (B x) := by
    rw [← hB (shift B α x) x, hBy, inner_smul_left]
  -- `⟪y, y⟫ = ⟪y, B x⟫ − α ⟪y, x⟫`
  have h2 : inner ℂ (shift B α x) (shift B α x) =
      inner ℂ (shift B α x) (B x) - α * inner ℂ (shift B α x) x := by
    conv_lhs => rw [shift_apply B α x]
    rw [inner_sub_right, inner_smul_right, shift_apply]
  have h3 : conj α * inner ℂ (shift B α x) (shift B α x) = 0 := by
    rw [h2, mul_sub, ← h1, ← mul_assoc, hαα, sub_self]
  have hc : conj α ≠ 0 := by
    simpa using hα0
  have h4 : inner ℂ (shift B α x) (shift B α x) = 0 := (mul_eq_zero.mp h3).resolve_left hc
  exact inner_self_eq_zero.mp h4

/-- [proved-derived; formal-checked] The generalized eigenspace at a mode on the circle is the
eigenspace: `(B − α)^(k+1) x = 0` gives `(B − α) x = 0`. -/
theorem pow_ker_of_similitude (B : E →ₗ[ℂ] E) (q : ℝ)
    (hB : ∀ x y, inner ℂ (B x) (B y) = (q : ℂ) * inner ℂ x y) (hq : q ≠ 0)
    {α : ℂ} (hα : Complex.normSq α = q) (k : ℕ) {x : E}
    (hx : ((shift B α) ^ (k + 1)) x = 0) : shift B α x = 0 := by
  induction k with
  | zero => simpa using hx
  | succ k ih =>
    apply ih
    -- `N^(k+2) x = N (N (N^k x))`, so `N (N^k x) = 0`, which is `N^(k+1) x = 0`.
    have e : (shift B α) ^ (k + 1 + 1) = shift B α * (shift B α * (shift B α) ^ k) := by
      rw [pow_succ', pow_succ']
    have h1 : shift B α (shift B α (((shift B α) ^ k) x)) = 0 := by
      have h0 := hx
      rw [e, Module.End.mul_apply, Module.End.mul_apply] at h0
      exact h0
    have h2 := no_jordan_block_of_similitude B q hB hq hα h1
    rw [pow_succ', Module.End.mul_apply]
    exact h2

end Half

/-! ## 3. The indefinite reading: a mode off the circle is a null vector of the scaled form -/

section Indefinite

variable {n : Type*} [Fintype n]

/-- [proved-derived; formal-checked] The Hermitian form of a matrix moved by `M` is the form of
`Mᴴ G M`. -/
theorem form_transport (G M : Matrix n n ℂ) (v : n → ℂ) :
    star (M *ᵥ v) ⬝ᵥ (G *ᵥ (M *ᵥ v)) = star v ⬝ᵥ ((Mᴴ * G * M) *ᵥ v) := by
  rw [star_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec (star v) Mᴴ]

/-- [proved-derived; formal-checked] The indefinite reading.  If `Mᴴ G M = q G` and `M v = α v`
then `(|α|² − q) · (v† G v) = 0`: a mode off the circle `|α|² = q` is a null vector of the scaled
form.  `G` need not be Hermitian or definite. -/
theorem mode_off_circle_is_null (G M : Matrix n n ℂ) (q : ℝ)
    (h : Mᴴ * G * M = (q : ℂ) • G) {α : ℂ} {v : n → ℂ} (hv : M *ᵥ v = α • v) :
    ((Complex.normSq α : ℂ) - q) * (star v ⬝ᵥ (G *ᵥ v)) = 0 := by
  have h1 := form_transport G M v
  rw [h, hv, smul_mulVec, dotProduct_smul, mulVec_smul, dotProduct_smul, star_smul,
    smul_dotProduct] at h1
  simp only [smul_eq_mul, Complex.star_def] at h1
  rw [Complex.normSq_eq_conj_mul_self, sub_mul]
  linear_combination h1

/-- [proved-derived; formal-checked] With a positive definite scaled form every mode sits at the
half. -/
theorem normSq_eigenvalue_of_posDef (G M : Matrix n n ℂ) (q : ℝ) (hG : G.PosDef)
    (h : Mᴴ * G * M = (q : ℂ) • G) {α : ℂ} {v : n → ℂ} (hv0 : v ≠ 0)
    (hv : M *ᵥ v = α • v) : Complex.normSq α = q := by
  have hnull := mode_off_circle_is_null G M q h hv
  have hpos : (0 : ℂ) < star v ⬝ᵥ (G *ᵥ v) := hG.dotProduct_mulVec_pos hv0
  have h2 : (Complex.normSq α : ℂ) - q = 0 := (mul_eq_zero.mp hnull).resolve_right hpos.ne'
  have h3 : (Complex.normSq α : ℂ) = q := sub_eq_zero.mp h2
  exact_mod_cast h3

end Indefinite

/-! ## 4. Real moves, complex modes -/

section RealMoves

variable {n : Type*} [Fintype n]

/-- [proved-derived; formal-checked] The Hermitian form of a real matrix on a complex vector has
real part the form on the vector's real part plus the form on its imaginary part. -/
theorem re_form_map (G : Matrix n n ℝ) (v : n → ℂ) :
    (star v ⬝ᵥ ((G.map (algebraMap ℝ ℂ)) *ᵥ v)).re =
      (fun i => (v i).re) ⬝ᵥ (G *ᵥ fun i => (v i).re) +
        (fun i => (v i).im) ⬝ᵥ (G *ᵥ fun i => (v i).im) := by
  simp only [dotProduct, mulVec, map_apply, Pi.star_apply, Complex.re_sum, Finset.mul_sum,
    Complex.coe_algebraMap, Complex.star_def]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_im]
  ring

/-- [proved-derived; formal-checked] A real positive definite form leaves no nonzero complex
null vector. -/
theorem form_map_ne_zero {G : Matrix n n ℝ} (hG : G.PosDef) {v : n → ℂ} (hv : v ≠ 0) :
    star v ⬝ᵥ ((G.map (algebraMap ℝ ℂ)) *ᵥ v) ≠ 0 := by
  intro h0
  have hre := re_form_map G v
  rw [h0, Complex.zero_re] at hre
  have hx : 0 ≤ (fun i => (v i).re) ⬝ᵥ (G *ᵥ fun i => (v i).re) := by
    simpa using hG.posSemidef.dotProduct_mulVec_nonneg (fun i => (v i).re)
  have hy : 0 ≤ (fun i => (v i).im) ⬝ᵥ (G *ᵥ fun i => (v i).im) := by
    simpa using hG.posSemidef.dotProduct_mulVec_nonneg (fun i => (v i).im)
  have hx0 : (fun i => (v i).re) ⬝ᵥ (G *ᵥ fun i => (v i).re) = 0 := by linarith
  have hy0 : (fun i => (v i).im) ⬝ᵥ (G *ᵥ fun i => (v i).im) = 0 := by linarith
  have hre0 : (fun i => (v i).re) = 0 := by
    by_contra hne
    have := hG.dotProduct_mulVec_pos hne
    simp only [star_trivial] at this
    linarith
  have him0 : (fun i => (v i).im) = 0 := by
    by_contra hne
    have := hG.dotProduct_mulVec_pos hne
    simp only [star_trivial] at this
    linarith
  apply hv
  funext i
  apply Complex.ext
  · simpa using congrFun hre0 i
  · simpa using congrFun him0 i

/-- [proved-derived; formal-checked] Real moves, complex modes: a real matrix `M` with
`Mᵀ G M = q G` for a real positive definite `G` has every complex mode at `|α|² = q`. -/
theorem normSq_eigenvalue_of_real_posDef (G M : Matrix n n ℝ) (q : ℝ) (hG : G.PosDef)
    (h : Mᵀ * G * M = q • G) {α : ℂ} {v : n → ℂ} (hv0 : v ≠ 0)
    (hv : (M.map (algebraMap ℝ ℂ)) *ᵥ v = α • v) : Complex.normSq α = q := by
  have hmap : (M.map (algebraMap ℝ ℂ))ᴴ * G.map (algebraMap ℝ ℂ) * M.map (algebraMap ℝ ℂ) =
      (q : ℂ) • G.map (algebraMap ℝ ℂ) := by
    have hconj : (M.map (algebraMap ℝ ℂ))ᴴ = Mᵀ.map (algebraMap ℝ ℂ) := by
      ext i j
      simp [conjTranspose_apply, transpose_apply]
    rw [hconj, ← Matrix.map_mul, ← Matrix.map_mul, h]
    ext i j
    simp
  have hnull := mode_off_circle_is_null (G.map (algebraMap ℝ ℂ)) (M.map (algebraMap ℝ ℂ)) q hmap hv
  have h2 : (Complex.normSq α : ℂ) - q = 0 :=
    (mul_eq_zero.mp hnull).resolve_right (form_map_ne_zero hG hv0)
  have h3 : (Complex.normSq α : ℂ) = q := sub_eq_zero.mp h2
  exact_mod_cast h3

end RealMoves

/-! ## 5. The converse: a diagonalizable move with its modes on the circle carries a certificate -/

section Converse

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- [proved-derived; formal-checked] The converse.  If `M = P D P⁻¹` with `P` invertible and
every diagonal mode at `|d i|² = q`, then `G = (P⁻¹)ᴴ P⁻¹` is positive definite and
`Mᴴ G M = q G`. -/
theorem certificate_of_diagonalizable (P : Matrix n n ℂ) (hP : IsUnit P.det) (d : n → ℂ)
    (q : ℝ) (hd : ∀ i, Complex.normSq (d i) = q) :
    ((P⁻¹)ᴴ * P⁻¹).PosDef ∧
      (P * diagonal d * P⁻¹)ᴴ * ((P⁻¹)ᴴ * P⁻¹) * (P * diagonal d * P⁻¹) =
        (q : ℂ) • ((P⁻¹)ᴴ * P⁻¹) := by
  have hinv : P⁻¹ * P = 1 := nonsing_inv_mul P hP
  have hinv' : P * P⁻¹ = 1 := mul_nonsing_inv P hP
  refine ⟨?_, ?_⟩
  · apply PosDef.conjTranspose_mul_self
    intro x y hxy
    have := congrArg (fun z => P *ᵥ z) hxy
    simpa [mulVec_mulVec, hinv'] using this
  · have hDD : (diagonal d)ᴴ * diagonal d = (q : ℂ) • (1 : Matrix n n ℂ) := by
      rw [diagonal_conjTranspose, diagonal_mul_diagonal]
      ext i j
      by_cases hij : i = j
      · subst hij
        rw [diagonal_apply_eq, Matrix.smul_apply, one_apply_eq, smul_eq_mul, mul_one]
        show star (d i) * d i = (q : ℂ)
        rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, hd]
      · rw [diagonal_apply_ne _ hij, Matrix.smul_apply, one_apply_ne hij, smul_zero]
    have hPP : Pᴴ * (P⁻¹)ᴴ = 1 := by
      rw [← conjTranspose_mul, hinv, conjTranspose_one]
    calc (P * diagonal d * P⁻¹)ᴴ * ((P⁻¹)ᴴ * P⁻¹) * (P * diagonal d * P⁻¹)
        = (P⁻¹)ᴴ * (diagonal d)ᴴ * (Pᴴ * (P⁻¹)ᴴ) * (P⁻¹ * P) * diagonal d * P⁻¹ := by
          simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = (P⁻¹)ᴴ * ((diagonal d)ᴴ * diagonal d) * P⁻¹ := by
          rw [hPP, hinv]
          simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = (q : ℂ) • ((P⁻¹)ᴴ * P⁻¹) := by
          rw [hDD]
          simp

end Converse

/-! ## 6. The cell: the companion of `x² − l x + q`, its area pairing and its norm form -/

section Cell

/-- [definition] The cell: the companion move of `x² − l x + q` on pairs `(a, b)`,
`(a, b) ↦ (−b, q a + l b)`. -/
def cell (l q : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; q, l]

/-- [definition] The area pairing on pairs: `ω ((a, b), (a', b')) = a b' − b a'`. -/
def area : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, 0]

/-- [definition] The norm form of the cell, `q a² + l a b + b²`, as a symmetric matrix. -/
def normForm (l q : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![q, l / 2; l / 2, 1]

/-- [proved-derived; formal-checked] The cell's determinant is the count `q`. -/
theorem cell_det (l q : ℝ) : (cell l q).det = q := by
  simp [cell, det_fin_two]

/-- [proved-derived; formal-checked] The cell's trace is `l`. -/
theorem cell_trace (l q : ℝ) : (cell l q).trace = l := by
  simp [cell, trace_fin_two]

/-- [proved-derived; formal-checked] The cell is a similitude of the area pairing by its
determinant: the reversal a functional equation supplies, with no condition on `l`. -/
theorem cell_area_similitude (l q : ℝ) : (cell l q)ᵀ * area * cell l q = q • area := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cell, area, Matrix.mul_apply, Fin.sum_univ_two]

/-- [proved-derived; formal-checked] The area pairing of a state with its own image under the
cell is the norm form `q a² + l a b + b²`. -/
theorem area_cell (l q a b : ℝ) :
    ![a, b] ⬝ᵥ (area *ᵥ (cell l q *ᵥ ![a, b])) = q * a ^ 2 + l * a * b + b ^ 2 := by
  simp [cell, area, dotProduct, mulVec, Fin.sum_univ_two]
  ring

/-- [proved-derived; formal-checked] The norm form's matrix is the symmetric part of
`area * cell`: the reversal's own form of the area pairing and the cell, halved. -/
theorem normForm_eq_symm_part (l q : ℝ) :
    (2 : ℝ) • normForm l q = area * cell l q + (area * cell l q)ᵀ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cell, area, normForm] <;> ring

/-- [proved-derived; formal-checked] The value of the norm form on a pair. -/
theorem normForm_value (l q : ℝ) (x : Fin 2 → ℝ) :
    x ⬝ᵥ (normForm l q *ᵥ x) = q * x 0 ^ 2 + l * x 0 * x 1 + x 1 ^ 2 := by
  simp [normForm, dotProduct, mulVec, Fin.sum_univ_two]
  ring

/-- [proved-derived; formal-checked] The norm form is scaled by `q` under the cell, for every
`l`: the scaling is an identity, and only the form's sign depends on `l`. -/
theorem normForm_similitude (l q : ℝ) :
    (cell l q)ᵀ * normForm l q * cell l q = q • normForm l q := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cell, normForm, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- [proved-derived; formal-checked] The norm form completes its square:
`q a² + l a b + b² = (b + l a / 2)² + (q − l² / 4) a²`. -/
theorem normForm_complete_square (l q a b : ℝ) :
    q * a ^ 2 + l * a * b + b ^ 2 = (b + l * a / 2) ^ 2 + (q - l ^ 2 / 4) * a ^ 2 := by
  ring

/-- [proved-derived; formal-checked] The norm form is positive on every nonzero pair iff
`l² < 4 q`: the cell is a turn. -/
theorem normForm_pos_iff (l q : ℝ) :
    (∀ x : Fin 2 → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (normForm l q *ᵥ x)) ↔ l ^ 2 < 4 * q := by
  constructor
  · intro h
    have hne : (![2, -l] : Fin 2 → ℝ) ≠ 0 := by
      intro h0
      have := congrFun h0 0
      simp at this
    have := h ![2, -l] hne
    rw [normForm_value] at this
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
    nlinarith
  · intro h x hx
    rw [normForm_value, normForm_complete_square]
    by_cases h0 : x 0 = 0
    · have h1 : x 1 ≠ 0 := by
        intro h1
        apply hx
        funext i
        fin_cases i
        · simpa using h0
        · simpa using h1
      rw [h0]
      have : 0 < x 1 ^ 2 := by positivity
      nlinarith
    · have hpos : 0 < (q - l ^ 2 / 4) * x 0 ^ 2 := by
        apply mul_pos
        · linarith
        · positivity
      have : 0 ≤ (x 1 + l * x 0 / 2) ^ 2 := sq_nonneg _
      linarith

/-- [proved-derived; formal-checked] At `l² = 4 q` the norm form has a nonzero null vector: the
cell is a shear. -/
theorem normForm_null_of_eq (l q : ℝ) (h : l ^ 2 = 4 * q) :
    ∃ x : Fin 2 → ℝ, x ≠ 0 ∧ x ⬝ᵥ (normForm l q *ᵥ x) = 0 := by
  refine ⟨![2, -l], ?_, ?_⟩
  · intro h0
    have := congrFun h0 0
    simp at this
  · rw [normForm_value]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    nlinarith

/-- [proved-derived; formal-checked] At `4 q < l²` the norm form takes a negative value: the cell
is a boost and its norm is indefinite. -/
theorem normForm_neg_of_lt (l q : ℝ) (h : 4 * q < l ^ 2) :
    ∃ x : Fin 2 → ℝ, x ⬝ᵥ (normForm l q *ᵥ x) < 0 := by
  refine ⟨![2, -l], ?_⟩
  rw [normForm_value]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  nlinarith

/-- [proved-derived; formal-checked] The norm form's matrix is symmetric. -/
theorem normForm_isSymm (l q : ℝ) : (normForm l q).IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [normForm]

/-- [proved-derived; formal-checked] The norm form's matrix is positive definite iff
`l² < 4 q`. -/
theorem normForm_posDef_iff (l q : ℝ) : (normForm l q).PosDef ↔ l ^ 2 < 4 * q := by
  rw [← normForm_pos_iff]
  constructor
  · intro h x hx
    have := h.dotProduct_mulVec_pos hx
    simpa using this
  · intro h
    refine PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
    · show (normForm l q)ᴴ = normForm l q
      rw [conjTranspose_eq_transpose_of_trivial]
      exact normForm_isSymm l q
    · simpa using h x hx

/-- [proved-derived; formal-checked] The cell at a turn: for `l² < 4 q` every complex mode of the
cell has `|α|² = q`, by the positive definite norm form and the similitude criterion. -/
theorem cell_modes_on_circle (l q : ℝ) (h : l ^ 2 < 4 * q) {α : ℂ} {v : Fin 2 → ℂ}
    (hv0 : v ≠ 0) (hv : ((cell l q).map (algebraMap ℝ ℂ)) *ᵥ v = α • v) :
    Complex.normSq α = q :=
  normSq_eigenvalue_of_real_posDef (normForm l q) (cell l q) q
    ((normForm_posDef_iff l q).mpr h) (normForm_similitude l q) hv0 hv

end Cell

section Audit

#print axioms krein_similitude
#print axioms kreinPow_similitude
#print axioms normSq_eigenvalue_of_similitude
#print axioms norm_sq_iterate_of_similitude
#print axioms no_jordan_block_of_similitude
#print axioms pow_ker_of_similitude
#print axioms mode_off_circle_is_null
#print axioms normSq_eigenvalue_of_posDef
#print axioms normSq_eigenvalue_of_real_posDef
#print axioms certificate_of_diagonalizable
#print axioms cell_area_similitude
#print axioms normForm_similitude
#print axioms normForm_pos_iff
#print axioms normForm_posDef_iff
#print axioms cell_modes_on_circle

end Audit

end Holonics.Coupling.KreinForm
