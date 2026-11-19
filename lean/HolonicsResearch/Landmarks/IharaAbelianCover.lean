import Mathlib
import HolonicsResearch.Landmarks.IharaBassConnection

/-!
# Artin's factorization over an abelian cover: a complex's dart determinant is the product of its characters' L-functions

`Landmarks/IharaBassConnection` proves the factorization for a double cover, by one block
operation.  This owner proves it for a cover of any number of sheets whose voltages lie in a
finite abelian group, by the group's own characters: the cover's dart determinant is the product,
over the characters, of the base's dart determinant twisted by each character.

The voltage group is the additive group of a finite commutative ring `G` (every finite abelian
group is one: a product of `ZMod mᵢ`).  A voltage `σ : E ⊕ E → G` on the darts of a complex
(cells `V`, contacts `E`, ends `a b : E → V`, the model of `Landmarks/IharaBass`) builds the cover
with cells `V × G` and darts `(E ⊕ E) × G`: the dart `(d, s)` leaves `src d` on sheet `s` and
enters `tgt d` on sheet `s + σ d`.  The characters are read through one primitive additive
character `ψ : AddChar G K` into a domain in which `#G` is not zero: the `k`-th character is
`x ↦ ψ (k * x)`, and these are all of them (`AddChar.sum_mulShift` is their orthogonality).

* [definition] `coverHashimoto σ`: the cover's dart operator in the base's model; `charFrame ψ`: the
  matrix `1 ⊗ (ψ (s * k))_{s,k}` that carries a function of the sheets to its characters;
  `twist ψ σ k`: the connection `d ↦ ψ (k * σ d)`.
* [proved-derived; formal-checked] the intertwining `cover_mul_charFrame`:
  `(1 − u B_Y) · W = W · blockDiag (k ↦ 1 − u · diag (twist k) · B)`, with no division; and
  `charFrame_det_ne_zero` (`W` is invertible because the characters are orthogonal on both sides,
  `charTableInv_mul_charTable` and `charTable_mul_charTableInv`, so the reversed frame
  `charFrameInv ψ` is a two-sided inverse up to `#G`: `charFrameInv_mul_charFrame`,
  `charFrame_mul_charFrameInv`).  The frame is named `charFrame` and not `fourier`, which
  Mathlib's Fourier basis on `AddCircle` holds under `open`.
* [proved-derived; formal-checked] **`artin_abelian_cover`** (A1): for every voltage and every `u`,
  `det (1 − u B_Y) = ∏_k det (1 − u B_{twist k})`, the twisted dart operators of
  `Landmarks/IharaBassConnection`.
* [proved-derived; formal-checked] `twist_connection` (A2): when `σ d.swap = −σ d` every twist is a
  connection, so each factor obeys Ihara–Bass with that connection, and
  **`artin_abelian_cover_ihara_bass`**: `(1 − u²)^(|V|·|G|) · det (1 − u B_Y) =
  ∏_k det (1 − u A_{twist k} + u² (D − 1)) · (1 − u²)^(|E|·|G|)`.
* [proved-derived; formal-checked] `twist_zero`, `artin_abelian_cover_base` (A3): the trivial
  character's factor is the base's dart determinant, so the base's divides the cover's
  (`base_dvd_cover`).
* [proved-derived; formal-checked] the cover is a complex of the plain kind (A4):
  `hashimoto_cover` identifies `coverHashimoto` with `IharaBass.hashimoto` of the contacts `E × G`
  with ends `coverA`, `coverB σ`, through `dartEquiv σ`, when `σ d.swap = −σ d`; so
  **`artin_abelian_cover_hashimoto`** states A1 for the plain dart operator of the cover.
* [proved-derived; formal-checked] a closed chain (A5): the cover of one cell with one loop of
  voltage `h` by `ZMod m` (`loopCover_det`) is `∏_k (1 − ψ(k h) u)(1 − ψ(−k h) u)`, each sense of
  the loop read with its character's holonomy; with voltage `1` and the `m`-th roots of unity in a
  field, `cycle_det` multiplies the factors out to `(1 − u^m)²`, the dart determinant of the
  `m`-cycle (`prod_sub_zmodChar`, `prod_one_sub_mul_of_prod_sub`).

**Reading.**  [interpretation] A1 is Artin's factorization `ζ_Y = ∏_χ L(χ)` for an abelian cover
of a finite complex (Stark and Terras 1996, `from training`), stated for the dart determinant.
The trivial character carries the base, and each other character carries what the cover adds:
its new modes are the modes of the twisted operators.  The holonomy of a closed walk, the sum of
its voltages, is what each character reads, and the gauge theorem of
`Landmarks/IharaBassConnection` (each twist is a connection whose determinant reads holonomies
alone) applies to every factor.  The double cover is the case `G = ZMod 2`, `ψ x = (−1)^x`.

**What this does not state.**  The cover's spectrum is not computed as the union of the twisted
spectra (the factorization of determinants says it for the dart operator's characteristic
roots, read through `det (1 − u B)`; no statement about eigenvectors is made).  Non-abelian covers
(an irreducible representation of degree above one in each factor) are not here.  No Euler
product is used, so the splitting of a prime cycle in the cover by the order of its holonomy is
not stated; the closed walks sorted by holonomy class, read through the twisted traces, are
`Landmarks/IharaCoverChebotarev`.

**Computational object.**  The helical pair interaction: the voltage is a pair contact's carry
between sheets, the characters are the cover's own frames, and the factorization is the
diagonalization of the sheets by those frames.  Of the winding guide's six objects: the pair (the
contact and its transport), cell holonomy (what each character reads around a closed walk) and
the tower thread (a cover is a transverse restriction with plural gluing).

**Consumers.**  The third record of November 18 on the half (§3, Artin's factorization and the
holonomy reading); the atlas row `trace.abelian-cover-artin`.

Source record: `research/records/2026-11-18_AN_ABELIAN_COVER_FACTORS_THROUGH_ITS_CHARACTERS_A_TEMPERED_COMPLEX_MIXES_AT_ITS_HALF_THE_FLUIDS_TRIADS_DO_NO_WORK_SO_EVERY_TRUNCATION_FLOWS_FOR_ALL_TIME_AND_HARD_LEFSCHETZ_IS_A_POSITIVE_COMMUTATOR.md`.

No `sorry`, no `axiom`, no `native_decide`.
-/

open Matrix
open scoped Kronecker

namespace Holonics.Landmarks.IharaAbelianCover

open Holonics.Landmarks.IharaBass Holonics.Landmarks.IharaBassConnection

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable {G : Type*} [CommRing G] [Fintype G] [DecidableEq G]
variable {K : Type*} [CommRing K]
variable (a b : E → V)

/-! ## The cover, the characters and the twists -/

section Defs

variable (K)

/-- [definition] The dart operator of the abelian cover of the voltage `σ`, in the base's model.
The dart `(d, s)` leaves `src d` on sheet `s` and enters `tgt d` on sheet `s + σ d`; `(f, s')`
continues it when `f` leaves the cell `d` enters, `f` is not `d` reversed and `s'` is the sheet
`(d, s)` ends on. -/
def coverHashimoto (σ : E ⊕ E → G) : Matrix ((E ⊕ E) × G) ((E ⊕ E) × G) K :=
  Matrix.of fun p p' =>
    if tgt a b p.1 = src a b p'.1 ∧ p'.1 ≠ p.1.swap ∧ p'.2 = p.2 + σ p.1 then 1 else 0

variable {K}

/-- [definition] The character table of the sheets: `F s k = ψ (s * k)`. -/
def charTable (ψ : AddChar G K) : Matrix G G K := Matrix.of fun s k => ψ (s * k)

/-- [definition] Its reversed table: `F' k s = ψ (−(k * s))`. -/
def charTableInv (ψ : AddChar G K) : Matrix G G K := Matrix.of fun k s => ψ (-(k * s))

/-- [definition] The frame change of the cover's darts: on each base dart, the character table of
the sheets. -/
def charFrame (D : Type*) [Fintype D] [DecidableEq D] (ψ : AddChar G K) :
    Matrix (D × G) (D × G) K :=
  (1 : Matrix D D K) ⊗ₖ charTable ψ

/-- [definition] The reversed frame change: on each base dart, the reversed character table. -/
def charFrameInv (D : Type*) [Fintype D] [DecidableEq D] (ψ : AddChar G K) :
    Matrix (D × G) (D × G) K :=
  (1 : Matrix D D K) ⊗ₖ charTableInv ψ

/-- [definition] The `k`-th twist of the voltage: the connection `d ↦ ψ (k * σ d)`. -/
def twist (ψ : AddChar G K) (σ : E ⊕ E → G) (k : G) : E ⊕ E → K := fun d => ψ (k * σ d)

end Defs

/-! ## The characters are orthogonal, so the frame change is invertible -/

section Orthogonality

variable [IsDomain K]

/-- [proved-derived; formal-checked] `F' F = #G`: the characters `x ↦ ψ (k * x)` of a primitive
`ψ` are orthogonal. -/
theorem charTableInv_mul_charTable {ψ : AddChar G K} (hψ : ψ.IsPrimitive) :
    charTableInv ψ * charTable ψ = (Fintype.card G : K) • (1 : Matrix G G K) := by
  ext k k'
  simp only [Matrix.mul_apply, charTableInv, charTable, Matrix.of_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul]
  have h : ∀ s : G, ψ (-(k * s)) * ψ (s * k') = ψ (s * (k' - k)) := by
    intro s
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  simp_rw [h]
  rw [AddChar.sum_mulShift (k' - k) hψ]
  by_cases hk : k = k'
  · subst hk
    simp
  · have : k' - k ≠ 0 := sub_ne_zero.mpr (Ne.symm hk)
    simp [this, hk]

/-- [proved-derived; formal-checked] The character table is invertible when `#G ≠ 0` in `K`. -/
theorem charTable_det_ne_zero {ψ : AddChar G K} (hψ : ψ.IsPrimitive)
    (hG : (Fintype.card G : K) ≠ 0) : (charTable ψ).det ≠ 0 := by
  intro h
  have h1 := congrArg Matrix.det (charTableInv_mul_charTable hψ)
  rw [Matrix.det_mul, h, mul_zero, Matrix.det_smul, Matrix.det_one, mul_one] at h1
  exact pow_ne_zero _ hG h1.symm

/-- [proved-derived; formal-checked] The frame change of the cover's darts is invertible. -/
theorem charFrame_det_ne_zero (D : Type*) [Fintype D] [DecidableEq D] {ψ : AddChar G K}
    (hψ : ψ.IsPrimitive) (hG : (Fintype.card G : K) ≠ 0) : (charFrame D ψ).det ≠ 0 := by
  rw [charFrame, Matrix.det_kronecker, Matrix.det_one, one_pow, one_mul]
  exact pow_ne_zero _ (charTable_det_ne_zero hψ hG)

/-- [proved-derived; formal-checked] The other side of the characters' orthogonality:
`F F' = #G`. -/
theorem charTable_mul_charTableInv {ψ : AddChar G K} (hψ : ψ.IsPrimitive) :
    charTable ψ * charTableInv ψ = (Fintype.card G : K) • (1 : Matrix G G K) := by
  ext s s'
  simp only [Matrix.mul_apply, charTableInv, charTable, Matrix.of_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul]
  have h : ∀ k : G, ψ (s * k) * ψ (-(k * s')) = ψ (k * (s - s')) := by
    intro k
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  simp_rw [h]
  rw [AddChar.sum_mulShift (s - s') hψ]
  by_cases hs : s = s'
  · subst hs
    simp
  · have : s - s' ≠ 0 := sub_ne_zero.mpr hs
    simp [this, hs]

/-- [proved-derived; formal-checked] `W' W = #G` on the cover's darts. -/
theorem charFrameInv_mul_charFrame (D : Type*) [Fintype D] [DecidableEq D]
    {ψ : AddChar G K} (hψ : ψ.IsPrimitive) :
    charFrameInv D ψ * charFrame D ψ = (Fintype.card G : K) • (1 : Matrix (D × G) (D × G) K) := by
  rw [charFrameInv, charFrame, ← Matrix.mul_kronecker_mul, Matrix.mul_one,
    charTableInv_mul_charTable hψ, Matrix.kronecker_smul, Matrix.one_kronecker_one]

/-- [proved-derived; formal-checked] `W W' = #G` on the cover's darts. -/
theorem charFrame_mul_charFrameInv (D : Type*) [Fintype D] [DecidableEq D]
    {ψ : AddChar G K} (hψ : ψ.IsPrimitive) :
    charFrame D ψ * charFrameInv D ψ = (Fintype.card G : K) • (1 : Matrix (D × G) (D × G) K) := by
  rw [charFrameInv, charFrame, ← Matrix.mul_kronecker_mul, Matrix.mul_one,
    charTable_mul_charTableInv hψ, Matrix.kronecker_smul, Matrix.one_kronecker_one]

end Orthogonality

/-! ## The intertwining and the factorization -/

section Factorization

omit [Fintype V] in
/-- [proved-derived; formal-checked] The cover's operator in the characters' frame:
`B_Y · W = W · blockDiag (k ↦ diag (twist k) · B)`. -/
theorem coverHashimoto_mul_charFrame (ψ : AddChar G K) (σ : E ⊕ E → G) :
    coverHashimoto K a b σ * charFrame (E ⊕ E) ψ =
      charFrame (E ⊕ E) ψ * Matrix.blockDiagonal fun k =>
        Matrix.diagonal (twist ψ σ k) * hashimoto K a b := by
  ext ⟨d, s⟩ ⟨f, k⟩
  rw [Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp only [charFrame, Matrix.kroneckerMap_apply, charTable, Matrix.of_apply, Matrix.one_apply,
    Matrix.blockDiagonal_apply, coverHashimoto, Matrix.diagonal_mul, hashimoto_apply, twist,
    ite_mul, one_mul, zero_mul, mul_ite, mul_zero, ite_and]
  simp only [Finset.sum_ite_irrel, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Finset.sum_const_zero]
  rw [Fintype.sum_eq_single d (fun x hx => by simp [Ne.symm hx])]
  simp only [if_true, mul_one, add_mul, AddChar.map_add_eq_mul, mul_comm k]

omit [Fintype V] in
/-- [proved-derived; formal-checked] **The intertwining.**  The frame change carries `1 − u B_Y` to
the block diagonal of the twisted operators:
`(1 − u B_Y) · W = W · blockDiag (k ↦ 1 − u · diag (twist k) · B)`.  No division is used. -/
theorem cover_mul_charFrame (ψ : AddChar G K) (σ : E ⊕ E → G) (u : K) :
    (1 - u • coverHashimoto K a b σ) * charFrame (E ⊕ E) ψ =
      charFrame (E ⊕ E) ψ * Matrix.blockDiagonal fun k =>
        (1 - u • (Matrix.diagonal (twist ψ σ k) * hashimoto K a b)) := by
  have hbd : (Matrix.blockDiagonal fun k =>
      (1 - u • (Matrix.diagonal (twist ψ σ k) * hashimoto K a b))) =
      1 - u • Matrix.blockDiagonal fun k => Matrix.diagonal (twist ψ σ k) * hashimoto K a b := by
    rw [← Matrix.blockDiagonal_smul, ← Matrix.blockDiagonal_one, ← Matrix.blockDiagonal_sub]
    rfl
  rw [hbd, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, coverHashimoto_mul_charFrame,
    Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul]

omit [Fintype V] in
/-- [proved-derived; formal-checked] Weighing the first dart and weighing the second give the same
determinant: `det (1 − u · diag w · B) = det (1 − u B_w)`. -/
theorem det_one_sub_diagonal_mul_hashimoto (w : E ⊕ E → K) (u : K) :
    (1 - u • (Matrix.diagonal w * hashimoto K a b)).det = (1 - u • hashimotoC a b w).det := by
  rw [← Matrix.smul_mul, Matrix.det_one_sub_mul_comm, Matrix.mul_smul, hashimoto_mul_diagonal]

omit [Fintype V] in
/-- [proved-derived; formal-checked] **Artin's factorization over an abelian cover** (A1).  For a
finite commutative ring `G` of voltages, a primitive additive character `ψ` into a domain in which
`#G ≠ 0`, every voltage `σ` on the darts and every `u`,
`det (1 − u B_Y) = ∏_k det (1 − u B_{twist k})`: the cover's dart determinant is the product of the
base's twisted by each character. -/
theorem artin_abelian_cover [IsDomain K] {ψ : AddChar G K} (hψ : ψ.IsPrimitive)
    (hG : (Fintype.card G : K) ≠ 0) (σ : E ⊕ E → G) (u : K) :
    (1 - u • coverHashimoto K a b σ).det =
      ∏ k, (1 - u • hashimotoC a b (twist ψ σ k)).det := by
  have hW := charFrame_det_ne_zero (E ⊕ E) hψ hG
  have h := congrArg Matrix.det (cover_mul_charFrame a b ψ σ u)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_blockDiagonal, mul_comm] at h
  refine (mul_left_cancel₀ hW h).trans ?_
  exact Finset.prod_congr rfl fun k _ => det_one_sub_diagonal_mul_hashimoto a b _ u

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] [Fintype G] [DecidableEq G] in
/-- [proved-derived; formal-checked] Each twist of a voltage that is reversed on the reversed dart,
`σ d.swap = −σ d`, is a connection (A2). -/
theorem twist_connection (ψ : AddChar G K) {σ : E ⊕ E → G} (hσ : ∀ d, σ d.swap = -σ d) (k : G)
    (d : E ⊕ E) : twist ψ σ k d * twist ψ σ k d.swap = 1 := by
  simp only [twist, hσ d, ← AddChar.map_add_eq_mul, mul_neg, add_neg_cancel,
    AddChar.map_zero_eq_one]

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] [Fintype G] [DecidableEq G] in
/-- [proved-derived; formal-checked] The trivial character's twist is the trivial connection. -/
theorem twist_zero (ψ : AddChar G K) (σ : E ⊕ E → G) : twist ψ σ 0 = fun _ => (1 : K) := by
  funext d
  simp [twist]

/-- [proved-derived; formal-checked] **Ihara–Bass over an abelian cover** (A2).  With
`σ d.swap = −σ d`, `(1 − u²)^(|V|·|G|) · det (1 − u B_Y) =
∏_k det (1 − u A_{twist k} + u² (D − 1)) · (1 − u²)^(|E|·|G|)`. -/
theorem artin_abelian_cover_ihara_bass [IsDomain K] {ψ : AddChar G K} (hψ : ψ.IsPrimitive)
    (hG : (Fintype.card G : K) ≠ 0) {σ : E ⊕ E → G} (hσ : ∀ d, σ d.swap = -σ d) (u : K) :
    (1 - u ^ 2) ^ (Fintype.card V * Fintype.card G) * (1 - u • coverHashimoto K a b σ).det =
      (∏ k, (1 - u • adjacencyC a b (twist ψ σ k) + u ^ 2 • (degree K a b - 1)).det) *
        (1 - u ^ 2) ^ (Fintype.card E * Fintype.card G) := by
  rw [artin_abelian_cover a b hψ hG σ u, pow_mul, pow_mul, ← Finset.card_univ (α := G),
    ← Finset.prod_const, ← Finset.prod_const, ← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun k _ =>
    ihara_bass_connection a b (twist ψ σ k) (twist_connection ψ hσ k) u

omit [Fintype V] in
/-- [proved-derived; formal-checked] **The base's factor** (A3): the trivial character carries the
base, `det (1 − u B_Y) = det (1 − u B) · ∏_{k ≠ 0} det (1 − u B_{twist k})`. -/
theorem artin_abelian_cover_base [IsDomain K] {ψ : AddChar G K} (hψ : ψ.IsPrimitive)
    (hG : (Fintype.card G : K) ≠ 0) (σ : E ⊕ E → G) (u : K) :
    (1 - u • coverHashimoto K a b σ).det =
      (1 - u • hashimoto K a b).det *
        ∏ k ∈ Finset.univ.erase (0 : G), (1 - u • hashimotoC a b (twist ψ σ k)).det := by
  rw [artin_abelian_cover a b hψ hG σ u,
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (0 : G)), twist_zero, hashimotoC_one]

omit [Fintype V] in
/-- [proved-derived; formal-checked] The base's dart determinant divides the cover's. -/
theorem base_dvd_cover [IsDomain K] {ψ : AddChar G K} (hψ : ψ.IsPrimitive)
    (hG : (Fintype.card G : K) ≠ 0) (σ : E ⊕ E → G) (u : K) :
    (1 - u • hashimoto K a b).det ∣ (1 - u • coverHashimoto K a b σ).det := by
  rw [artin_abelian_cover_base a b hψ hG σ u]
  exact Dvd.intro _ rfl

end Factorization

/-! ## The cover is a complex of the plain kind -/

section Complex

/-- [definition] The cover's contacts are `E × G`; the first end of `(e, s)` is `a e` on sheet
`s`. -/
def coverA : E × G → V × G := fun p => (a p.1, p.2)

/-- [definition] The second end of `(e, s)` is `b e` on the sheet `s + σ (inl e)`. -/
def coverB (σ : E ⊕ E → G) : E × G → V × G := fun p => (b p.1, p.2 + σ (Sum.inl p.1))

/-- [definition] The cover's darts in the two models: `inl (e, s) ↦ (inl e, s)` and
`inr (e, s) ↦ (inr e, s + σ (inl e))`, the sheet the reversed dart leaves. -/
def dartEquiv (σ : E ⊕ E → G) : (E × G) ⊕ (E × G) ≃ (E ⊕ E) × G where
  toFun := Sum.elim (fun p => (Sum.inl p.1, p.2))
    (fun p => (Sum.inr p.1, p.2 + σ (Sum.inl p.1)))
  invFun q := Sum.elim (fun e => Sum.inl (e, q.2))
    (fun e => Sum.inr (e, q.2 - σ (Sum.inl e))) q.1
  left_inv := by
    rintro (⟨e, s⟩ | ⟨e, s⟩)
    · rfl
    · simp
  right_inv := by
    rintro ⟨e | e, s⟩
    · rfl
    · simp

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] [Fintype G] [DecidableEq G] in
/-- [proved-derived; formal-checked] A cover dart leaves the base dart's start on its own sheet. -/
theorem cover_src (σ : E ⊕ E → G) (y : (E × G) ⊕ (E × G)) :
    src (coverA a) (coverB b σ) y = (src a b (dartEquiv σ y).1, (dartEquiv σ y).2) := by
  rcases y with ⟨e, s⟩ | ⟨e, s⟩ <;> rfl

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] [Fintype G] [DecidableEq G] in
/-- [proved-derived; formal-checked] A cover dart enters the base dart's end on the sheet
`s + σ d`. -/
theorem cover_tgt (σ : E ⊕ E → G) (hσ : ∀ d, σ d.swap = -σ d) (x : (E × G) ⊕ (E × G)) :
    tgt (coverA a) (coverB b σ) x =
      (tgt a b (dartEquiv σ x).1, (dartEquiv σ x).2 + σ (dartEquiv σ x).1) := by
  rcases x with ⟨e, s⟩ | ⟨e, s⟩
  · rfl
  · have h := hσ (Sum.inl e)
    simp only [Sum.swap_inl] at h
    simp [dartEquiv, coverA, h]

omit [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E] [Fintype G] [DecidableEq G] in
/-- [proved-derived; formal-checked] The reversal of a cover dart is `(d.swap, s + σ d)`. -/
theorem dartEquiv_swap (σ : E ⊕ E → G) (hσ : ∀ d, σ d.swap = -σ d)
    (x : (E × G) ⊕ (E × G)) :
    dartEquiv σ x.swap = ((dartEquiv σ x).1.swap, (dartEquiv σ x).2 + σ (dartEquiv σ x).1) := by
  rcases x with ⟨e, s⟩ | ⟨e, s⟩
  · rfl
  · have h := hσ (Sum.inl e)
    simp only [Sum.swap_inl] at h
    simp [dartEquiv, h]

omit [Fintype V] [Fintype E] [Fintype G] in
/-- [proved-derived; formal-checked] The cover's dart operator is the plain file's `hashimoto` of
the contacts `E × G` with ends `coverA`, `coverB σ`, through `dartEquiv σ` (A4). -/
theorem hashimoto_cover (σ : E ⊕ E → G) (hσ : ∀ d, σ d.swap = -σ d) :
    hashimoto K (coverA a) (coverB b σ) =
      (coverHashimoto K a b σ).submatrix (dartEquiv σ) (dartEquiv σ) := by
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
/-- [proved-derived; formal-checked] **Artin's factorization on the plain model** (A4).  For a
voltage with `σ d.swap = −σ d`, the dart determinant of the cover (contacts `E × G`, ends
`coverA`, `coverB σ`) is the product over the characters of the twisted dart determinants. -/
theorem artin_abelian_cover_hashimoto [IsDomain K] {ψ : AddChar G K} (hψ : ψ.IsPrimitive)
    (hG : (Fintype.card G : K) ≠ 0) (σ : E ⊕ E → G) (hσ : ∀ d, σ d.swap = -σ d) (u : K) :
    (1 - u • hashimoto K (coverA a) (coverB b σ)).det =
      ∏ k, (1 - u • hashimotoC a b (twist ψ σ k)).det := by
  rw [hashimoto_cover a b σ hσ, ← artin_abelian_cover a b hψ hG σ u,
    ← Matrix.det_submatrix_equiv_self (dartEquiv σ) (1 - u • coverHashimoto K a b σ)]
  congr 1
  ext x y
  simp [Matrix.one_apply, (dartEquiv σ).injective.eq_iff]

end Complex

/-! ## A closed chain: the cover of one loop -/

section Loop

/-- [proved-derived; formal-checked] **The cover of one loop** (A5).  One cell, one contact that is
a loop, voltage `h` on its first dart and `−h` on its reversal: the cover's dart determinant is
`∏_k (1 − ψ (k h) u)(1 − ψ (−(k h)) u)`, each sense of the loop read with its character's
holonomy. -/
theorem loopCover_det [IsDomain K] {ψ : AddChar G K} (hψ : ψ.IsPrimitive)
    (hG : (Fintype.card G : K) ≠ 0) (h : G) (u : K) :
    (1 - u • coverHashimoto K (fun _ : Unit => ()) (fun _ : Unit => ())
        (Sum.elim (fun _ => h) (fun _ => -h))).det =
      ∏ k, (1 - ψ (k * h) * u) * (1 - ψ (-(k * h)) * u) := by
  rw [artin_abelian_cover _ _ hψ hG]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [det_hashimotoC_loop]
  simp [twist, mul_neg]

end Loop

/-! ## The closed chain of `m` contacts -/

section Cycle

variable {F : Type*} [Field F] {m : ℕ} [NeZero m] {ζ : F}

/-- [proved-standard; formal-checked] The characters of `ZMod m` read through a primitive `m`-th
root of unity are the `m`-th roots of unity: `∏_k (x − ψ k) = x^m − 1`. -/
theorem prod_sub_zmodChar (hζ : IsPrimitiveRoot ζ m) (x : F) :
    ∏ k : ZMod m, (x - AddChar.zmodChar m hζ.pow_eq_one k) = x ^ m - 1 := by
  classical
  have hm : 0 < m := NeZero.pos m
  have hpoly := congrArg (Polynomial.eval x) (Polynomial.X_pow_sub_one_eq_prod hm hζ)
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one,
    Polynomial.eval_prod, Polynomial.eval_C] at hpoly
  rw [hpoly]
  refine Finset.prod_nbij (fun k => AddChar.zmodChar m hζ.pow_eq_one k) ?_ ?_ ?_ ?_
  · intro k _
    rw [Polynomial.mem_nthRootsFinset hm, AddChar.zmodChar_apply, ← pow_mul, mul_comm, pow_mul,
      hζ.pow_eq_one, one_pow]
  · intro k _ k' _ hkk
    simp only [AddChar.zmodChar_apply] at hkk
    exact ZMod.val_injective m (hζ.pow_inj (ZMod.val_lt k) (ZMod.val_lt k') hkk)
  · intro ξ hξ
    rw [Finset.mem_coe, Polynomial.mem_nthRootsFinset hm] at hξ
    obtain ⟨i, hi, rfl⟩ := hζ.eq_pow_of_pow_eq_one hξ
    refine ⟨(i : ZMod m), Finset.mem_coe.mpr (Finset.mem_univ _), ?_⟩
    show AddChar.zmodChar m hζ.pow_eq_one (i : ZMod m) = ζ ^ i
    rw [AddChar.zmodChar_apply, ZMod.val_natCast, Nat.mod_eq_of_lt hi]
  · intro k _
    rfl

/-- [proved-standard; formal-checked] If the values of a character of `ZMod m` are the `m`-th roots
of unity, `∏_k (1 − ψ k · u) = 1 − u^m`. -/
theorem prod_one_sub_mul_of_prod_sub {ψ : AddChar (ZMod m) F}
    (hψ : ∀ x, ∏ k, (x - ψ k) = x ^ m - 1) (u : F) :
    ∏ k, (1 - ψ k * u) = 1 - u ^ m := by
  have hm : 0 < m := NeZero.pos m
  have h1 : ∀ x : F, (∏ k, ψ k) * ∏ k, (1 - ψ (-k) * x) = (-1) ^ m * (x ^ m - 1) := by
    intro x
    have hk : ∀ k, ψ k * (1 - ψ (-k) * x) = (-1) * (x - ψ k) := by
      intro k
      have : ψ k * ψ (-k) = 1 := by
        rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
      linear_combination (-x) * this
    rw [← Finset.prod_mul_distrib, Finset.prod_congr rfl fun k _ => hk k, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_univ, ZMod.card, hψ x]
  have h0 := h1 0
  simp only [mul_zero, sub_zero, Finset.prod_const_one, mul_one, zero_pow hm.ne', zero_sub] at h0
  have hneg : ∏ k, (1 - ψ k * u) = ∏ k, (1 - ψ (-k) * u) :=
    (Fintype.prod_equiv (Equiv.neg (ZMod m)) _ _ fun k => by simp).symm
  have hu := h1 u
  rw [h0, ← hneg] at hu
  have hz : (-1 : F) ^ m * (∏ k, (1 - ψ k * u) - (1 - u ^ m)) = 0 := by
    linear_combination (-1) * hu
  rcases mul_eq_zero.mp hz with h | h
  · exact absurd h (pow_ne_zero _ (by norm_num))
  · exact sub_eq_zero.mp h

/-- [proved-derived; formal-checked] **The closed chain of `m` contacts** (A5).  The `m`-sheeted
cover of one loop by `ZMod m` with voltage `1` is the cycle of `m` contacts, and its dart
determinant is `(1 − u^m)²`: two prime closed walks of length `m`, one each sense. -/
theorem cycle_det (hζ : IsPrimitiveRoot ζ m) (u : F) :
    (1 - u • hashimoto F (coverA (G := ZMod m) (fun _ : Unit => ()))
        (coverB (fun _ : Unit => ()) (Sum.elim (fun _ => (1 : ZMod m)) (fun _ => -1)))).det =
      (1 - u ^ m) ^ 2 := by
  have hψ := AddChar.zmodChar_primitive_of_primitive_root m hζ
  have hG : (Fintype.card (ZMod m) : F) ≠ 0 := by
    rw [ZMod.card]
    exact (hζ.neZero').out
  have hσ : ∀ d : Unit ⊕ Unit,
      (Sum.elim (fun _ => (1 : ZMod m)) (fun _ => -1)) d.swap =
        -(Sum.elim (fun _ => (1 : ZMod m)) (fun _ => -1)) d := by
    rintro (_ | _) <;> simp
  rw [artin_abelian_cover_hashimoto _ _ hψ hG _ hσ u]
  have hprod := prod_one_sub_mul_of_prod_sub (prod_sub_zmodChar hζ) u
  have hprod' : ∏ k : ZMod m, (1 - AddChar.zmodChar m hζ.pow_eq_one (-k) * u) = 1 - u ^ m := by
    rw [← hprod]
    exact Fintype.prod_equiv (Equiv.neg (ZMod m)) _ _ fun k => by simp
  rw [show (1 - u ^ m) ^ 2 = (∏ k : ZMod m, (1 - AddChar.zmodChar m hζ.pow_eq_one k * u)) *
      ∏ k : ZMod m, (1 - AddChar.zmodChar m hζ.pow_eq_one (-k) * u) by rw [hprod, hprod', sq],
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [det_hashimotoC_loop]
  simp [twist]

end Cycle

section Audit

#print axioms charTableInv_mul_charTable
#print axioms charFrame_det_ne_zero
#print axioms charTable_mul_charTableInv
#print axioms charFrameInv_mul_charFrame
#print axioms charFrame_mul_charFrameInv
#print axioms coverHashimoto_mul_charFrame
#print axioms cover_mul_charFrame
#print axioms artin_abelian_cover
#print axioms twist_connection
#print axioms artin_abelian_cover_ihara_bass
#print axioms artin_abelian_cover_base
#print axioms base_dvd_cover
#print axioms hashimoto_cover
#print axioms artin_abelian_cover_hashimoto
#print axioms loopCover_det
#print axioms prod_sub_zmodChar
#print axioms prod_one_sub_mul_of_prod_sub
#print axioms cycle_det

end Audit

end Holonics.Landmarks.IharaAbelianCover
