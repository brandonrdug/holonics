import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

/-!
# The causal chord: transfer function, rate form, and the atlas one spectrum cannot supply

[definition] This owner states the law of the causal chord. Its Rust realization,
`crates/holonics/src/receiver/causal_chord.rs`, had no library caller after `hnn::modes` retired and
was retired at THE_REBUILD U3's second loop (September 28; [history](https://github.com/brandonrdug/holonics/blob/c10acca9/crates/holonics/src/receiver/causal_chord.rs)); the laws
only it carried (the Faddeev–LeVerrier construction and its coefficientwise certificate,
cancellation, poles named by their factors, residues, the resolvent's index and the six-vertex
cospectral pair) are in `docs/RECEIVER_HOLARCHY.md`, "The causal chord". It is receiver **R1** of
`docs/plans/THE_RECEIVER_ATLAS_SEPARATES_WHAT_ONE_FACE_CANNOT.md` and it formalizes the rate-form
algebra of `research/records/2026-09-15_INTEGRATING_AND_DIFFERENTIATING_ROLES_SHARE_ONE_CURRENT.md`
§"The critical seam is the `Sigma_G = 0` case". Four things are stated here, in this order.

1. **The transfer function over a field.** A `Linearization` is the triple `(A, B, C)` of the plan's
   `x' = A x + B u`, `y = C x`, carried as `state`/`excitation`/`readout` so that no field name
   collides with `Polynomial.C`. `numerator` is `C · adj(sI − A) · B` and `denominator` is
   `A.charpoly`; `transfer` is their quotient in `RatFunc K`. `resolvent_identity` is the statement
   that this quotient really is `C (sI − A)⁻¹ B`: `charmatrix A * adjugate (charmatrix A)` is
   `charpoly A • 1` exactly. `denominator_ne_zero` holds because the characteristic polynomial is
   monic, and `denominator_smul_transfer_eq_numerator` is **poles ⊆ eigenvalues**: clearing one
   copy of `denominator` already returns a polynomial matrix, so the denominator of every entry
   divides the characteristic polynomial and no pole sits outside the spectrum.
2. **The chart-change law.** `rebase` is the plan's rebase equivariance: conjugating the state by a
   unit and moving the excitation and readout along with it. `rebase_denominator`,
   `rebase_numerator` and `rebase_transfer` prove the whole transfer object is invariant, so the
   chord is a property of the current and not of the coordinates. The chart lemmas
   `adjugate_eq_det_smul_right`, `adjugate_conj`, `charmatrix_conj` and `charpoly_conj` carry the
   conjugation through `adjugate`, through `Polynomial.C` and through the determinant; they are
   stated for a two-sided inverse pair rather than for a `Units` coercion, which is the same
   hypothesis with none of the coercion ambiguity.
3. **Cancellation is visible, not lost.** `cancellation_is_strict` exhibits a diagonal
   `Linearization` over `ℚ` in which `2` is an eigenvalue — a root of `denominator` — and is *not*
   a pole, because the mode it names is neither excited by `excitation` nor observed by `readout`.
   The inclusion "poles ⊆ eigenvalues" is therefore strict, and the reduced denominator
   `X − C 1` is exhibited with a nonzero value at `2`.
4. **The chord survives the release.** A chart `V`, any `r × n` matrix, with `V A = Ā V`,
   `V B = B̄` and `C = C̄ V` leaves the transfer object unchanged,
   `C(sI − A)⁻¹B = C̄(sI − Ā)⁻¹B̄` (`transfer_descend`). The characteristic matrices intertwine
   (`charmatrix_intertwine`), so the resolvents do, `(sI − Ā)⁻¹V = V(sI − A)⁻¹`, and
   `transfer_eq_resolvent` reads the transfer object as `C(sI − A)⁻¹B` in `RatFunc K`. Hence
   `det(sI − Ā)` already clears every entry of the full chord (`descended_denominator_clears`);
   when `V` is onto, `det(sI − Ā)` divides `det(sI − A)` (`charpoly_dvd_of_quotient`: in a basis
   adapted to `ker V`, `Basis.sumQuot`, the matrix is block triangular with `Ā` as its quotient
   block), so the release removes only factors of `det(sI − A)` that every entry cancels
   (`release_cancels`). This is the mode quotient's descended chord (`HNN/ModeQuotient` item 3,
   `docs/HNN_FORMULA.md`, "The chord survives the release"), which the retired Rust test
   `the_chord_survives_the_release` (`hnn/tests/modes.rs`, history at `1bdacc8f`) checked entry by
   entry in lowest terms on exact fixtures.

[proved-derived; formal-checked] **The rate form.** `rateForm A G = Aᴴ G + G A` is the constant-`G`
case of the record's `Sigma_G = A*G + GA + G'`. `rateForm_congruence` is the record's
`Sigma_(G') = B^-* Sigma_G B^-1` exactly: the form transforms by congruence under a constant
invertible chart, which is why its signature and not the eigenvalues of `A` is the invariant
content of a situated role. `seam_iff_gSkew` is the record's `Sigma_G = 0 ⟺ L*G + GL = G`, obtained
by centering at one half. `gSkew_eigenvalue_re_eq_zero` proves that a `G`-skew generator with
positive definite `G` has purely imaginary spectrum, and `seam_eigenvalue_re_eq_half` is the seam
corollary `Re λ = 1/2`. That direction is unconditional.

[proved-derived; formal-checked] `semisimple_imaginary_has_conserving_receiver` supplies the
provable direction of the plan's biconditional: for `A = S D S⁻¹` with every `d i` purely
imaginary, `G = S⁻ᴴ S⁻¹` is positive definite and `rateForm A G = 0`.

[proved-derived; formal-checked] **The correction the plan requires.**
`jordan_has_no_conserving_receiver` shows the naive converse is false. `jordanI = !![I, 1; 0, I]`
has `jordan_eigenvalue_eq_I`: its only eigenvalue is `I`, purely imaginary, so `L = jordanI + I/2`
sits on the seam spectrally; yet no positive definite `G` makes `rateForm jordanI G = 0`, because
the `(1,0)` entry of that form is exactly `G 0 0`, which a positive definite `G` keeps strictly
positive. Purely imaginary spectrum does **not** give a conserving receiver: **semisimplicity is
the dropped hypothesis**, and a defective generator sits on the seam spectrally with no conserving
receiver at all. This is why the plan reads response through the resolvent and not through the
spectrum.

[definition] The remaining direction — "`A` is `G`-skew for some positive definite `G` ⟹ `A` is
semisimple" — is **not** formalized here, and is not asserted anywhere below. It needs the spectral
theorem for skew-adjoint operators transported through `G^{1/2}`: one must build the positive
square root of `G`, conjugate by it to obtain a skew-Hermitian matrix, and invoke unitary
diagonalizability. None of that is rate algebra, and stating it without the construction would be
exactly the dropped hypothesis this file exists to name.

[proved-derived; formal-checked] **The atlas.** `spectrum_does_not_determine_response` exhibits two
linearizations over `ℚ` with the same characteristic polynomial `X²` and different numerators: this
is the plan's governing correction, that isospectral objects exist and identity is carried by the
organized family of responses under admitted probes, not by one global spectrum. The retired Rust
owner's `separate_under_probe` exhibited the same phenomenon on a genuine pair of
Laplacian-cospectral non-isomorphic graphs on six vertices, separated at thirty-two of the
thirty-six probe/readout pairs (the pair and its numerators are kept in `docs/RECEIVER_HOLARCHY.md`);
the 2×2 witness here is the minimal one a kernel can check.
`full_atlas_determines_the_operator_fin_two` is the positive counterpart at `Fin 2`: the
*complete* probe/readout atlas — every entry of `adjugate (charmatrix A)`, which is the numerator
for every pair of coordinate probe and coordinate readout — does determine the operator. It is
stated and proved at `Fin 2` only; the general statement is true but needs the cofactor expansion
of `adjugate (charmatrix A)` in degree `n − 2`, which is not done here, and the name records the
restriction.

Retired Rust owner ([history at `c10acca9`](https://github.com/brandonrdug/holonics/blob/c10acca9/crates/holonics/src/receiver/causal_chord.rs)):
`crates/holonics/src/receiver/causal_chord.rs`
(`Linearization` ↔ `Linearization`; `transfer_function` and `TransferFunction` ↔ `numerator`,
`denominator`, `transfer`, `denominator_smul_transfer_eq_numerator`; `ResolventExpansion` ↔
`resolvent_identity`; `causal_chord` and `CausalChord` ↔ `rebase_transfer`; `pole_atlas` and
`HalfPlaneCount` ↔ `cancellation_is_strict` and `seam_eigenvalue_re_eq_half`; `rate_form` ↔
`rateForm` and `rateForm_congruence`; `seam_form` ↔ `seam_iff_gSkew`; `is_semisimple` ↔
`semisimple_imaginary_has_conserving_receiver`; `resolvent_probe` and `jordan_realification` ↔
`jordan_eigenvalue_eq_I`; `conserving_receiver_space` ↔ `jordan_has_no_conserving_receiver` and
`semisimple_imaginary_has_conserving_receiver`; `separate_under_probe` ↔
`spectrum_does_not_determine_response` and `full_atlas_determines_the_operator_fin_two`).
-/

noncomputable section

namespace Holonics.Foundation.CausalChord

open Matrix Polynomial

/-! ## The chart

A chart is a two-sided inverse pair `U V = 1`, `V U = 1`. These four lemmas carry such a pair
through `adjugate`, through the coefficient embedding `Polynomial.C` and through the determinant,
which is what makes the whole transfer object chart-invariant. They hold over any commutative ring.
-/

section Chart

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- [proved-derived; formal-checked] For an invertible matrix the adjugate is the determinant times
the inverse. This is the only fact about `adjugate` a chart change needs. -/
theorem adjugate_eq_det_smul_right {U V : Matrix ι ι R} (h : V * U = 1) :
    Matrix.adjugate U = U.det • V := by
  calc Matrix.adjugate U = V * U * Matrix.adjugate U := by rw [h, Matrix.one_mul]
    _ = V * (U * Matrix.adjugate U) := by rw [Matrix.mul_assoc]
    _ = V * (U.det • (1 : Matrix ι ι R)) := by rw [Matrix.mul_adjugate]
    _ = U.det • V := by rw [Matrix.mul_smul, Matrix.mul_one]

/-- [proved-derived; formal-checked] The adjugate is equivariant under conjugation by a chart: the
two determinant factors are mutually inverse and cancel. -/
theorem adjugate_conj {U V M : Matrix ι ι R} (h₁ : U * V = 1) (h₂ : V * U = 1) :
    Matrix.adjugate (U * M * V) = U * Matrix.adjugate M * V := by
  have hU : Matrix.adjugate U = U.det • V := adjugate_eq_det_smul_right h₂
  have hV : Matrix.adjugate V = V.det • U := adjugate_eq_det_smul_right h₁
  have hdet : U.det * V.det = 1 := by rw [← Matrix.det_mul, h₁, Matrix.det_one]
  rw [Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib, hU, hV]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc, hdet, one_smul]

/-- [proved-derived; formal-checked] The characteristic matrix of a conjugate is the conjugate of
the characteristic matrix, in the polynomial chart. The scalar part `X • 1` is central, so it
passes through untouched. -/
theorem charmatrix_conj {U V M : Matrix ι ι R} (h₁ : U * V = 1) :
    Matrix.charmatrix (U * M * V)
      = U.map Polynomial.C * Matrix.charmatrix M * V.map Polynomial.C := by
  have hmap : U.map Polynomial.C * V.map Polynomial.C = 1 := by
    rw [← Matrix.map_mul, h₁]; simp
  have hcentral : U.map Polynomial.C * Matrix.scalar ι (Polynomial.X : R[X])
      * V.map Polynomial.C = Matrix.scalar ι (Polynomial.X : R[X]) := by
    rw [Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul, hmap]
  have hconj : U.map Polynomial.C * M.map Polynomial.C * V.map Polynomial.C
      = (U * M * V).map Polynomial.C := by simp [Matrix.map_mul]
  simp only [Matrix.charmatrix, RingHom.mapMatrix_apply, Matrix.mul_sub, Matrix.sub_mul, hcentral,
    hconj]

/-- [proved-derived; formal-checked] The characteristic polynomial is a chart invariant: the
spectrum belongs to the current, not to the coordinates. -/
theorem charpoly_conj {U V M : Matrix ι ι R} (h₂ : V * U = 1) :
    (U * M * V).charpoly = M.charpoly := by
  rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, h₂, Matrix.one_mul]

end Chart

/-! ## A quotient's characteristic polynomial divides the whole's -/

section Quotient

variable {K : Type*} [Field K] {n r : ℕ}

/-- [proved-standard; formal-checked] **A quotient's characteristic polynomial divides the
whole's.** If `V` is onto and `V T = S V`, then `ker V` is carried by `T`; in a basis of `K^n`
adapted to `ker V` (`Module.Basis.sumQuot`, a basis of the kernel followed by lifts of a basis of
the quotient, which `V` identifies with `K^r`) the matrix of `T` is block triangular with `S` as its
quotient block, so `charpoly T = charpoly(T on ker V) · charpoly S`. -/
theorem charpoly_dvd_of_quotient (V : Matrix (Fin r) (Fin n) K)
    (hV : Function.Surjective V.mulVec) {T : Matrix (Fin n) (Fin n) K}
    {S : Matrix (Fin r) (Fin r) K} (h : V * T = S * V) : S.charpoly ∣ T.charpoly := by
  set Vl : (Fin n → K) →ₗ[K] (Fin r → K) := Matrix.toLin' V
  set f : (Fin n → K) →ₗ[K] (Fin n → K) := Matrix.toLin' T
  have hVl : Function.Surjective Vl := hV
  set W := LinearMap.ker Vl
  have hinv : ∀ v ∈ W, f v ∈ W := by
    intro v hv
    simp only [W, LinearMap.mem_ker, Vl, f, Matrix.toLin'_apply] at hv ⊢
    rw [mulVec_mulVec, h, ← mulVec_mulVec, hv, mulVec_zero]
  let e : ((Fin n → K) ⧸ W) ≃ₗ[K] (Fin r → K) := Vl.quotKerEquivOfSurjective hVl
  let bW := Module.finBasis K W
  let bQ : Module.Basis (Fin r) K ((Fin n → K) ⧸ W) := (Pi.basisFun K (Fin r)).map e.symm
  let b := Module.Basis.sumQuot bW bQ
  set M := LinearMap.toMatrix b b f
  have hM : M.charpoly = T.charpoly := by
    rw [LinearMap.charpoly_toMatrix, Matrix.charpoly_toLin']
  have h21 : M.toBlocks₂₁ = 0 := by
    ext i j
    simp only [toBlocks₂₁, of_apply, Matrix.zero_apply, M, LinearMap.toMatrix_apply]
    rw [Module.Basis.sumQuot_inl]
    exact Module.Basis.sumQuot_repr_inr_of_mem bW bQ _ (hinv _ (bW j).2) i
  have hVb : ∀ j, V *ᵥ b (Sum.inr j) = Pi.single j 1 := by
    intro j
    have h1 : e (Submodule.Quotient.mk (b (Sum.inr j))) = Vl (b (Sum.inr j)) :=
      Vl.quotKerEquivOfSurjective_apply_mk hVl _
    rw [Module.Basis.sumQuot_inr] at h1
    simp only [bQ, Module.Basis.map_apply, LinearEquiv.apply_symm_apply, Pi.basisFun_apply] at h1
    rw [← Matrix.toLin'_apply]
    exact h1.symm
  have h22 : M.toBlocks₂₂ = S := by
    ext i j
    simp only [toBlocks₂₂, of_apply, M, LinearMap.toMatrix_apply]
    rw [Module.Basis.sumQuot_repr_inr]
    simp only [bQ, Module.Basis.map_repr, LinearEquiv.trans_apply, LinearEquiv.symm_symm,
      Pi.basisFun_repr, Submodule.mkQ_apply]
    rw [show e (Submodule.Quotient.mk (f (b (Sum.inr j)))) = Vl (f (b (Sum.inr j))) from
      Vl.quotKerEquivOfSurjective_apply_mk hVl _]
    simp only [Vl, f, Matrix.toLin'_apply]
    rw [mulVec_mulVec, h, ← mulVec_mulVec, hVb, mulVec_single_one]
    rfl
  rw [← hM, ← Matrix.fromBlocks_toBlocks M, h21, h22, Matrix.charpoly_fromBlocks_zero₂₁]
  exact Dvd.intro_left _ rfl

end Quotient

/-! ## The transfer function over a field -/

/-- [definition] A local linearization `x' = A x + B u`, `y = C x`. The three fields are named
`state`, `excitation` and `readout` rather than `A`, `B`, `C` precisely because `C` is the
coefficient embedding `Polynomial.C` that every statement below uses. -/
structure Linearization (K : Type*) [Field K] (n m p : ℕ) where
  /-- `A`: the generator of the free motion. -/
  state : Matrix (Fin n) (Fin n) K
  /-- `B`: which modes an admitted source can excite. -/
  excitation : Matrix (Fin n) (Fin m) K
  /-- `C`: which modes an admitted receiver can observe. -/
  readout : Matrix (Fin p) (Fin n) K

namespace Linearization

variable {K : Type*} [Field K] {n m p : ℕ}

/-- [definition] The polynomial numerator `C · adj(sI − A) · B` of the transfer object. -/
def numerator (L : Linearization K n m p) : Matrix (Fin p) (Fin m) K[X] :=
  L.readout.map Polynomial.C * (Matrix.charmatrix L.state).adjugate
    * L.excitation.map Polynomial.C

/-- [definition] The polynomial denominator `det(sI − A)`: the characteristic polynomial. -/
def denominator (L : Linearization K n m p) : K[X] := L.state.charpoly

/-- [definition] The transfer object `H(s) = C (sI − A)⁻¹ B` as a matrix of rational functions. -/
def transfer (L : Linearization K n m p) : Matrix (Fin p) (Fin m) (RatFunc K) :=
  (algebraMap K[X] (RatFunc K) L.denominator)⁻¹ •
    (L.numerator).map (algebraMap K[X] (RatFunc K))

/-- [proved-derived; formal-checked] **The resolvent identity.**
`(sI − A) · adj(sI − A) = det(sI − A) · I`. This is exactly the statement that
`numerator / denominator` *is* `C (sI − A)⁻¹ B`: the adjugate divided by the characteristic
polynomial is the resolvent, with no inversion and no invertibility hypothesis anywhere. -/
theorem resolvent_identity (A : Matrix (Fin n) (Fin n) K) :
    Matrix.charmatrix A * (Matrix.charmatrix A).adjugate = A.charpoly • 1 := by
  rw [Matrix.charpoly]
  exact Matrix.mul_adjugate _

/-- [proved-derived; formal-checked] The denominator never vanishes: the characteristic polynomial
is monic, so the transfer object is always defined. -/
theorem denominator_ne_zero (L : Linearization K n m p) : L.denominator ≠ 0 :=
  (Matrix.charpoly_monic L.state).ne_zero

/-- [proved-derived; formal-checked] **Poles are contained in eigenvalues.** Clearing a single copy
of the characteristic polynomial already returns a polynomial matrix, so the denominator of every
entry of `transfer` divides `denominator = A.charpoly`. No response pole sits outside the spectrum
of the generator. -/
theorem denominator_smul_transfer_eq_numerator (L : Linearization K n m p) :
    (algebraMap K[X] (RatFunc K) L.denominator) • L.transfer
      = (L.numerator).map (algebraMap K[X] (RatFunc K)) := by
  rw [transfer, smul_smul, mul_inv_cancel₀ (RatFunc.algebraMap_ne_zero L.denominator_ne_zero),
    one_smul]

/-! ### The chart-change law -/

/-- [definition] Rebasing a linearization by an invertible chart `T`: the state is conjugated, the
excitation is pushed forward and the readout is pulled back. -/
def rebase (T : (Matrix (Fin n) (Fin n) K)ˣ) (L : Linearization K n m p) :
    Linearization K n m p where
  state := T.val * L.state * T.inv
  excitation := T.val * L.excitation
  readout := L.readout * T.inv

@[simp]
theorem rebase_state (T : (Matrix (Fin n) (Fin n) K)ˣ) (L : Linearization K n m p) :
    (rebase T L).state = T.val * L.state * T.inv := rfl

@[simp]
theorem rebase_excitation (T : (Matrix (Fin n) (Fin n) K)ˣ) (L : Linearization K n m p) :
    (rebase T L).excitation = T.val * L.excitation := rfl

@[simp]
theorem rebase_readout (T : (Matrix (Fin n) (Fin n) K)ˣ) (L : Linearization K n m p) :
    (rebase T L).readout = L.readout * T.inv := rfl

/-- [proved-derived; formal-checked] The spectrum is a chart invariant. -/
theorem rebase_denominator (T : (Matrix (Fin n) (Fin n) K)ˣ) (L : Linearization K n m p) :
    (rebase T L).denominator = L.denominator :=
  charpoly_conj T.inv_val

/-- [proved-derived; formal-checked] **The numerator is a chart invariant.** The two copies of the
chart introduced by the readout and the excitation cancel exactly the two copies that the adjugate
of the conjugated characteristic matrix carries. -/
theorem rebase_numerator (T : (Matrix (Fin n) (Fin n) K)ˣ) (L : Linearization K n m p) :
    (rebase T L).numerator = L.numerator := by
  have hVU : T.inv.map Polynomial.C * T.val.map Polynomial.C = 1 := by
    rw [← Matrix.map_mul, T.inv_val]; simp
  have hUV : T.val.map Polynomial.C * T.inv.map Polynomial.C = 1 := by
    rw [← Matrix.map_mul, T.val_inv]; simp
  have hcancel : ∀ {q : ℕ} (Y : Matrix (Fin n) (Fin q) K[X]),
      T.inv.map Polynomial.C * (T.val.map Polynomial.C * Y) = Y := by
    intro q Y
    rw [← Matrix.mul_assoc, hVU, Matrix.one_mul]
  rw [numerator, numerator, rebase_state, rebase_excitation, rebase_readout,
    charmatrix_conj T.val_inv, adjugate_conj hUV hVU]
  simp only [Matrix.map_mul, Matrix.mul_assoc, hcancel]

/-- [proved-derived; formal-checked] **The whole transfer object is a chart invariant.** This is
the plan's rebase equivariance: the causal chord belongs to the current, not to the coordinates
in which it is written. -/
theorem rebase_transfer (T : (Matrix (Fin n) (Fin n) K)ˣ) (L : Linearization K n m p) :
    (rebase T L).transfer = L.transfer := by
  rw [transfer, transfer, rebase_denominator, rebase_numerator]

/-! ### The chord survives the release -/

/-- [proved-derived; formal-checked] **The transfer object is the resolvent.** In `RatFunc K`,
`transfer = C (sI − A)⁻¹ B` with the characteristic matrix inverted: the adjugate over the
determinant is the inverse once both are read as rational functions. -/
theorem transfer_eq_resolvent (L : Linearization K n m p) :
    L.transfer = (L.readout.map Polynomial.C).map (algebraMap K[X] (RatFunc K))
      * ((Matrix.charmatrix L.state).map (algebraMap K[X] (RatFunc K)))⁻¹
      * (L.excitation.map Polynomial.C).map (algebraMap K[X] (RatFunc K)) := by
  set φ := algebraMap K[X] (RatFunc K)
  rw [Matrix.inv_def, Ring.inverse_eq_inv, transfer, numerator, denominator, Matrix.charpoly,
    Matrix.map_mul, Matrix.map_mul]
  have hdet : φ (Matrix.charmatrix L.state).det
      = ((Matrix.charmatrix L.state).map φ).det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
  have hadj : ((Matrix.charmatrix L.state).adjugate).map φ
      = ((Matrix.charmatrix L.state).map φ).adjugate := by
    rw [← RingHom.mapMatrix_apply, RingHom.map_adjugate, RingHom.mapMatrix_apply]
  rw [hdet, hadj, Matrix.mul_smul, Matrix.smul_mul]

/-- [proved-derived; formal-checked] **A chart that closes the square intertwines the
characteristic matrices**: `V T = S V` gives `V (sI − T) = (sI − S) V` in the polynomial chart,
for a rectangular `V`. -/
theorem charmatrix_intertwine {r : ℕ} (V : Matrix (Fin r) (Fin n) K)
    {T : Matrix (Fin n) (Fin n) K} {S : Matrix (Fin r) (Fin r) K} (h : V * T = S * V) :
    V.map Polynomial.C * Matrix.charmatrix T = Matrix.charmatrix S * V.map Polynomial.C := by
  have hscal : ∀ {a b : ℕ} (W : Matrix (Fin a) (Fin b) K[X]),
      W * Matrix.scalar (Fin b) (X : K[X]) = Matrix.scalar (Fin a) (X : K[X]) * W := by
    intro a b W
    rw [Matrix.scalar_apply, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal,
      ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.one_mul]
  have hmap : V.map Polynomial.C * T.map Polynomial.C = S.map Polynomial.C * V.map Polynomial.C := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, h]
  simp only [Matrix.charmatrix, RingHom.mapMatrix_apply, Matrix.mul_sub, Matrix.sub_mul, hscal,
    hmap]

/-- [proved-derived; formal-checked] **`transfer_descend`: the chord survives the release.** A
chart `V : K^n → K^r` with `V A = Ā V`, `V B = B̄` and `C = C̄ V` leaves the whole transfer object
unchanged, `C (sI − A)⁻¹ B = C̄ (sI − Ā)⁻¹ B̄`: the resolvents intertwine,
`(sI − Ā)⁻¹ V = V (sI − A)⁻¹`, and the chart is absorbed by the excitation on one side and the
readout on the other. `V` need not be onto; at `r = 0` both sides are zero. -/
theorem transfer_descend {r : ℕ} (L : Linearization K n m p) (L' : Linearization K r m p)
    (V : Matrix (Fin r) (Fin n) K) (hT : V * L.state = L'.state * V)
    (hB : V * L.excitation = L'.excitation) (hρ : L.readout = L'.readout * V) :
    L.transfer = L'.transfer := by
  set φ := algebraMap K[X] (RatFunc K)
  set M := (Matrix.charmatrix L.state).map φ
  set M' := (Matrix.charmatrix L'.state).map φ
  set W := (V.map Polynomial.C).map φ
  have hM : IsUnit M.det := by
    rw [isUnit_iff_ne_zero, show M.det = φ (Matrix.charmatrix L.state).det by
      rw [RingHom.map_det, RingHom.mapMatrix_apply]]
    exact RatFunc.algebraMap_ne_zero L.denominator_ne_zero
  have hM' : IsUnit M'.det := by
    rw [isUnit_iff_ne_zero, show M'.det = φ (Matrix.charmatrix L'.state).det by
      rw [RingHom.map_det, RingHom.mapMatrix_apply]]
    exact RatFunc.algebraMap_ne_zero L'.denominator_ne_zero
  have hWM : W * M = M' * W := by
    simp only [W, M, M', ← Matrix.map_mul, charmatrix_intertwine V hT]
  have hcomm : W * M⁻¹ = M'⁻¹ * W := by
    calc W * M⁻¹ = M'⁻¹ * M' * W * M⁻¹ := by rw [Matrix.nonsing_inv_mul _ hM', Matrix.one_mul]
      _ = M'⁻¹ * (W * M) * M⁻¹ := by rw [hWM]; simp only [Matrix.mul_assoc]
      _ = M'⁻¹ * W := by rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hM,
            Matrix.mul_one]
  rw [transfer_eq_resolvent, transfer_eq_resolvent, hρ, ← hB]
  simp only [Matrix.map_mul]
  change _ * W * M⁻¹ * _ = _ * M'⁻¹ * (W * _)
  rw [Matrix.mul_assoc _ W, hcomm]
  simp only [Matrix.mul_assoc]

/-- [proved-derived; formal-checked] **The descended denominator clears the full chord.** Under the
hypotheses of `transfer_descend`, one copy of `det(sI − Ā)` turns every entry of the full ring's
transfer object into the descended numerator, a polynomial: no pole of the full chord lies outside
the spectrum of `Ā`. -/
theorem descended_denominator_clears {r : ℕ} (L : Linearization K n m p)
    (L' : Linearization K r m p) (V : Matrix (Fin r) (Fin n) K)
    (hT : V * L.state = L'.state * V) (hB : V * L.excitation = L'.excitation)
    (hρ : L.readout = L'.readout * V) :
    (algebraMap K[X] (RatFunc K) L'.denominator) • L.transfer
      = (L'.numerator).map (algebraMap K[X] (RatFunc K)) := by
  rw [transfer_descend L L' V hT hB hρ, denominator_smul_transfer_eq_numerator]

/-- [proved-derived; formal-checked] **`release_cancels`: the release removes only factors every
entry cancels.** When the chart `V` is onto (a release of `ker V`), `det(sI − A)` is
`det(sI − Ā)` times the released factor `R` (`charpoly_dvd_of_quotient`), and `det(sI − Ā)` alone
already clears every entry of the full chord (`descended_denominator_clears`): the factor `R` is
cancelled by every entry. -/
theorem release_cancels {r : ℕ} (L : Linearization K n m p) (L' : Linearization K r m p)
    (V : Matrix (Fin r) (Fin n) K) (hV : Function.Surjective V.mulVec)
    (hT : V * L.state = L'.state * V) (hB : V * L.excitation = L'.excitation)
    (hρ : L.readout = L'.readout * V) :
    (∃ R : K[X], L.denominator = L'.denominator * R) ∧
      (algebraMap K[X] (RatFunc K) L'.denominator) • L.transfer
        = (L'.numerator).map (algebraMap K[X] (RatFunc K)) :=
  ⟨charpoly_dvd_of_quotient V hV hT, descended_denominator_clears L L' V hT hB hρ⟩

/-! ### Cancellation is visible, not lost -/

/-- [definition] Two decoupled rational modes at `1` and `2`, of which only the first is excited
and only the first is observed. -/
def cancellingWitness : Linearization ℚ 2 1 1 where
  state := Matrix.diagonal ![1, 2]
  excitation := !![1; 0]
  readout := !![1, 0]

/-- [proved-derived; formal-checked] Its denominator is the full characteristic polynomial: both
`1` and `2` are eigenvalues. -/
theorem cancellingWitness_denominator :
    cancellingWitness.denominator = (X - C 1) * (X - C 2) := by
  rw [denominator]
  show (Matrix.diagonal ![(1 : ℚ), 2]).charpoly = _
  rw [Matrix.charpoly_diagonal, Fin.prod_univ_two]
  simp

/-- [proved-derived; formal-checked] Its numerator carries only the observed and excited mode: the
factor `X − C 2` survives, so the mode at `2` cancels. -/
theorem cancellingWitness_numerator :
    cancellingWitness.numerator 0 0 = X - C 2 := by
  have herase : (Finset.univ.erase (0 : Fin 2)) = {1} := by decide
  simp [numerator, cancellingWitness, Matrix.mul_apply, Fin.sum_univ_two, herase]

/-- [proved-derived; formal-checked] **The inclusion "poles ⊆ eigenvalues" is strict.** `2` is a
root of `denominator`, so it is an eigenvalue of the generator; but it is cancelled by the
numerator, and the reduced denominator `X − C 1` does not vanish at `2`, so `2` is not a pole of
the response. The mode at `2` is neither excited by `excitation` nor observed by `readout`, and the
cancellation is exhibited — the factorization is returned, not silently lost. -/
theorem cancellation_is_strict :
    cancellingWitness.denominator = (X - C 1) * cancellingWitness.numerator 0 0
      ∧ cancellingWitness.denominator.eval 2 = 0
      ∧ (X - C (1 : ℚ)).eval 2 ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [cancellingWitness_denominator, cancellingWitness_numerator]
  · rw [cancellingWitness_denominator]; simp
  · norm_num

end Linearization

/-! ## The rate form over `ℂ` -/

section Rate

open scoped ComplexOrder

variable {n : ℕ}

/-- [definition] The constant-metric rate form `Sigma_G = A* G + G A` of the record. With a moving
metric the record's third term `G'` is added; that term is not carried here because every statement
below fixes `G`. The moving-metric law with forcing is `Geometry/Motion.energy_rate_moving_metric`
(algebraic form) and `Holon/Deposition.learned_energy_balance` (its dynamical owner in the
Holon's quadratic port chart); `rateForm` is their `Ġ = 0`, `f = 0` reading over `ℂ`. -/
def rateForm (A G : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := Aᴴ * G + G * A

/-- [proved-derived; formal-checked] **The rate form transforms by congruence**, which is the
record's `Sigma_(G') = B^-* Sigma_G B^-1`. The reading `x* G x` and the form are therefore
chart-independent up to congruence, which is the exact reason the *signature* of `Sigma_G` — and
not the eigenvalues of `A` — is the invariant content of a situated role. -/
theorem rateForm_congruence (T : (Matrix (Fin n) (Fin n) ℂ)ˣ)
    (A G : Matrix (Fin n) (Fin n) ℂ) :
    rateForm (T.val * A * T.inv) (T.invᴴ * G * T.inv) = T.invᴴ * rateForm A G * T.inv := by
  have hL : ∀ Y : Matrix (Fin n) (Fin n) ℂ, T.valᴴ * (T.invᴴ * Y) = Y := by
    intro Y
    rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, T.inv_val, Matrix.conjTranspose_one,
      Matrix.one_mul]
  have hR : ∀ Y : Matrix (Fin n) (Fin n) ℂ, T.inv * (T.val * Y) = Y := by
    intro Y
    rw [← Matrix.mul_assoc, T.inv_val, Matrix.one_mul]
  simp only [rateForm, Matrix.conjTranspose_mul, Matrix.add_mul, Matrix.mul_add,
    Matrix.mul_assoc, hL, hR]

/-- [proved-derived; formal-checked] **The seam, after centering.** `Sigma_G = 0` for the centered
generator `A = L − I/2` is exactly the record's `L* G + G L = G`, because
`(L − I/2)* G + G (L − I/2) = L* G + G L − G`. The coefficient one half is the normalization that
separates one current into its invariant and anti-invariant parts. -/
theorem seam_iff_gSkew (L G : Matrix (Fin n) (Fin n) ℂ) :
    rateForm (L - (2⁻¹ : ℂ) • 1) G = 0 ↔ Lᴴ * G + G * L = G := by
  have hc : ((2⁻¹ : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ))ᴴ = (2⁻¹ : ℂ) • 1 := by
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
    norm_num
  have key : rateForm (L - (2⁻¹ : ℂ) • 1) G = Lᴴ * G + G * L - G := by
    simp only [rateForm, Matrix.conjTranspose_sub, hc, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
    module
  rw [key, sub_eq_zero]

/-- [proved-derived; formal-checked] **A `G`-skew generator has purely imaginary spectrum.** Pair
the vanishing rate form with an eigenvector against the metric: the two terms are `conj μ · q` and
`μ · q` with `q = v* G v > 0`, so `conj μ + μ = 0`. This direction is unconditional — no
semisimplicity, no normality, no diagonalizability. -/
theorem gSkew_eigenvalue_re_eq_zero {A G : Matrix (Fin n) (Fin n) ℂ}
    (hG : G.PosDef) (hA : rateForm A G = 0) {v : Fin n → ℂ} {μ : ℂ}
    (hv : v ≠ 0) (heig : A *ᵥ v = μ • v) : μ.re = 0 := by
  have hqpos : (0 : ℂ) < star v ⬝ᵥ (G *ᵥ v) := hG.dotProduct_mulVec_pos hv
  have hqne : star v ⬝ᵥ (G *ᵥ v) ≠ 0 := hqpos.ne'
  have h0 : star v ⬝ᵥ ((rateForm A G) *ᵥ v) = 0 := by rw [hA]; simp
  rw [rateForm, Matrix.add_mulVec, dotProduct_add] at h0
  have h1 : star v ⬝ᵥ ((Aᴴ * G) *ᵥ v) = (starRingEnd ℂ) μ * (star v ⬝ᵥ (G *ᵥ v)) := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, heig]
    simp [smul_dotProduct]
  have h2 : star v ⬝ᵥ ((G * A) *ᵥ v) = μ * (star v ⬝ᵥ (G *ᵥ v)) := by
    rw [← Matrix.mulVec_mulVec, heig, Matrix.mulVec_smul, dotProduct_smul]
    simp
  rw [h1, h2] at h0
  have hsum : ((starRingEnd ℂ) μ + μ) * (star v ⬝ᵥ (G *ᵥ v)) = 0 := by linear_combination h0
  have hconj : (starRingEnd ℂ) μ + μ = 0 := by
    rcases mul_eq_zero.mp hsum with h | h
    · exact h
    · exact absurd h hqne
  have hfin : μ + (starRingEnd ℂ) μ = 0 := by rw [add_comm]; exact hconj
  rw [Complex.add_conj] at hfin
  have hre := Complex.ofReal_eq_zero.mp hfin
  linarith

/-- [proved-derived; formal-checked] **The seam eigenvalue law.** If `L* G + G L = G` for a
positive definite `G`, every eigenvalue of `L` has real part one half. This is the corollary of
`seam_iff_gSkew` and `gSkew_eigenvalue_re_eq_zero` at `A = L − I/2`. -/
theorem seam_eigenvalue_re_eq_half {L G : Matrix (Fin n) (Fin n) ℂ} (hG : G.PosDef)
    (h : Lᴴ * G + G * L = G) {v : Fin n → ℂ} {μ : ℂ}
    (hv : v ≠ 0) (heig : L *ᵥ v = μ • v) : μ.re = 1 / 2 := by
  have hA : rateForm (L - (2⁻¹ : ℂ) • 1) G = 0 := (seam_iff_gSkew L G).mpr h
  have heig' : (L - (2⁻¹ : ℂ) • 1) *ᵥ v = (μ - 2⁻¹) • v := by
    rw [Matrix.sub_mulVec, heig, Matrix.smul_mulVec, Matrix.one_mulVec, sub_smul]
  have hre := gSkew_eigenvalue_re_eq_zero hG hA hv heig'
  have h2 : ((2 : ℂ)⁻¹).re = 1 / 2 := by
    rw [show ((2 : ℂ)⁻¹) = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.ofReal_re]
  rw [Complex.sub_re, h2] at hre
  linarith

/-- [proved-derived; formal-checked] **The provable direction of the plan's biconditional.** A
semisimple generator with purely imaginary spectrum does admit a conserving receiver: take
`G = S⁻ᴴ S⁻¹` for any diagonalizing chart `S`. Positive definiteness is the Gram form of an
injective map, and the rate form vanishes because a purely imaginary diagonal is skew. -/
theorem semisimple_imaginary_has_conserving_receiver
    (S : (Matrix (Fin n) (Fin n) ℂ)ˣ) (d : Fin n → ℂ) (hd : ∀ i, (d i).re = 0) :
    (S.invᴴ * S.inv).PosDef
      ∧ rateForm (S.val * Matrix.diagonal d * S.inv) (S.invᴴ * S.inv) = 0 := by
  have hinj : Function.Injective S.inv.mulVec := by
    intro x y hxy
    have h := congrArg (fun w => S.val *ᵥ w) hxy
    simpa [Matrix.mulVec_mulVec, S.val_inv] using h
  have hstar : star d = -d := by
    funext i
    have h := hd i
    apply Complex.ext <;> simp [h]
  have hDskew : (Matrix.diagonal d)ᴴ = -Matrix.diagonal d := by
    rw [Matrix.diagonal_conjTranspose, hstar, Matrix.diagonal_neg]
    rfl
  have hL : ∀ Y : Matrix (Fin n) (Fin n) ℂ, S.valᴴ * (S.invᴴ * Y) = Y := by
    intro Y
    rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, S.inv_val, Matrix.conjTranspose_one,
      Matrix.one_mul]
  have hR : ∀ Y : Matrix (Fin n) (Fin n) ℂ, S.inv * (S.val * Y) = Y := by
    intro Y
    rw [← Matrix.mul_assoc, S.inv_val, Matrix.one_mul]
  refine ⟨Matrix.PosDef.conjTranspose_mul_self _ hinj, ?_⟩
  simp only [rateForm, Matrix.conjTranspose_mul, hDskew, Matrix.neg_mul, Matrix.mul_neg,
    Matrix.mul_assoc, hL, hR, neg_add_cancel]

/-! ### The counterexample to the naive converse -/

/-- [definition] The defective generator `!![I, 1; 0, I]`. Its spectrum is purely imaginary, so
`L = jordanI + I/2` sits on the seam spectrally, but it is not semisimple. -/
def jordanI : Matrix (Fin 2) (Fin 2) ℂ := !![Complex.I, 1; 0, Complex.I]

/-- [proved-derived; formal-checked] `jordanI` has exactly one eigenvalue, `I`, which is purely
imaginary. Elementary: the second coordinate forces `μ = I` whenever the second component of the
eigenvector is nonzero, and otherwise the first component is nonzero and the first coordinate
forces `μ = I` again. -/
theorem jordan_eigenvalue_eq_I {v : Fin 2 → ℂ} {μ : ℂ}
    (hv : v ≠ 0) (heig : jordanI *ᵥ v = μ • v) : μ = Complex.I := by
  have e0 : Complex.I * v 0 + v 1 = μ * v 0 := by
    have h := congrFun heig 0
    simpa [jordanI, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.vecHead,
      Matrix.vecTail] using h
  have e1 : Complex.I * v 1 = μ * v 1 := by
    have h := congrFun heig 1
    simpa [jordanI, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.vecHead,
      Matrix.vecTail] using h
  by_cases h1 : v 1 = 0
  · have h0 : v 0 ≠ 0 := fun hz => hv (funext (Fin.forall_fin_two.mpr ⟨hz, h1⟩))
    have hmul : (Complex.I - μ) * v 0 = 0 := by linear_combination e0 - h1
    rcases mul_eq_zero.mp hmul with h | h
    · linear_combination -h
    · exact absurd h h0
  · have hmul : (Complex.I - μ) * v 1 = 0 := by linear_combination e1
    rcases mul_eq_zero.mp hmul with h | h
    · linear_combination -h
    · exact absurd h h1

/-- [proved-derived; formal-checked] **Purely imaginary spectrum does not give a conserving
receiver.** The `(1,0)` entry of `jordanIᴴ G + G jordanI` is exactly `G 0 0`, so a vanishing rate
form forces `G 0 0 = 0`, which no positive definite `G` allows.

This is the correction the plan requires. `jordanI` is spectrally on the seam —
`jordan_eigenvalue_eq_I` says every eigenvalue is `I`, so every eigenvalue of `jordanI + I/2` has
real part one half — and yet it admits no conserving receiver at all. **Semisimplicity is the
dropped hypothesis** in any reading of "neutral rate" off a spectrum. A defective generator sits on
the seam spectrally with no conserving receiver, which is exactly why the plan reads response
through the resolvent and not through the spectrum. -/
theorem jordan_has_no_conserving_receiver :
    ¬ ∃ G : Matrix (Fin 2) (Fin 2) ℂ, G.PosDef ∧ rateForm jordanI G = 0 := by
  rintro ⟨G, hG, h0⟩
  have hentry := congrFun (congrFun h0 1) 0
  simp [rateForm, jordanI, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]
    at hentry
  have hzero : G 0 0 = 0 := by linear_combination hentry
  have hpos : (0 : ℂ) < G 0 0 := hG.diag_pos
  exact absurd hzero hpos.ne'

end Rate

/-! ## The response atlas separates what the spectrum cannot -/

namespace Linearization

/-- [definition] A single nilpotent Jordan block, probed at the second coordinate and read at the
first. -/
def nilpotentWitness : Linearization ℚ 2 1 1 where
  state := !![0, 1; 0, 0]
  excitation := !![0; 1]
  readout := !![1, 0]

/-- [definition] The zero generator with the same probe and the same readout. -/
def zeroWitness : Linearization ℚ 2 1 1 where
  state := 0
  excitation := !![0; 1]
  readout := !![1, 0]

/-- [proved-derived; formal-checked] -/
theorem nilpotentWitness_denominator : nilpotentWitness.denominator = X ^ 2 := by
  rw [denominator]
  show (!![(0 : ℚ), 1; 0, 0]).charpoly = _
  rw [Matrix.charpoly_fin_two]
  simp [Matrix.trace_fin_two, Matrix.det_fin_two]

/-- [proved-derived; formal-checked] -/
theorem zeroWitness_denominator : zeroWitness.denominator = X ^ 2 := by
  rw [denominator]
  show (0 : Matrix (Fin 2) (Fin 2) ℚ).charpoly = _
  simp

/-- [proved-derived; formal-checked] -/
theorem nilpotentWitness_numerator : nilpotentWitness.numerator 0 0 = 1 := by
  simp [numerator, nilpotentWitness, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.adjugate_fin_two]

/-- [proved-derived; formal-checked] -/
theorem zeroWitness_numerator : zeroWitness.numerator 0 0 = 0 := by
  simp [numerator, zeroWitness, Matrix.mul_apply, Fin.sum_univ_two]

/-- [proved-derived; formal-checked] **The spectrum does not determine the response.** Two
linearizations with the same characteristic polynomial `X²` and different numerators. This is the
plan's governing correction: isospectral objects exist, so identity is carried by the organized
family of responses under admitted probes and receivers, not by one global spectrum.

The Rust owner's `separate_under_probe` exhibits the same phenomenon on a genuine cospectral
non-isomorphic graph pair at 5×5; the 2×2 witness here is the minimal one a kernel can check. -/
theorem spectrum_does_not_determine_response :
    ∃ L₁ L₂ : Linearization ℚ 2 1 1,
      L₁.denominator = L₂.denominator ∧ L₁.numerator ≠ L₂.numerator := by
  refine ⟨nilpotentWitness, zeroWitness, ?_, ?_⟩
  · rw [nilpotentWitness_denominator, zeroWitness_denominator]
  · intro h
    have hentry := congrFun (congrFun h 0) 0
    rw [nilpotentWitness_numerator, zeroWitness_numerator] at hentry
    exact one_ne_zero hentry

/-- [proved-derived; formal-checked] **The complete atlas does determine the operator.** The
positive counterpart of `spectrum_does_not_determine_response`: the whole matrix
`adjugate (charmatrix A)` — the numerator for every pair of a coordinate probe and a coordinate
readout — recovers `A` entry by entry. Stated at `Fin 2`, where the adjugate is
`!![X − C (A 1 1), C (A 0 1); C (A 1 0), X − C (A 0 0)]` and every entry of `A` is read off
directly. The general statement is true but needs the degree-`n − 2` cofactor expansion, which is
not carried out here; the name records the restriction. -/
theorem full_atlas_determines_the_operator_fin_two {K : Type*} [Field K]
    {A B : Matrix (Fin 2) (Fin 2) K}
    (h : (Matrix.charmatrix A).adjugate = (Matrix.charmatrix B).adjugate) : A = B := by
  have key : ∀ i j, (Matrix.charmatrix A).adjugate i j = (Matrix.charmatrix B).adjugate i j :=
    fun i j => by rw [h]
  have h11 := key 0 0
  have h01 := key 0 1
  have h10 := key 1 0
  have h00 := key 1 1
  simp [Matrix.adjugate_fin_two, Polynomial.C_inj, sub_right_inj] at h11 h01 h10 h00
  ext i j
  fin_cases i <;> fin_cases j <;> simp_all

end Linearization

/-! ## The positive form of a declared finite receiver future

[agent-inferred] Put the form beside the chord that owns source/transport/readout together.
`L i` is the actual composed read `Cᵢ Φᵢ`, so a moving receiver, clock or chart belongs in this
operand. This form measures observations. It is physical storage only under a separate material
calibration. No dense runtime matrix or cost saving is asserted by the following identities.
-/

section FiniteFuture

variable {K ι n m : Type*} [CommRing K] [Fintype ι] [Fintype n] [Fintype m]

/-- [definition] The finite future-read form `Σᵢ Lᵢᵀ Qᵢ Lᵢ`, including interference within each
actual receiver reading before it is paired. The declared index may carry positive integration
weights through `Q`. -/
def futureReadForm (L : ι → Matrix m n K) (Q : ι → Matrix m m K) : Matrix n n K :=
  ∑ i, (L i)ᵀ * Q i * L i

/-- [proved-derived; kernel-check pending] The form is exactly the sum of the actual quadratic
receiver readings; no independent modal intensities replace their coherent sum. -/
theorem futureReadForm_pairing (L : ι → Matrix m n K) (Q : ι → Matrix m m K) (x : n → K) :
    x ⬝ᵥ (futureReadForm L Q *ᵥ x) =
      ∑ i, (L i *ᵥ x) ⬝ᵥ (Q i *ᵥ (L i *ᵥ x)) := by
  have hs : futureReadForm L Q *ᵥ x = ∑ i, ((L i)ᵀ * Q i * L i) *ᵥ x := by
    simpa only [futureReadForm] using
      (Matrix.sum_mulVec Finset.univ (fun i => (L i)ᵀ * Q i * L i) x)
  rw [hs, dotProduct_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    dotProduct_mulVec, Matrix.vecMul_transpose]

/-- [proved-derived; kernel-check pending] Positive receiver metrics identify exactly the
declared future kernel: zero observation score iff every actual future reading vanishes. A
semidefinite metric would instead test only its own observed quotient. -/
theorem futureReadForm_zero_iff [PartialOrder K] [StarRing K] [TrivialStar K] [AddLeftMono K]
    (L : ι → Matrix m n K) (Q : ι → Matrix m m K) (hQ : ∀ i, (Q i).PosDef)
    (x : n → K) :
    x ⬝ᵥ (futureReadForm L Q *ᵥ x) = 0 ↔ ∀ i, L i *ᵥ x = 0 := by
  rw [futureReadForm_pairing]
  have hn : ∀ i, 0 ≤ (L i *ᵥ x) ⬝ᵥ (Q i *ᵥ (L i *ᵥ x)) := by
    intro i
    simpa only [star_trivial] using
      (hQ i).posSemidef.dotProduct_mulVec_nonneg (L i *ᵥ x)
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hn i)]
  constructor
  · intro h i
    by_contra hi
    have hp : 0 < (L i *ᵥ x) ⬝ᵥ (Q i *ᵥ (L i *ᵥ x)) := by
      simpa only [star_trivial] using (hQ i).dotProduct_mulVec_pos hi
    exact (ne_of_gt hp) (h i (Finset.mem_univ i))
  · intro h i _
    rw [h i, Matrix.mulVec_zero, dotProduct_zero]

end FiniteFuture

section Axioms

#print axioms adjugate_eq_det_smul_right
#print axioms adjugate_conj
#print axioms charmatrix_conj
#print axioms charpoly_conj
#print axioms Linearization.resolvent_identity
#print axioms Linearization.denominator_ne_zero
#print axioms Linearization.denominator_smul_transfer_eq_numerator
#print axioms Linearization.rebase_denominator
#print axioms Linearization.rebase_numerator
#print axioms Linearization.rebase_transfer
#print axioms charpoly_dvd_of_quotient
#print axioms Linearization.transfer_eq_resolvent
#print axioms Linearization.charmatrix_intertwine
#print axioms Linearization.transfer_descend
#print axioms Linearization.descended_denominator_clears
#print axioms Linearization.release_cancels
#print axioms Linearization.cancellingWitness_denominator
#print axioms Linearization.cancellingWitness_numerator
#print axioms Linearization.cancellation_is_strict
#print axioms rateForm_congruence
#print axioms seam_iff_gSkew
#print axioms gSkew_eigenvalue_re_eq_zero
#print axioms seam_eigenvalue_re_eq_half
#print axioms semisimple_imaginary_has_conserving_receiver
#print axioms jordan_eigenvalue_eq_I
#print axioms jordan_has_no_conserving_receiver
#print axioms Linearization.nilpotentWitness_denominator
#print axioms Linearization.zeroWitness_denominator
#print axioms Linearization.nilpotentWitness_numerator
#print axioms Linearization.zeroWitness_numerator
#print axioms Linearization.spectrum_does_not_determine_response
#print axioms Linearization.full_atlas_determines_the_operator_fin_two
#print axioms futureReadForm_pairing
#print axioms futureReadForm_zero_iff

end Axioms

end Holonics.Foundation.CausalChord
