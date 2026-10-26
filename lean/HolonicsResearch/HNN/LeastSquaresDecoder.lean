import Holonics.HNN.Encoding
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic

/-!
# An injective observation has the least-squares decoder, and it is the one fact admission owes

The atlas row `linalg.prime-image-injective` (owner `holonics::ratio::linear`, consumer
`PairedObservation::admit` and `ObservationPort::decoder`) reads: a nonzero maximal minor of the
row-scaled integer image `diag(s)E` in one prime chart certifies `ker_ℚ E = 0`, and `ker E = 0`
gives `D = (EᵀE)⁻¹Eᵀ` with `DE = I`. #410 owes the certificate, the decoder and their join to
`Holonics.HNN.Encoding.factor_of_ker_le` (`ρ` factors through `E` iff `ker E ≤ ker ρ`), so that
`ker E = 0` is the one fact an observation's admission certifies. This file proves the decoder over
any ordered field, the certificate over any domain, and the join on the rational carriers the Rust
owner uses.

[proved-standard; formal-checked] What is proved.

1. **The Gram reading keeps the kernel** (`mulVec_eq_zero_of_gram`): `EᵀE v = 0` gives
   `|Ev|² = vᵀEᵀEv = 0`, so `Ev = 0`. Over an ordered field nothing is isotropic.
2. **An injective observation has an invertible Gram** (`gram_isUnit`) and **the least-squares
   decoder is a left inverse** (`decoder_mul`): `ker E = 0` gives `D = (EᵀE)⁻¹Eᵀ` with `DE = I`.
3. **Injectivity is exactly what a decoder needs** (`injective_iff_left_inverse`): `ker E = 0` iff
   some `D` has `DE = I`.
4. **The join to the encoding's factor law** (`reading_factors`, `reading_factors_through_encoding`):
   with `ker E = 0` every reading `R` of the class directions factors as `R = (RD)E`, and as linear
   maps `factor_of_ker_le` applies with `ker E = 0 ≤ ker ρ` for every `ρ`.
5. **A nonzero maximal minor gives `ker E = 0`** (`ker_eq_zero_of_minor`): `adj(E_f) E_f = det(E_f) I`,
   so `Ev = 0` gives `det(E_f) v = 0`, and `v = 0` over a domain. **A chart can only lose a minor**
   (`ker_eq_zero_of_chart_minor`): a ring map sends `0` to `0`, so a minor nonzero in one chart
   `φ : R → F` is nonzero; a chart where it vanishes refuses and does not refute. Over a ring with
   zero divisors the certificate fails (`ℤ/6 → ℤ/2`, `E = [3]`, `E·2 = 0`), so the domain is the
   scope.
6. **The certificate lifts and the scales keep the kernel** (`ker_eq_zero_of_lift`,
   `admission_certificate`, `mulVec_eq_zero_of_scaled`): a minor nonzero over `ℤ` stays nonzero in
   `ℚ`, so the integer image read in `ℚ` is injective, and nonzero row scales `diag(s)` keep the
   kernel.
7. **Admission owes one fact** (`admission_injective`, `admission_decoder`, `admission_factors`): a
   rational observation `E` whose row-scaled integer image `S = diag(s)E` has a minor nonzero in one
   prime chart is injective, so it has the decoder `DE = I` and every linear reading factors
   through it.

The computational object is the helical pair interaction: the Gram `EᵀE` is the pairing of the
observation with itself, and the decoder reads the pair back. Of the winding guide's six general
objects this touches faces and placement (the observation's chart); the helix, the pair, the cell
holonomy, the tube and the tower thread stay attached.

Consumers: the atlas row `linalg.prime-image-injective`.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.HNN.LeastSquaresDecoder

open Matrix

variable {m n K : Type*} [Fintype m] [Fintype n] [DecidableEq n]
  [Field K] [LinearOrder K] [IsStrictOrderedRing K]

omit [DecidableEq n] in
/-- [proved-standard; formal-checked] **The Gram reading keeps the kernel:** `EᵀE v = 0` gives
`E v = 0`. -/
theorem mulVec_eq_zero_of_gram (E : Matrix m n K) {v : n → K} (h : (Eᵀ * E) *ᵥ v = 0) :
    E *ᵥ v = 0 := by
  have h1 : v ⬝ᵥ ((Eᵀ * E) *ᵥ v) = 0 := by rw [h, dotProduct_zero]
  rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose] at h1
  exact dotProduct_self_eq_zero.mp h1

/-- [proved-standard; formal-checked] **An injective observation has an invertible Gram.** -/
theorem gram_isUnit (E : Matrix m n K) (hE : ∀ v, E *ᵥ v = 0 → v = 0) : IsUnit (Eᵀ * E) := by
  rw [← mulVec_injective_iff_isUnit]
  intro v w hvw
  have h : (Eᵀ * E) *ᵥ (v - w) = 0 := by rw [mulVec_sub, hvw, sub_self]
  exact sub_eq_zero.mp (hE _ (mulVec_eq_zero_of_gram E h))

/-- [definition] The least-squares decoder `D = (EᵀE)⁻¹Eᵀ`. -/
noncomputable def decoder (E : Matrix m n K) : Matrix n m K := (Eᵀ * E)⁻¹ * Eᵀ

/-- [proved-standard; formal-checked] **The least-squares decoder is a left inverse:** `ker E = 0`
gives `DE = I`. -/
theorem decoder_mul (E : Matrix m n K) (hE : ∀ v, E *ᵥ v = 0 → v = 0) : decoder E * E = 1 := by
  rw [decoder, Matrix.mul_assoc,
    (Eᵀ * E).nonsing_inv_mul ((Eᵀ * E).isUnit_iff_isUnit_det.mp (gram_isUnit E hE))]

/-- [proved-standard; formal-checked] **Injectivity is exactly what a decoder needs:** `ker E = 0`
iff some `D` has `DE = I`. -/
theorem injective_iff_left_inverse (E : Matrix m n K) :
    (∀ v, E *ᵥ v = 0 → v = 0) ↔ ∃ D : Matrix n m K, D * E = 1 := by
  refine ⟨fun hE => ⟨decoder E, decoder_mul E hE⟩, fun ⟨D, hD⟩ v hv => ?_⟩
  rw [← one_mulVec v, ← hD, ← mulVec_mulVec, hv, mulVec_zero]

/-- [proved-derived; formal-checked] **Every reading of the class directions factors through an
injective observation:** `R = (R D) E`. -/
theorem reading_factors {k : Type*} (E : Matrix m n K) (hE : ∀ v, E *ᵥ v = 0 → v = 0)
    (R : Matrix k n K) : R = R * decoder E * E := by
  rw [Matrix.mul_assoc, decoder_mul E hE, Matrix.mul_one]

omit [Fintype m] [DecidableEq n] [LinearOrder K] [IsStrictOrderedRing K] in
/-- [proved-derived; formal-checked] **The join to the encoding's factor law:** with `ker E = 0`,
`Holonics.HNN.Encoding.factor_of_ker_le` gives every linear reading `ρ` as `D ∘ E`. -/
theorem reading_factors_through_encoding {V : Type*} [AddCommGroup V] [Module K V]
    (E : Matrix m n K) (hE : ∀ v, E *ᵥ v = 0 → v = 0) (ρ : (n → K) →ₗ[K] V) :
    ∃ D : (m → K) →ₗ[K] V, ρ = D.comp (Matrix.mulVecLin E) :=
  Holonics.HNN.Encoding.factor_of_ker_le (Matrix.mulVecLin E) ρ (by
    intro v hv
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv
    rw [hE v hv]
    exact (LinearMap.ker ρ).zero_mem)

omit [DecidableEq n] [LinearOrder K] [IsStrictOrderedRing K] in
/-- [proved-standard; formal-checked] **Row scales keep the kernel:** with every scale nonzero,
`diag(s) E v = 0` gives `E v = 0`. -/
theorem mulVec_eq_zero_of_scaled [DecidableEq m] (s : m → K) (hs : ∀ i, s i ≠ 0)
    (E : Matrix m n K) {v : n → K} (h : (diagonal s * E) *ᵥ v = 0) : E *ᵥ v = 0 := by
  rw [← mulVec_mulVec] at h
  funext i
  have hi := congrFun h i
  rw [mulVec_diagonal, Pi.zero_apply] at hi
  exact (mul_eq_zero.mp hi).resolve_left (hs i)

/-! ## The admission certificate: one chart's nonzero minor -/

section Admission

variable {R : Type*} [CommRing R] [IsDomain R]

omit [Fintype m] in
/-- [proved-standard; formal-checked] **A nonzero maximal minor gives `ker E = 0`:** with the rows
`f` picked, `adj(E_f) E_f = det(E_f) I`, so `E v = 0` gives `det(E_f) v = 0`, and `v = 0` over a
domain. -/
theorem ker_eq_zero_of_minor (E : Matrix m n R) (f : n → m) (h : (E.submatrix f id).det ≠ 0) :
    ∀ v, E *ᵥ v = 0 → v = 0 := by
  intro v hv
  have hsub : (E.submatrix f id) *ᵥ v = 0 := by
    funext i
    exact congrFun hv (f i)
  have hdet : (E.submatrix f id).det • v = 0 := by
    rw [← one_mulVec v, ← smul_mulVec, ← adjugate_mul, ← mulVec_mulVec, hsub, mulVec_zero]
  funext i
  have hi := congrFun hdet i
  rw [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi
  exact (mul_eq_zero.mp hi).resolve_left h

omit [Fintype m] in
/-- [proved-standard; formal-checked] **A chart can only lose a minor:** a ring map sends `0` to `0`,
so a minor nonzero in one chart `φ : R → F` is nonzero, and `ker E = 0`. A chart where the minor
vanishes refuses; it does not refute. -/
theorem ker_eq_zero_of_chart_minor {F : Type*} [CommRing F] (φ : R →+* F) (E : Matrix m n R)
    (f : n → m) (h : φ (E.submatrix f id).det ≠ 0) : ∀ v, E *ᵥ v = 0 → v = 0 :=
  ker_eq_zero_of_minor E f fun h0 => h (by rw [h0, map_zero])

omit [Fintype m] [IsDomain R] in
/-- [proved-standard; formal-checked] **The certificate lifts:** a minor nonzero over `R` stays
nonzero under an injective map into a domain `S`, so `E` read in `S` keeps `ker = 0`. -/
theorem ker_eq_zero_of_lift {S : Type*} [CommRing S] [IsDomain S] (ψ : R →+* S)
    (hψ : Function.Injective ψ) (E : Matrix m n R) (f : n → m)
    (h : (E.submatrix f id).det ≠ 0) : ∀ v, (E.map ψ) *ᵥ v = 0 → v = 0 := by
  refine ker_eq_zero_of_minor (E.map ψ) f ?_
  have hdet : ((E.map ψ).submatrix f id).det = ψ (E.submatrix f id).det := by
    rw [RingHom.map_det]
    all_goals rfl
  rw [hdet]
  exact fun h0 => h (hψ (by rw [h0, map_zero]))

omit [Fintype m] in
/-- [proved-standard; formal-checked] **One prime chart certifies the rational kernel:** an integer
image `E` whose minor is nonzero in one chart `φ : ℤ → F` is injective read in `ℚ`. -/
theorem admission_certificate {F : Type*} [CommRing F] (φ : ℤ →+* F) (E : Matrix m n ℤ)
    (f : n → m) (h : φ (E.submatrix f id).det ≠ 0) :
    ∀ v : n → ℚ, (E.map (Int.castRingHom ℚ)) *ᵥ v = 0 → v = 0 :=
  ker_eq_zero_of_lift (Int.castRingHom ℚ) (fun a b hab => by simpa using hab) E f
    fun h0 => h (by rw [h0, map_zero])

end Admission

/-- [proved-derived; formal-checked] **One prime chart admits a rational observation:** if the
row-scaled integer image `S = diag(s) E` has a minor nonzero in one chart, `ker_ℚ E = 0`. -/
theorem admission_injective [DecidableEq m] {F : Type*} [CommRing F] (φ : ℤ →+* F)
    (E : Matrix m n ℚ) (s : m → ℚ) (S : Matrix m n ℤ)
    (hS : S.map (Int.castRingHom ℚ) = diagonal s * E) (f : n → m)
    (h : φ (S.submatrix f id).det ≠ 0) : ∀ v, E *ᵥ v = 0 → v = 0 := by
  intro v hv
  refine admission_certificate φ S f h v ?_
  rw [hS, ← mulVec_mulVec, hv, mulVec_zero]

/-- [proved-derived; formal-checked] **The admitted observation has its decoder** `DE = I`. -/
theorem admission_decoder [DecidableEq m] {F : Type*} [CommRing F] (φ : ℤ →+* F)
    (E : Matrix m n ℚ) (s : m → ℚ) (S : Matrix m n ℤ)
    (hS : S.map (Int.castRingHom ℚ) = diagonal s * E) (f : n → m)
    (h : φ (S.submatrix f id).det ≠ 0) : decoder E * E = 1 :=
  decoder_mul E (admission_injective φ E s S hS f h)

/-- [proved-derived; formal-checked] **Admission is the one fact the readings owe:** every linear
reading of the admitted observation's class directions factors through it. -/
theorem admission_factors [DecidableEq m] {F V : Type*} [CommRing F] [AddCommGroup V]
    [Module ℚ V] (φ : ℤ →+* F) (E : Matrix m n ℚ) (s : m → ℚ) (S : Matrix m n ℤ)
    (hS : S.map (Int.castRingHom ℚ) = diagonal s * E) (f : n → m)
    (h : φ (S.submatrix f id).det ≠ 0) (ρ : (n → ℚ) →ₗ[ℚ] V) :
    ∃ D : (m → ℚ) →ₗ[ℚ] V, ρ = D.comp (Matrix.mulVecLin E) :=
  reading_factors_through_encoding E (admission_injective φ E s S hS f h) ρ

end Holonics.HNN.LeastSquaresDecoder
