import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Matrix.Mul

/-!
# Fluid.ComplexFluid: the complex-bilinear fluid law is not the Fourier chart of a real field

[definition] Battle test 4 of rebuild step 6, K3 (#74). Two different objects carry complex
numbers:

* the **complex-bilinear fluid law** acts on a pair of real fields `U = a + ib`: advection
  `B(U, U) = (B(a,a) − B(b,b)) + i(B(a,b) + B(b,a))` (`complexAdvection`), a law of two physical
  fields;
* the **Fourier chart** of one real field `u` has complex coefficients `û(k)`, constrained by the
  reality of `u` to the Hermitian slice `û(−k) = conj û(k)`; it introduces no second field.

[proved-derived; formal-checked]

* **The complex law keeps its own terms.** Its real part retains the definite `−B(b,b)`, which a
  projection to `a` loses (`Physics/ConductiveFluidReflection.complexRealProjection_retains_Bbb`);
  conjugation `(a,b) ↦ (a,−b)` is the Swing about `(a,0)` and the law is equivariant under it
  (`complexAdvection_conj`).
* **Its Hermitian energy is exchanged, MHD's is not.** For an advection skew in its transported
  argument (`⟨w, B u v⟩ = −⟨v, B u w⟩`), the complex law exchanges `2⟨a, B(b,b)⟩` into the
  Hermitian energy `(|a|² + |b|²)/2` (`complex_energy_exchange`), while the MHD induction sign
  `B(a,b) − B(b,a)` cancels it (`mhd_energy_exchange`).
* **The skew advection is actual.** The skew-symmetrized advection
  `B(u,w) = ½[u ⊙ Dw + D(u ⊙ w)]` with an antisymmetric difference `D` is skew in its transported
  argument (`skewAdvection_skew`).
* **The Fourier chart** (`ZMod.dft` on `ℤ/N`): conjugating a field reflects its transform,
  `𝓕(conj Φ)(k) = conj(𝓕Φ(−k))` (`dft_conj`); a field is real exactly when its transform is
  Hermitian (`real_iff_hermitian`); the bilinear product pairs `k` with `−k`,
  `Σ Φ Ψ = N⁻¹ Σ_k 𝓕Φ(k) 𝓕Ψ(−k)` (`bilinear_plancherel`), and it **diagonalizes** to
  `N⁻¹ Σ_k |𝓕Φ(k)|²` only on the Hermitian slice (`hermitian_diagonal`).

[counterexample; formal-checked]

* **The exchange is nonzero**: on `ℤ/4` with the centred difference, `a = δ₀` and
  `b = δ₀ + δ₁` exchange `2⟨a, B(b,b)⟩ = 1`, and `−a` exchanges `−1` (`complex_exchange_witness`).
* **The bilinear product is not an energy off the Hermitian slice**: the complex state `U = i δ₀`
  (`a = 0`, `b = δ₀`) has `Σ U·U = −1` while `Σ |U|² = 1`, and its transform is not Hermitian
  (`imaginary_state_witness`): a complex-fluid state is not the Fourier chart of a real field.

[established-bounded; source-inspected] The finite-Galerkin statements of the same distinction,
the MHD difference `−2B(b,a)` and the Elsasser identities, are
`Physics/ConductiveFluidReflection` (`complexImaginaryEvolution_differs_from_mhd`,
`complexRealProjection_retains_Bbb`).
-/

noncomputable section

namespace Holonics.Physics.Fluid.ComplexFluid

open Matrix

/-! ## 1. The complex-bilinear law on a pair of real fields -/

section Law

variable {V : Type*} [AddCommGroup V] [Module ℚ V] (B : V →ₗ[ℚ] V →ₗ[ℚ] V)

/-- [definition] **The complex-bilinear advection** `B(U,U)` of `U = a + ib`, as its real and
imaginary parts. -/
def complexAdvection (a b : V) : V × V := (B a a - B b b, B a b + B b a)

/-- [definition] **The MHD advection**: the same real part, the opposite stretching sign in the
induction. -/
def mhdAdvection (a b : V) : V × V := (B a a - B b b, B a b - B b a)

/-- [proved-derived; formal-checked] **Conjugation is a symmetry of the law**: the Swing
`(a,b) ↦ (a,−b)` about `(a,0)` keeps the real part and negates the imaginary part. -/
theorem complexAdvection_conj (a b : V) :
    complexAdvection B a (-b) = ((complexAdvection B a b).1, -(complexAdvection B a b).2) := by
  simp [complexAdvection]
  abel

/-- [definition] Advection skew in its transported argument for the pairing `⟪·,·⟫`. -/
def SkewIn (pair : V →ₗ[ℚ] V →ₗ[ℚ] ℚ) : Prop := ∀ u v w, pair w (B u v) = -pair v (B u w)

theorem SkewIn.self_zero {pair : V →ₗ[ℚ] V →ₗ[ℚ] ℚ} (h : SkewIn B pair) (u v : V) :
    pair v (B u v) = 0 := by
  have := h u v v
  linarith

/-- [definition] The rate of the Hermitian energy `(⟪a,a⟫ + ⟪b,b⟫)/2` under an advection
`(ȧ, ḃ) = −adv`, for a symmetric pairing: `⟪a, ȧ⟫ + ⟪b, ḃ⟫`. -/
def energyExchange (pair : V →ₗ[ℚ] V →ₗ[ℚ] ℚ) (a b : V) (adv : V × V) : ℚ :=
  pair a (-adv.1) + pair b (-adv.2)

/-- [proved-derived; formal-checked] **The complex law exchanges `2⟨a, B(b,b)⟩`** with its
Hermitian energy: the indefinite stretching exchange. -/
theorem complex_energy_exchange {pair : V →ₗ[ℚ] V →ₗ[ℚ] ℚ} (h : SkewIn B pair) (a b : V) :
    energyExchange pair a b (complexAdvection B a b) = 2 * pair a (B b b) := by
  simp only [energyExchange, complexAdvection, map_neg, map_sub, map_add, h.self_zero]
  rw [h b a b]
  ring

/-- [proved-derived; formal-checked] **MHD's opposite stretching sign cancels the exchange.** -/
theorem mhd_energy_exchange {pair : V →ₗ[ℚ] V →ₗ[ℚ] ℚ} (h : SkewIn B pair) (a b : V) :
    energyExchange pair a b (mhdAdvection B a b) = 0 := by
  simp only [energyExchange, mhdAdvection, map_neg, map_sub, h.self_zero]
  rw [h b a b]
  ring

end Law

/-! ## 2. The skew-symmetrized discrete advection -/

section Skew

variable {N : ℕ}

/-- [definition] **The skew-symmetrized advection** `B(u,w) = ½[u ⊙ Dw + D(u ⊙ w)]` of a field `u`
transporting `w`, with a difference matrix `D`. -/
def skewAdvection (D : Matrix (Fin N) (Fin N) ℚ) : (Fin N → ℚ) →ₗ[ℚ] (Fin N → ℚ) →ₗ[ℚ] (Fin N → ℚ) :=
  LinearMap.mk₂ ℚ (fun u w => (1 / 2 : ℚ) • (u * (D *ᵥ w) + D *ᵥ (u * w)))
    (fun u u' w => by simp [add_mul, mulVec_add, smul_add]; abel)
    (fun c u w => by simp [mulVec_smul, smul_add, smul_comm c])
    (fun u w w' => by simp [mul_add, mulVec_add, smul_add]; abel)
    (fun c u w => by simp [mulVec_smul, smul_add, smul_comm c])

/-- [definition] The dot-product pairing. -/
def dotPairing : (Fin N → ℚ) →ₗ[ℚ] (Fin N → ℚ) →ₗ[ℚ] ℚ :=
  LinearMap.mk₂ ℚ (fun v w => v ⬝ᵥ w) (fun _ _ _ => add_dotProduct _ _ _)
    (fun _ _ _ => smul_dotProduct _ _ _) (fun _ _ _ => dotProduct_add _ _ _)
    (fun _ _ _ => dotProduct_smul _ _ _)

theorem dotProduct_hadamard (z u w : Fin N → ℚ) : z ⬝ᵥ (u * w) = (z * u) ⬝ᵥ w := by
  simp only [dotProduct, Pi.mul_apply]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- [proved-derived; formal-checked] **The skew-symmetrized advection is skew in its transported
argument** whenever `Dᵀ = −D`. -/
theorem skewAdvection_skew {D : Matrix (Fin N) (Fin N) ℚ} (hD : Dᵀ = -D) :
    SkewIn (skewAdvection D) dotPairing := by
  intro u v w
  simp only [skewAdvection, dotPairing, LinearMap.mk₂_apply, dotProduct_smul, dotProduct_add]
  have hT : ∀ x y : Fin N → ℚ, x ⬝ᵥ (D *ᵥ y) = -((D *ᵥ x) ⬝ᵥ y) := by
    intro x y
    rw [dotProduct_mulVec, ← mulVec_transpose, hD, neg_mulVec, neg_dotProduct]
  rw [hT w (u * v), hT v (u * w), dotProduct_hadamard w u (D *ᵥ v),
    dotProduct_hadamard v u (D *ᵥ w)]
  have h1 : (D *ᵥ w) ⬝ᵥ (u * v) = (v * u) ⬝ᵥ (D *ᵥ w) := by
    rw [dotProduct_comm, mul_comm u v]
  have h2 : (D *ᵥ v) ⬝ᵥ (u * w) = (w * u) ⬝ᵥ (D *ᵥ v) := by
    rw [dotProduct_comm, mul_comm u w]
  rw [h1, h2, smul_eq_mul, smul_eq_mul]
  ring

/-- [definition] The centred difference on `ℤ/4`, `(Dw)ₓ = (w_{x+1} − w_{x−1})/2`. -/
def centred4 : Matrix (Fin 4) (Fin 4) ℚ :=
  !![0, 1/2, 0, -1/2; -1/2, 0, 1/2, 0; 0, -1/2, 0, 1/2; 1/2, 0, -1/2, 0]

theorem centred4_antisymm : centred4ᵀ = -centred4 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [centred4] <;> norm_num

/-- [counterexample; formal-checked] **The complex exchange is nonzero and indefinite**: with the
centred difference on `ℤ/4`, `a = δ₀` and `b = δ₀ + δ₁` exchange `1`, and `−a` exchanges `−1`,
while MHD exchanges `0` for both. -/
theorem complex_exchange_witness :
    energyExchange dotPairing ![1, 0, 0, 0] ![1, 1, 0, 0]
        (complexAdvection (skewAdvection centred4) ![1, 0, 0, 0] ![1, 1, 0, 0]) = 1 ∧
      energyExchange dotPairing (-![1, 0, 0, 0]) ![1, 1, 0, 0]
        (complexAdvection (skewAdvection centred4) (-![1, 0, 0, 0]) ![1, 1, 0, 0]) = -1 ∧
      energyExchange dotPairing ![1, 0, 0, 0] ![1, 1, 0, 0]
        (mhdAdvection (skewAdvection centred4) ![1, 0, 0, 0] ![1, 1, 0, 0]) = 0 := by
  have hs := skewAdvection_skew centred4_antisymm
  refine ⟨?_, ?_, mhd_energy_exchange _ hs _ _⟩
  · rw [complex_energy_exchange _ hs]
    simp [dotPairing, skewAdvection, centred4, dotProduct, Fin.sum_univ_four, Matrix.vecHead,
      Pi.mul_apply]
    norm_num
  · rw [complex_energy_exchange _ hs]
    simp [dotPairing, skewAdvection, centred4, dotProduct, Fin.sum_univ_four, Matrix.vecHead,
      Pi.mul_apply]
    norm_num

end Skew

/-! ## 3. The Fourier chart of one real field -/

section Fourier

open ZMod ComplexConjugate

variable {N : ℕ} [NeZero N]

/-- [proved-derived; formal-checked] **Conjugating a field reflects its transform**:
`𝓕(conj Φ)(k) = conj(𝓕Φ(−k))`. -/
theorem dft_conj (Φ : ZMod N → ℂ) (k : ZMod N) :
    𝓕 (fun j => conj (Φ j)) k = conj (𝓕 Φ (-k)) := by
  simp only [dft_apply, map_sum, smul_eq_mul, map_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← AddChar.map_neg_eq_conj]
  congr 2
  ring

/-- [proved-derived; formal-checked] **A field is real exactly when its transform is Hermitian**:
`Φ = conj Φ ⇔ 𝓕Φ(−k) = conj(𝓕Φ(k))`. -/
theorem real_iff_hermitian (Φ : ZMod N → ℂ) :
    (∀ j, conj (Φ j) = Φ j) ↔ ∀ k, 𝓕 Φ (-k) = conj (𝓕 Φ k) := by
  constructor
  · intro h k
    have := dft_conj Φ (-k)
    rw [neg_neg] at this
    have hfun : (fun j => conj (Φ j)) = Φ := funext h
    rw [hfun] at this
    exact this
  · intro h
    have hdft : 𝓕 (fun j => conj (Φ j)) = 𝓕 Φ := by
      funext k
      rw [dft_conj, h k]
      simp
    have := dft.injective hdft
    exact fun j => congrFun this j

/-- [proved-derived; formal-checked] **The bilinear product pairs `k` with `−k`**:
`Σ_j Φ(j)Ψ(j) = N⁻¹ Σ_k 𝓕Φ(k) 𝓕Ψ(−k)`. -/
theorem bilinear_plancherel (Φ Ψ : ZMod N → ℂ) :
    ∑ j, Φ j * Ψ j = (N : ℂ)⁻¹ * ∑ k, 𝓕 Φ k * 𝓕 Ψ (-k) := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have key : ∑ k, 𝓕 Φ k * 𝓕 Ψ (-k) = ∑ l, Ψ l * 𝓕 (𝓕 Φ) (-l) := by
    simp only [dft_apply Ψ, dft_apply (𝓕 Φ), smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
    rw [show -(l * -k) = -(k * -l) by ring]
    ring
  rw [key, dft_dft]
  simp only [neg_neg, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  field_simp

/-- [proved-derived; formal-checked] **On the Hermitian slice the product diagonalizes**: for a
real field, `Σ_j Φ(j)² = N⁻¹ Σ_k |𝓕Φ(k)|²`. -/
theorem hermitian_diagonal (Φ : ZMod N → ℂ) (hreal : ∀ j, conj (Φ j) = Φ j) :
    ∑ j, Φ j * Φ j = (N : ℂ)⁻¹ * ∑ k, ((Complex.normSq (𝓕 Φ k) : ℝ) : ℂ) := by
  rw [bilinear_plancherel]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [(real_iff_hermitian Φ).mp hreal k, Complex.mul_conj]

/-- [definition] The imaginary complex-fluid state `U = i δ₀` on `ℤ/N` (`a = 0`, `b = δ₀`). -/
def imaginaryState : ZMod N → ℂ := fun j => if j = 0 then Complex.I else 0

/-- [counterexample; formal-checked] **A complex-fluid state is not a real field's chart**: the
state `U = i δ₀` has bilinear product `Σ U·U = −1` against Hermitian energy `Σ |U|² = 1`, and its
transform is not Hermitian. -/
theorem imaginary_state_witness :
    ∑ j, imaginaryState (N := N) j * imaginaryState j = -1 ∧
      ∑ j, ((Complex.normSq (imaginaryState (N := N) j) : ℝ) : ℂ) = 1 ∧
      ¬ ∀ k, 𝓕 (imaginaryState (N := N)) (-k) = conj (𝓕 imaginaryState k) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Finset.sum_eq_single 0]
    · simp [imaginaryState]
    · intro j _ hj; simp [imaginaryState, hj]
    · simp
  · rw [Finset.sum_eq_single 0]
    · simp [imaginaryState]
    · intro j _ hj; simp [imaginaryState, hj]
    · simp
  · intro h
    have hre := (real_iff_hermitian _).mpr h 0
    simp [imaginaryState, Complex.ext_iff] at hre
    norm_num at hre

end Fourier

section Audit

#print axioms complex_energy_exchange
#print axioms mhd_energy_exchange
#print axioms skewAdvection_skew
#print axioms complex_exchange_witness
#print axioms real_iff_hermitian
#print axioms bilinear_plancherel
#print axioms hermitian_diagonal
#print axioms imaginary_state_witness

end Audit

end Holonics.Physics.Fluid.ComplexFluid
