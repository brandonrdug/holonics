import Holonics.Holon.Dirac
import Mathlib.Tactic

/-! [agent-inferred] This existing law block has an independent consumer.
Its canonical namespace and every statement/proof are preserved exactly;
the aggregate owner imports it once. Import factoring excludes unrelated
constitutions/witnesses at the fixed one-core, 17-second, 2^32-byte RSS gate. -/

noncomputable section

namespace Holonics.HolonCore

open Matrix

section Morphism

variable {𝕜 : Type*} [Field 𝕜] {ι ι' ι'' : Type*} [Fintype ι] [Fintype ι'] [Fintype ι'']

/-- [definition] **The pushforward of bonds** along a flow map `P`: flows map forward
`f' = P f`, efforts map back `e = Pᵀ e'`. -/
def pushforward (P : Matrix ι' ι 𝕜) (D : Submodule 𝕜 (Bond 𝕜 ι)) : Set (Bond 𝕜 ι') :=
  {b' | ∃ f, P *ᵥ f = b'.1 ∧ (f, Pᵀ *ᵥ b'.2) ∈ D}

/-- [proved-derived; formal-checked] **A morphism preserves power**: `⟨e', P f⟩ = ⟨Pᵀ e', f⟩`. -/
theorem power_pushforward (P : Matrix ι' ι 𝕜) (f : ι → 𝕜) (e' : ι' → 𝕜) :
    power ((P *ᵥ f, e') : Bond 𝕜 ι') = power ((f, Pᵀ *ᵥ e') : Bond 𝕜 ι) := by
  simp only [power]
  rw [dotProduct_mulVec, mulVec_transpose]

/-- [definition] **A morphism of port structures**: its pushforward lands in the target
structure. -/
def IsMorphism (P : Matrix ι' ι 𝕜) (D : Submodule 𝕜 (Bond 𝕜 ι)) (D' : Submodule 𝕜 (Bond 𝕜 ι')) :
    Prop :=
  pushforward P D ⊆ D'

/-- [proved-derived; formal-checked] Morphisms compose. -/
theorem IsMorphism.comp {P : Matrix ι' ι 𝕜} {P' : Matrix ι'' ι' 𝕜} {D : Submodule 𝕜 (Bond 𝕜 ι)}
    {D' : Submodule 𝕜 (Bond 𝕜 ι')} {D'' : Submodule 𝕜 (Bond 𝕜 ι'')}
    (h : IsMorphism P D D') (h' : IsMorphism P' D' D'') : IsMorphism (P' * P) D D'' := by
  rintro b'' ⟨f, hf, hD⟩
  refine h' ⟨P *ᵥ f, by rw [mulVec_mulVec]; exact hf, h ⟨f, rfl, ?_⟩⟩
  rw [Matrix.transpose_mul, ← mulVec_mulVec] at hD
  exact hD

/-- [definition] The graph of a port map as a relation between `Bond ι'` and `Bond ι`:
`((P f, e'), (f, −Pᵀ e'))`. -/
def graphD (P : Matrix ι' ι 𝕜) : Submodule 𝕜 (Bond 𝕜 ι' × Bond 𝕜 ι) where
  carrier := {x | P *ᵥ x.2.1 = x.1.1 ∧ x.2.2 = -(Pᵀ *ᵥ x.1.2)}
  add_mem' ha hb := ⟨by simp [mulVec_add, ha.1, hb.1], by simp [ha.2, hb.2, mulVec_add]; abel⟩
  zero_mem' := ⟨by simp, by simp⟩
  smul_mem' c x hx := ⟨by simp [mulVec_smul, hx.1], by simp [hx.2, mulVec_smul]⟩

/-- [definition] Negate the efforts of a structure. -/
def negEffort (D : Submodule 𝕜 (Bond 𝕜 ι)) : Submodule 𝕜 (Bond 𝕜 ι) :=
  D.map (LinearMap.prodMap LinearMap.id (-LinearMap.id))

variable [DecidableEq ι] [DecidableEq ι']

omit [DecidableEq ι] [DecidableEq ι'] in
theorem negEffort_isDirac {D : Submodule 𝕜 (Bond 𝕜 ι)} (hD : IsDirac (bondForm 𝕜 ι) D) :
    IsDirac (bondForm 𝕜 ι) (negEffort D) := by
  apply isDirac_of
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    have := hD.pairing_eq_zero hx hy
    simp only [bondForm_apply, LinearMap.prodMap_apply, LinearMap.id_apply,
      LinearMap.neg_apply] at this ⊢
    simp only [neg_dotProduct]; linear_combination -this
  · intro y hy
    refine ⟨(y.1, -y.2), ?_, by simp⟩
    rw [← hD]
    intro x hx
    have := hy ((LinearMap.prodMap LinearMap.id (-LinearMap.id)) x) ⟨x, hx, rfl⟩
    simp only [bondForm_apply, LinearMap.prodMap_apply, LinearMap.id_apply,
      LinearMap.neg_apply, neg_dotProduct] at this ⊢
    linear_combination -this

/-- [proved-derived; formal-checked] The graph of any port map is a Dirac relation. -/
theorem graphD_isDirac (P : Matrix ι' ι 𝕜) :
    IsDirac (prodForm (bondForm 𝕜 ι') (bondForm 𝕜 ι)) (graphD P) := by
  apply isDirac_of
  · rintro x ⟨hx1, hx2⟩ y ⟨hy1, hy2⟩
    rw [prodForm_apply, bondForm_apply, bondForm_apply, ← hx1, ← hy1, hx2, hy2]
    have key : ∀ (a : ι' → 𝕜) (b : ι → 𝕜), (Pᵀ *ᵥ a) ⬝ᵥ b = a ⬝ᵥ (P *ᵥ b) := fun a b => by
      rw [dotProduct_comm, transpose_dot]
    simp only [neg_dotProduct, key]
    ring
  · intro y hy
    have h1 : y.1.1 = P *ᵥ y.2.1 := by
      funext j
      have := hy ((0, Pi.single j 1), (0, -(Pᵀ *ᵥ Pi.single j 1))) ⟨by simp, rfl⟩
      simp only [prodForm_apply, bondForm_apply, add_zero, neg_dotProduct,
        dotProduct_zero] at this
      rw [dotProduct_comm (Pᵀ *ᵥ _), transpose_dot, single_dotProduct, single_dotProduct,
        one_mul, one_mul] at this
      linear_combination this
    have h2 : y.2.2 = -(Pᵀ *ᵥ y.1.2) := by
      funext j
      have := hy ((P *ᵥ Pi.single j 1, 0), (Pi.single j 1, 0)) ⟨rfl, by simp⟩
      simp only [prodForm_apply, bondForm_apply, zero_dotProduct, zero_add] at this
      rw [dotProduct_mulVec, ← mulVec_transpose] at this
      simp only [dotProduct_single, mul_one] at this
      simp only [Pi.neg_apply]
      linear_combination this
    exact ⟨h1.symm, h2⟩

/-- [definition] **The pushforward Dirac structure**: compose the graph of `P` with the
effort-negated source structure. -/
def pushforwardD (P : Matrix ι' ι 𝕜) (D : Submodule 𝕜 (Bond 𝕜 ι)) : Submodule 𝕜 (Bond 𝕜 ι') :=
  compose (graphD P) (negEffort D)

omit [DecidableEq ι] [DecidableEq ι'] in
/-- [proved-derived; formal-checked] The pushforward submodule is the pushforward set. -/
theorem mem_pushforwardD (P : Matrix ι' ι 𝕜) (D : Submodule 𝕜 (Bond 𝕜 ι)) (b' : Bond 𝕜 ι') :
    b' ∈ pushforwardD P D ↔ b' ∈ pushforward P D := by
  rw [pushforwardD, mem_compose]
  constructor
  · rintro ⟨q, ⟨x, hx, rfl⟩, h1, h2⟩
    refine ⟨x.1, h1, ?_⟩
    simp only [LinearMap.prodMap_apply, LinearMap.id_apply, LinearMap.neg_apply] at h2
    have : x.2 = Pᵀ *ᵥ b'.2 := by rw [← neg_neg x.2, h2, neg_neg]
    rw [← this]; exact hx
  · rintro ⟨f, hf, hD⟩
    exact ⟨(f, -(Pᵀ *ᵥ b'.2)), ⟨(f, Pᵀ *ᵥ b'.2), hD, by simp⟩, hf, rfl⟩

/-- [proved-derived; formal-checked] **The pushforward of a Dirac structure along any port map is
Dirac** — no injectivity or surjectivity is needed in finite dimension: it is a composition of
Dirac relations (`compose_isDirac`). -/
theorem pushforwardD_isDirac (P : Matrix ι' ι 𝕜) {D : Submodule 𝕜 (Bond 𝕜 ι)}
    (hD : IsDirac (bondForm 𝕜 ι) D) : IsDirac (bondForm 𝕜 ι') (pushforwardD P D) :=
  compose_isDirac bondForm_symm bondForm_symm bondForm_separating bondForm_separating
    (graphD_isDirac P) (negEffort_isDirac hD)

/-- [proved-derived; formal-checked] Witness: pushing the gyrator along the projection onto its
first port returns the passive coholon `{f = 0}` (a non-invertible map, a Dirac result). -/
theorem gyrator_projection_witness (e : Fin 1 → ℚ) :
    ((0, e) : Bond ℚ (Fin 1)) ∈ pushforwardD (!![1, 0] : Matrix (Fin 1) (Fin 2) ℚ)
      (skewGraph gyrator) := by
  rw [mem_pushforwardD]
  refine ⟨![0, e 0], ?_, ?_⟩
  · ext i; fin_cases i; simp [mulVec, dotProduct]
  · show ![0, e 0] = gyrator *ᵥ _
    ext i; fin_cases i <;> simp [gyrator, mulVec, dotProduct, Fin.sum_univ_two]

end Morphism

end Holonics.HolonCore
