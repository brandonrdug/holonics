import ElementaryHolonics.Holon.Dirac
import ElementaryHolonics.Objects.Membrane

/-!
# Holon.Restriction: morphisms, the scale square and exact Kron reduction

[definition] The restriction facet `π`. A port map `P` pushes flows forward and pulls efforts
back (`pushforward`); a **morphism** lands the pushed structure inside the target one
(`IsMorphism`).

[proved-derived; formal-checked] Morphisms preserve power (`power_pushforward`) and compose
(`IsMorphism.comp`); the pushforward of a Dirac structure along **any** port map (injective or
not) is Dirac, as the composition of the port map's graph relation (`graphD_isDirac`) with the
effort-negated source (`pushforwardD_isDirac`, `mem_pushforwardD`; witness: the gyrator pushed
along a projection gives the passive coholon, `gyrator_projection_witness`); a scale square `π A_fine = A_coarse π` propagates to every horizon
(`scale_square_pow`); the shift read on one coordinate has defect `1` for every coarse generator
(`shift_has_no_coarse_generator`) while a diagonal generator closes exactly (`diagonal_square`).
Kron/Schur elimination of a network's interior is an exact restriction: interior-balanced states
have boundary bonds on the graph of `Λ_DN` with the full power preserved, and every boundary value
extends (`kron_exact`, composing `Objects/Membrane`); witness the series path
(`series_path_restriction`).
-/

noncomputable section

namespace Soma.Holonics.HolonCore

open Matrix

/-! ## 1. Morphisms of bond spaces -/

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

/-! ## 2. The scale square and its defect -/

section Square

variable {𝕜 : Type*} [Field 𝕜] {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
  [DecidableEq κ]

/-- [proved-derived; formal-checked] **The scale square propagates.** If `π A_fine = A_coarse π`,
then `π A_fineⁿ = A_coarseⁿ π` for every number of steps. -/
theorem scale_square_pow (π : Matrix κ ι 𝕜) (Af : Matrix ι ι 𝕜) (Ac : Matrix κ κ 𝕜)
    (h : π * Af = Ac * π) (n : ℕ) : π * Af ^ n = Ac ^ n * π := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, h, ← Matrix.mul_assoc,
      ← pow_succ]

/-- [definition] The typed defect of a proposed coarse generator. -/
def squareDefect (π : Matrix κ ι 𝕜) (Af : Matrix ι ι 𝕜) (Ac : Matrix κ κ 𝕜) : Matrix κ ι 𝕜 :=
  π * Af - Ac * π

/-- [counterexample; formal-checked] **A dynamic reduction with nonzero defect for every coarse
generator.** Reading the first coordinate of the shift `ẋ₁ = x₂`, `ẋ₂ = 0`, no coarse generator
closes the square: the defect at `x = (0, 1)` is `1`. -/
theorem shift_has_no_coarse_generator (a : ℚ) :
    (squareDefect !![1, 0] !![0, 1; 0, 0] !![a] *ᵥ ![0, 1]) 0 = 1 := by
  simp [squareDefect, mulVec, dotProduct, Fin.sum_univ_two]

/-- [proved-derived; formal-checked] The diagonal generator closes the square exactly. -/
theorem diagonal_square (a b : ℚ) :
    squareDefect !![1, 0] !![a, 0; 0, b] !![a] = 0 := by
  ext i j; fin_cases i; fin_cases j <;> simp [squareDefect]

end Square

/-! ## 3. Kron/Schur elimination is an exact restriction with reading `Λ_DN` -/

section Kron

open Soma.Holonics.Objects.MembraneJoin

variable {K : Type*} [Field K] {I B : Type*} [Fintype I] [Fintype B] [DecidableEq I]
  [DecidableEq B]

/-- [definition] The boundary bond of a network state: boundary injected currents and boundary
potentials. -/
def boundaryBond (L : Matrix (I ⊕ B) (I ⊕ B) K) (u : I ⊕ B → K) : Bond K B :=
  ((L *ᵥ u) ∘ Sum.inr, u ∘ Sum.inr)

omit [DecidableEq B] in
/-- [proved-derived; formal-checked] **Kron reduction is exact.** For every interior-balanced
state the boundary bond lies on the graph of `Λ_DN` (`MembraneJoin.interior_elimination`), the
boundary power equals the network's full power `⟨u, L u⟩` (`MembraneJoin.energy_on_boundary`), and
every boundary potential has an interior-balanced extension. -/
theorem kron_exact (L : Matrix (I ⊕ B) (I ⊕ B) K) (hA : IsUnit L.toBlocks₁₁.det) :
    (∀ u : I ⊕ B → K, (∀ i, (L *ᵥ u) (Sum.inl i) = 0) →
      (boundaryBond L u).1 = dtn L *ᵥ (boundaryBond L u).2 ∧
        power (boundaryBond L u) = u ⬝ᵥ (L *ᵥ u)) ∧
    ∀ uB : B → K, ∃ u : I ⊕ B → K, (∀ i, (L *ᵥ u) (Sum.inl i) = 0) ∧ u ∘ Sum.inr = uB := by
  refine ⟨fun u hbal => ⟨(interior_elimination L hA u hbal).2, ?_⟩, fun uB => ?_⟩
  · rw [energy_on_boundary L hA u hbal, power, boundaryBond,
      (interior_elimination L hA u hbal).2, dotProduct_comm]
  · refine ⟨Sum.elim (harmonicExtension L uB) uB, fun i => ?_, by funext b; rfl⟩
    rw [mulVec_split, Sum.elim_inl, Sum.elim_comp_inl, Sum.elim_comp_inr]
    unfold harmonicExtension
    rw [mulVec_neg, mulVec_mulVec, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hA,
      Matrix.one_mul]
    simp

/-- [proved-derived; formal-checked] **Witness: the series path.** The path with conductances `1`
and `2` restricts to the boundary relation `Λ_DN = (2/3)[[1,−1],[−1,1]]`
(`MembraneJoin.series_path_dtn`). -/
theorem series_path_restriction :
    dtn ((laplacian pathIncidence pathΘ).submatrix pathSplit.symm pathSplit.symm) =
      !![2 / 3, -(2 / 3); -(2 / 3), 2 / 3] :=
  series_path_dtn

end Kron

end Soma.Holonics.HolonCore
