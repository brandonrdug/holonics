import ElementaryHolonics.Objects.RelativeCompleteness
import ElementaryHolonics.Objects.Deposition
import ElementaryHolonics.Millennium.Reflection
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The boundary datum is a membrane face, and eliminating the interior is `Λ_DN`

[definition] Objects 6 and 7 of `docs/ELEMENTARY_OBJECTS.md`. `Objects/RelativeCompleteness`
declared the boundary map `β` of a region and, separately, a membrane `S` bounding the region's
interior chain; which face of `S` the datum returns was left open, as was the join to the
Dirichlet-to-Neumann map. This module supplies both joins.

[proved-derived; formal-checked] What is proved.

1. **The membrane face.** On a bounding membrane, the face of `ω` equals the face of `dω` on the
   interior chain; with `d := ∂.dualMap` this is definitional (`membraneFace_eq_interior_face`,
   labelled as an unfolding, not as Gauss). The substantive statement is gauge freedom: exact
   coholons read zero on a bounding membrane, which uses `∂∂ = 0`
   (`membraneFace_exact_eq_zero`, `membraneFace_gauge`); the lateral tube membrane fails it
   (`tube_face_is_not_gauge_free`). A discrete Gauss law with an independently given coboundary
   matrix is not stated here.
2. **The linear globe's `β` is that face.** For the quarter-turn globe of
   `RelativeCompleteness`, the conserved mass `massC v` is the face of the edge cochain
   `edgeField v` on `globeMembrane`, equal to the face of its coboundary on the interior cell
   (`linearGlobe_boundary_is_membrane_face`). The lateral (tube) membrane does not return a
   gauge-free datum: an exact coholon moves its face (`tube_face_is_not_gauge_free`).
3. **Eliminating the interior is the Schur complement.** For any operator `L` on
   `interior ⊕ boundary` with invertible interior block `A`, every state balanced on the interior
   has interior values `u_I = −A⁻¹B u_B` and boundary response `(Lu)_B = (D − CA⁻¹B) u_B`
   (`interior_elimination`); its energy is `⟨u, Lu⟩ = ⟨u_B, Λ u_B⟩` (`energy_on_boundary`).
4. **On a weighted graph this is the discrete `Λ_DN`, and it reads the boundary datum.** For the
   conductance Laplacian `L = dᵀ diag(Θ) d`, `Deposition.Solves d Θ φ σ` is `L φ = σ`
   (`solves_iff_laplacian`); for any declared split of the nodes `Fin p ≃ I ⊕ B`, a solve with no
   interior source returns the boundary source as `σ_B = Λ_DN φ_B` (`solves_boundary_is_dtn`),
   and the boundary source at a node is the flux face on that node's coboundary (its star)
   (`boundary_source_is_star_face`). The one-site case is `Millennium/Reflection`'s transported
   row (`reflection_row_is_schur`). Witness: the path `b₀ —1— i —2— b₁` eliminates to the series
   conductance `2/3` (`series_path_dtn`).

[open] The join of `Λ_DN` to a `Region`'s dynamics (a time-extended interior with its own clock
whose boundary receiver is `Λ_DN`), a continuum DtN operator, and a membrane of a general
`HodgeReceiver.WeightedComplex` beyond grade 0/1.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Soma.Holonics.Objects.MembraneJoin

open Soma.Holonics
open Soma.Holonics.Objects.RelativeCompleteness
open Matrix

/-! ## 1. Gauss on a bounding membrane -/

section Face

variable {K C₀ C₁ C₂ : Type*} [Field K]
  [AddCommGroup C₀] [Module K C₀] [AddCommGroup C₁] [Module K C₁]
  [AddCommGroup C₂] [Module K C₂]

/-- [definition] The face of a coholon on the membrane. -/
def membraneFace (S : Membrane K C₀ C₁ C₂) (ω : Module.Dual K C₁) : K := ω S.surface

/-- [definition; formal-checked] On a membrane bounding the interior chain,
`⟨ω, ∂Ω⟩ = ⟨dω, Ω⟩`. With `d := ∂.dualMap` this is the definition of the coboundary unfolded
(`ExteriorBoundary.stokes_pairing` is `rfl`); it is not a Gauss theorem. The content that uses
`∂∂ = 0` is gauge freedom of the face (`membraneFace_exact_eq_zero`, `membraneFace_gauge`). -/
theorem membraneFace_eq_interior_face {S : Membrane K C₀ C₁ C₂} (h : S.BoundsInterior)
    (ω : Module.Dual K C₁) :
    membraneFace S ω = S.boundary₂.dualMap ω S.interiorChain := by
  rw [membraneFace, ← h]
  rfl

/-- [proved-derived; formal-checked] **Exact coholons read zero on a bounding membrane**
(`Membrane.closed_iff_no_exact_flux`): the membrane face is gauge free. -/
theorem membraneFace_exact_eq_zero {S : Membrane K C₀ C₁ C₂} (h : S.Bounds)
    (φ : Module.Dual K C₀) : membraneFace S (S.boundary₁.dualMap φ) = 0 :=
  (Membrane.closed_iff_no_exact_flux S).mp h.closed φ

/-- [proved-derived; formal-checked] The membrane face is unchanged by an exact gauge. -/
theorem membraneFace_gauge {S : Membrane K C₀ C₁ C₂} (h : S.Bounds)
    (ω : Module.Dual K C₁) (φ : Module.Dual K C₀) :
    membraneFace S (ω + S.boundary₁.dualMap φ) = membraneFace S ω := by
  have := membraneFace_exact_eq_zero h φ
  simp only [membraneFace, LinearMap.add_apply] at this ⊢
  rw [this, add_zero]

end Face

/-! ## 2. The linear globe's boundary datum is its membrane face -/

/-- [definition] The edge cochain an interior state carries: its conserved mass on edge `e₀`. -/
def edgeField (v : Interior3) : Module.Dual ℚ (Fin 4 → ℚ) :=
  v.2.2 • LinearMap.proj (R := ℚ) (φ := fun _ : Fin 4 => ℚ) 0

/-- [proved-derived; formal-checked] **`β` of the linear globe is a membrane face.** The exterior
datum `massC v` is the face of `edgeField v` on the bounding square, and equals the face of its
coboundary on the interior cell. -/
theorem linearGlobe_boundary_is_membrane_face (v : Interior3) :
    massC v = membraneFace globeMembrane (edgeField v) ∧
      membraneFace globeMembrane (edgeField v) =
        globeMembrane.boundary₂.dualMap (edgeField v) globeMembrane.interiorChain := by
  refine ⟨?_, membraneFace_eq_interior_face globeMembrane_boundsInterior _⟩
  simp [massC, membraneFace, edgeField, globeMembrane]

/-- [counterexample; formal-checked] **The tube face is not gauge free**: the exact coholon of the
potential at `v₁` moves the lateral membrane's face by `1`. -/
theorem tube_face_is_not_gauge_free :
    membraneFace tubeMembrane (0 + tubeMembrane.boundary₁.dualMap (LinearMap.proj 1)) ≠
      membraneFace tubeMembrane 0 := by
  rw [zero_add]
  unfold membraneFace
  rw [tubeMembrane_escapes.1]
  simp

/-! ## 3. Eliminating the interior: the Schur complement -/

section Schur

variable {K : Type*} [Field K] {I B : Type*} [Fintype I] [Fintype B] [DecidableEq I]
  [DecidableEq B]

/-- [definition] **The boundary transport** (Schur complement, discrete `Λ_DN`) of an operator on
`interior ⊕ boundary`: `D − C A⁻¹ B`. -/
def dtn (L : Matrix (I ⊕ B) (I ⊕ B) K) : Matrix B B K :=
  L.toBlocks₂₂ - L.toBlocks₂₁ * L.toBlocks₁₁⁻¹ * L.toBlocks₁₂

/-- [definition] The interior values forced by boundary values: `−A⁻¹ B u_B`. -/
def harmonicExtension (L : Matrix (I ⊕ B) (I ⊕ B) K) (uB : B → K) : I → K :=
  -((L.toBlocks₁₁⁻¹ * L.toBlocks₁₂) *ᵥ uB)

omit [DecidableEq I] [DecidableEq B] in
theorem mulVec_split (L : Matrix (I ⊕ B) (I ⊕ B) K) (u : I ⊕ B → K) :
    L *ᵥ u = Sum.elim (L.toBlocks₁₁ *ᵥ (u ∘ Sum.inl) + L.toBlocks₁₂ *ᵥ (u ∘ Sum.inr))
      (L.toBlocks₂₁ *ᵥ (u ∘ Sum.inl) + L.toBlocks₂₂ *ᵥ (u ∘ Sum.inr)) := by
  conv_lhs => rw [← fromBlocks_toBlocks L]
  exact fromBlocks_mulVec _ _ _ _ u

omit [DecidableEq B] in
/-- [proved-derived; formal-checked] **The interior is eliminated exactly.** If the interior block
is invertible and the state is balanced on the interior (`(Lu)_I = 0`), the interior values are
the harmonic extension of the boundary values and the boundary response is `Λ u_B`. -/
theorem interior_elimination (L : Matrix (I ⊕ B) (I ⊕ B) K) (hA : IsUnit L.toBlocks₁₁.det)
    (u : I ⊕ B → K) (hbal : ∀ i, (L *ᵥ u) (Sum.inl i) = 0) :
    u ∘ Sum.inl = harmonicExtension L (u ∘ Sum.inr) ∧
      (L *ᵥ u) ∘ Sum.inr = dtn L *ᵥ (u ∘ Sum.inr) := by
  have hsplit := mulVec_split L u
  have hI : L.toBlocks₁₁ *ᵥ (u ∘ Sum.inl) + L.toBlocks₁₂ *ᵥ (u ∘ Sum.inr) = 0 := by
    funext i
    have := hbal i
    rw [hsplit] at this
    simpa using this
  have huI : u ∘ Sum.inl = harmonicExtension L (u ∘ Sum.inr) := by
    have h1 : L.toBlocks₁₁ *ᵥ (u ∘ Sum.inl) = -(L.toBlocks₁₂ *ᵥ (u ∘ Sum.inr)) :=
      eq_neg_of_add_eq_zero_left hI
    have h2 := congrArg (fun v => L.toBlocks₁₁⁻¹ *ᵥ v) h1
    simp only [mulVec_mulVec, nonsing_inv_mul _ hA, one_mulVec, mulVec_neg] at h2
    rw [h2, harmonicExtension, ← mulVec_mulVec]
  refine ⟨huI, ?_⟩
  funext b
  have hb : (L *ᵥ u) (Sum.inr b) =
      (L.toBlocks₂₁ *ᵥ (u ∘ Sum.inl) + L.toBlocks₂₂ *ᵥ (u ∘ Sum.inr)) b := by
    rw [hsplit]; rfl
  simp only [Function.comp_apply, hb, huI, harmonicExtension, dtn, sub_mulVec, mulVec_neg,
    mulVec_mulVec, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Matrix.mul_assoc]
  ring

omit [DecidableEq B] in
/-- [proved-derived; formal-checked] **The energy lives on the boundary.** For an interior-balanced
state, `⟨u, Lu⟩ = ⟨u_B, Λ u_B⟩`. -/
theorem energy_on_boundary (L : Matrix (I ⊕ B) (I ⊕ B) K) (hA : IsUnit L.toBlocks₁₁.det)
    (u : I ⊕ B → K) (hbal : ∀ i, (L *ᵥ u) (Sum.inl i) = 0) :
    u ⬝ᵥ (L *ᵥ u) = (u ∘ Sum.inr) ⬝ᵥ (dtn L *ᵥ (u ∘ Sum.inr)) := by
  rw [← (interior_elimination L hA u hbal).2]
  simp only [dotProduct, Fintype.sum_sum_type, hbal, mul_zero, Finset.sum_const_zero, zero_add,
    Function.comp_apply]

end Schur

/-! ## 4. On a weighted graph: `Λ_DN` reads the boundary source -/

section Graph

open Soma.Holonics.Objects.Deposition

variable {p q : ℕ}

/-- [definition] The conductance Laplacian `dᵀ diag(Θ) d`. -/
def laplacian (d : Matrix (Fin q) (Fin p) ℚ) (Θ : Constitution q) : Matrix (Fin p) (Fin p) ℚ :=
  dᵀ * diagonal Θ.1 * d

/-- [proved-derived; formal-checked] `Deposition.Solves` is the Laplacian equation `Lφ = σ`. -/
theorem solves_iff_laplacian (d : Matrix (Fin q) (Fin p) ℚ) (Θ : Constitution q)
    (φ σ : Fin p → ℚ) : Solves d Θ φ σ ↔ laplacian d Θ *ᵥ φ = σ := by
  rw [solves_iff_boundary_flux, laplacian, ← mulVec_mulVec, ← mulVec_mulVec]
  have : diagonal Θ.1 *ᵥ (d *ᵥ φ) = flux d Θ φ := by
    funext e; simp [flux, mulVec_diagonal]
  rw [this]

/-- [proved-derived; formal-checked] **The boundary source is the flux face on the node's
star.** `σ_b = ⟨j, d δ_b⟩`: the pairing of the flux cochain with the coboundary of the node's
indicator (Stokes on the node's star). -/
theorem boundary_source_is_star_face {d : Matrix (Fin q) (Fin p) ℚ} {Θ : Constitution q}
    {φ σ : Fin p → ℚ} (h : Solves d Θ φ σ) (b : Fin p) :
    σ b = flux d Θ φ ⬝ᵥ (d *ᵥ Pi.single b 1) := by
  rw [solves_iff_boundary_flux] at h
  rw [← h, mulVec_single_one, dotProduct_comm]
  simp [mulVec, dotProduct, transpose_apply]

/-- [proved-derived; formal-checked] **A solve with no interior source reads `Λ_DN` on the
boundary.** For any declared split `Fin p ≃ I ⊕ B` of the nodes with an invertible interior
block, a potential solving `σ` with `σ` zero on the interior has boundary source
`σ_B = Λ_DN φ_B`, and interior potential the harmonic extension of `φ_B`. -/
theorem solves_boundary_is_dtn {I B : Type} [Fintype I] [Fintype B] [DecidableEq I]
    [DecidableEq B] (split : Fin p ≃ I ⊕ B) {d : Matrix (Fin q) (Fin p) ℚ} {Θ : Constitution q}
    {φ σ : Fin p → ℚ} (h : Solves d Θ φ σ)
    (hA : IsUnit ((laplacian d Θ).submatrix split.symm split.symm).toBlocks₁₁.det)
    (hint : ∀ i, σ (split.symm (Sum.inl i)) = 0) :
    (φ ∘ split.symm) ∘ Sum.inl =
        harmonicExtension ((laplacian d Θ).submatrix split.symm split.symm)
          ((φ ∘ split.symm) ∘ Sum.inr) ∧
      (σ ∘ split.symm) ∘ Sum.inr =
        dtn ((laplacian d Θ).submatrix split.symm split.symm) *ᵥ ((φ ∘ split.symm) ∘ Sum.inr) := by
  have hL : (laplacian d Θ).submatrix split.symm split.symm *ᵥ (φ ∘ split.symm) =
      σ ∘ split.symm := by
    have hφ : (φ ∘ split.symm) ∘ split.symm.symm = φ := by funext x; simp
    rw [submatrix_mulVec_equiv, hφ, (solves_iff_laplacian d Θ φ σ).mp h]
  have hbal : ∀ i, ((laplacian d Θ).submatrix split.symm split.symm *ᵥ (φ ∘ split.symm))
      (Sum.inl i) = 0 := by
    intro i; rw [hL]; exact hint i
  obtain ⟨h1, h2⟩ := interior_elimination _ hA _ hbal
  exact ⟨h1, by rw [← h2, hL]⟩

/-- [proved-derived; formal-checked] **One interior site is `Millennium/Reflection`'s transported
row.** With interior capacity `m` coupled by `c₁, c₂` to two boundary sites and boundary diagonal
`p`, eliminating the interior returns the row `(p − c₁²/m, −c₁c₂/m)`, which is
`Reflection.theBoundaryRowCarriesTheTransportAndTheSource` at zero interior source. -/
theorem reflection_row_is_schur (p' c₁ c₂ m q' : ℚ) (hm : m ≠ 0) (u₁ u₂ : ℚ) :
    (dtn (fromBlocks (!![m] : Matrix (Fin 1) (Fin 1) ℚ) (!![-c₁, -c₂] : Matrix (Fin 1) (Fin 2) ℚ)
        (!![-c₁; -c₂] : Matrix (Fin 2) (Fin 1) ℚ) (!![p', 0; 0, q'] : Matrix (Fin 2) (Fin 2) ℚ)) *ᵥ
        ![u₁, u₂]) 0 =
      p' * u₁ - c₁ * Millennium.Reflection.interiorSolve c₁ c₂ m u₁ u₂ 0 := by
  have hinv : (!![m] : Matrix (Fin 1) (Fin 1) ℚ)⁻¹ = !![m⁻¹] := by
    apply inv_eq_left_inv
    ext i j; fin_cases i; fin_cases j; simp [inv_mul_cancel₀ hm]
  rw [Millennium.Reflection.theBoundaryRowCarriesTheTransportAndTheSource p' c₁ c₂ m u₁ u₂ 0 hm]
  simp [dtn, hinv, mulVec, dotProduct, Fin.sum_univ_two]
  field_simp
  ring

/-- [definition] The path `b₀ —Θ₀— i —Θ₁— b₁`, nodes ordered `(i, b₀, b₁)`. -/
def pathIncidence : Matrix (Fin 2) (Fin 3) ℚ := !![1, -1, 0; -1, 0, 1]

/-- [definition] The split `Fin 3 ≃ Fin 1 ⊕ Fin 2` declaring node `0` interior. -/
def pathSplit : Fin 3 ≃ Fin 1 ⊕ Fin 2 where
  toFun k := if h : k = 0 then Sum.inl 0 else Sum.inr ⟨k.val - 1, by omega⟩
  invFun x := match x with
    | Sum.inl _ => 0
    | Sum.inr b => ⟨b.val + 1, by omega⟩
  left_inv k := by fin_cases k <;> rfl
  right_inv x := by
    rcases x with a | b
    · fin_cases a; rfl
    · fin_cases b <;> rfl

/-- [definition] The constitution `(1, 2)` on the path. -/
def pathΘ : Constitution 2 := ⟨![1, 2], by intro e; fin_cases e <;> norm_num⟩

/-- [proved-derived; formal-checked] **Witness: the series law.** Eliminating the interior node of
the path with conductances `1` and `2` returns `Λ_DN = (2/3)[[1, −1], [−1, 1]]`: the series
conductance `1·2/(1+2)`. -/
theorem series_path_dtn :
    dtn ((laplacian pathIncidence pathΘ).submatrix pathSplit.symm pathSplit.symm) =
      !![2 / 3, -(2 / 3); -(2 / 3), 2 / 3] := by
  have hA : ((laplacian pathIncidence pathΘ).submatrix pathSplit.symm pathSplit.symm).toBlocks₁₁ =
      (!![3] : Matrix (Fin 1) (Fin 1) ℚ) := by
    ext i j
    simp [laplacian, pathIncidence, pathΘ, pathSplit, toBlocks₁₁, Matrix.mul_apply,
      Fin.sum_univ_two, diagonal]
    norm_num
  have hinv : (!![3] : Matrix (Fin 1) (Fin 1) ℚ)⁻¹ = (!![1 / 3] : Matrix (Fin 1) (Fin 1) ℚ) := by
    apply inv_eq_left_inv
    ext i j; fin_cases i; fin_cases j; simp
  ext i j
  rw [dtn, hA, hinv]
  fin_cases i <;> fin_cases j <;>
    simp [laplacian, pathIncidence, pathΘ, pathSplit, toBlocks₁₂, toBlocks₂₁, toBlocks₂₂,
      Matrix.mul_apply, Fin.sum_univ_two, diagonal] <;> norm_num

end Graph

section Audit
#print axioms membraneFace_eq_interior_face
#print axioms membraneFace_exact_eq_zero
#print axioms membraneFace_gauge
#print axioms linearGlobe_boundary_is_membrane_face
#print axioms tube_face_is_not_gauge_free
#print axioms interior_elimination
#print axioms energy_on_boundary
#print axioms solves_iff_laplacian
#print axioms boundary_source_is_star_face
#print axioms solves_boundary_is_dtn
#print axioms reflection_row_is_schur
#print axioms series_path_dtn
end Audit

end Soma.Holonics.Objects.MembraneJoin
