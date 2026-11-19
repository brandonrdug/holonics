import Holonics.Objects.Membrane
import Holonics.Holon.Restriction
import Holonics.Foundation.ContinuingTower
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# `Λ_DN` along a tube's stations and a tower's levels

Source: #410's box "The `Λ_DN` join: the elimination of an interior joined to the tube and tower owners", which
`docs/ELEMENTARY_OBJECTS.md` §7 states as "`Λ_DN` read along a tube's stations and a tower's levels is owed in
#410". `Objects/Membrane` (namespace `MembraneJoin`) owns the elimination of one interior: `dtn L = D − C A⁻¹ B` on
`interior ⊕ boundary`, the harmonic extension `−A⁻¹ B u_B`, `interior_elimination`, `energy_on_boundary` and the
witness `series_path_dtn`; `Holon/Restriction.kron_exact` reads that elimination as a restriction that preserves
power. The record
`research/records/2026-08-09_THE_INTERIOR_IS_AN_INTEGRAL_OVER_ITS_BOUNDARY_AND_THE_KERNEL_IS_BUILT_BY_REFLECTION.md`
derives the Schur complement as the discrete Dirichlet-to-Neumann map with `−A⁻¹B` as harmonic measure. Atlas rows
served: `tube.dn-elimination`, `tube.dtn-energy-on-boundary`, `tube.kron-exact`, `tube.series-path-dtn`,
`tube.series-path-restriction`, `tube.neck-rank-bound` and `tower.continuing-tower`; the moment chart of the same
two laws stands in `HNN/EffectiveTension` (`tension_le_residual` is Dirichlet's principle for a face Gram,
`tension_fromRows` the quotient formula; atlas `contact.effective-tension`, `contact.tension-founds-face`), and
this file states them on `MembraneJoin.dtn` itself, without importing that chart.

[proved-standard; formal-checked] What is proved: the classical laws (staged elimination, the series law,
Dirichlet's principle, Rayleigh monotonicity, the positivity of `Λ`); [proved-derived; formal-checked] and their
joins to the owners (the tube's stations and path, the elimination tower, the neck). Each theorem carries its tag.

1. **Staged elimination is joint elimination** (§1, the quotient formula). For `L` on `I₁ ⊕ (I₂ ⊕ B)` with the
   interior block on `I₁` and the `I₂` block of `dtn L` invertible, the joint interior block on `I₁ ⊕ I₂`
   (`joint`, the reindexing by `Equiv.sumAssoc`) has determinant `det A₁ · det S₂` (`joint_toBlocks₁₁`,
   `det_joint`, `isUnit_det_joint`), eliminating `I₁` and then `I₂` returns the joint elimination
   (`staged_elimination`), and the joint harmonic extension is the staged one (`staged_harmonicExtension`,
   both read from `staged_state`). `Λ_DN` does not see how its interior is labelled (`dtn_reindex_interior`) and
   follows a relabelling of its boundary (`dtn_reindex_boundary`); every extension by the harmonic values is
   balanced on the interior (`harmonicExtension_balanced`, read from `kron_exact`).
2. **The tube: stations eliminate in any order, and segments glue in series** (§2). If `I₁` then `I₂` can be
   eliminated and the `I₂` block is invertible, then `I₂` then `I₁` can be eliminated, and both orders return one
   boundary relation (`stations_eliminate_in_any_order`, through `joint_swap`). A segment that does not touch the
   interior passes through its elimination unchanged (`dtn_embed`). Two segments glued at a shared station `S`
   (`glue`: their blocks add on `S`, each port sees only its own segment) eliminate at `S` to the Schur
   complement of the block sum (`glue_dtn`); for two-port conductances `a, b` with `a + b ≠ 0` this is the series
   conductance `ab/(a + b)` (`series_conductance`, with `twoPort`). A path of `n + 1` edges (`pathOp`, glued edge
   by edge, its old end becoming an interior station: `extendStep`, `extendStep_dtn`, `placed_twoPorts`)
   eliminates to `(Σ_k 1/g_k)⁻¹`: resistances add (`path_eliminates_in_series`); the witness `path_witness`
   returns `series_path_dtn`'s `2/3`.
3. **Dirichlet's principle and Rayleigh monotonicity** (§3). For `L` positive semidefinite with an invertible
   interior block, `⟨u_B, Λ u_B⟩ ≤ ⟨u, L u⟩` for every `u` that agrees with `u_B` on the boundary
   (`dirichlet_principle`), with equality at the harmonic extension (`dirichlet_attained`), so `Λ` is the least
   energy over extensions and is positive semidefinite (`dtn_posSemidef`; Hermitian by `dtn_isHermitian`). With
   a positive definite interior block, `L ≤ L'` in the Loewner order gives `Λ(L) ≤ Λ(L')`: raising a conductance
   never lowers the boundary relation (`rayleigh_monotone`). A positive definite `L` has a positive definite `Λ`
   (`dtn_posDef`, with `posDef_toBlocks₁₁`, `isUnit_det_of_posDef`).
4. **The tower: elimination is a `ContinuingTower.Tower`** (§4). With faces at level `n` the positive definite
   symmetric real matrices on `Fin n` (`RelationFace`) and `restrict` for `m ≤ n` the elimination of the top
   `n − m` sites (`siteSplit`, `eliminateTop`), positive definiteness is kept (`dtn_posDef`,
   `eliminateTop_posDef`), `restrict_refl` and `restrict_trans` hold (`eliminateTop_refl`, `eliminateTop_trans`,
   through `staged_elimination`, `topJoin` and `siteSplit_comp`), and the tower is `eliminationTower`. Each
   restriction is `kron_exact`'s restriction with power preserved (`eliminationTower_restrict_is_kron`). The
   decoupled grounded sites `c · 1` are continuing objects for every `c > 0` (`eliminateTop_smul_one`,
   `scaledSection`), so the tower's gluing is plural (`eliminationTower_gluing`).
5. **The neck** (§5). For `L` on `interior ⊕ (left ⊕ right)` with no direct left–right block, the left–right
   block of `Λ` is `−B_L A⁻¹ B_R` (`neck_block`), of rank at most `rank B_L`, at most `rank B_R` and at most the
   interior's size (`neck_rank`): what a tube passes from one end to the other passes through its interior, the
   static reading of `Transport/HolonicChain.transfer_rank_le_cross_rank`.

What is not claimed. No continuum Dirichlet-to-Neumann operator and no time-extended interior with its
own clock (`MembraneJoin`'s `[open]` join of `Λ_DN` to a `Region`'s dynamics stays open). The tube here is a path of
stations eliminated along its length; no `Transport/ContinuingTube.Tube` is built that carries `eliminationTower`
along a longitudinal transport, and `eliminationTower` meets the tube owner only through `ContinuingTube`'s reading
of every `Tower` as a tube's transverse section. Order independence is proved for two stations; any order of `n`
stations follows by adjacent swaps and is not stated as one theorem. The path theorem asks `g_k > 0` in an ordered
field; the two-segment law asks only `a + b ≠ 0`. The tower, Dirichlet's principle and Rayleigh monotonicity are
stated over `ℝ` (positive semidefinite in Mathlib's sense, which includes symmetry); staged elimination, the
gluing law and the neck hold over any field. The incidence is real and carries no phase: a connection-valued
incidence, whose holonomy on a circuit would enter `Λ_DN`, is not treated.

The computational object is the helical pair interaction, read on networks of pair contacts: an edge is a contact
whose slip is the difference of its two stations' values, its conductance the contact's material weight, and the
network's operator the contact material `Σ w J* J`. Eliminating an interior station composes the contacts that meet
there into contacts between the remaining stations, and two contacts in series compose into one whose resistance is
the sum of theirs. Of the winding guide's six general objects this touches the pair (a two-port contact and its
material), faces and placement (`Λ_DN` as the face a boundary presents, the harmonic extension placing the interior
values it forces), the tube (stations eliminated along a path, in any order, and its neck) and the tower thread
(restriction by elimination as a `Tower`, its continuing objects and its plural gluing); the helix and cell holonomy
stay attached.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.Holon.DtNTubeTower

open Matrix
open Holonics.Objects.MembraneJoin

/-! ## 0. Reindexing the stations -/

section Reindex

variable {α : Type*} {I₁ I₂ B : Type*}

/-- [definition] **The joint interior.** An operator on `I₁ ⊕ (I₂ ⊕ B)` read on `(I₁ ⊕ I₂) ⊕ B`, so that
`MembraneJoin.dtn` eliminates both interiors at once. -/
def joint (L : Matrix (I₁ ⊕ (I₂ ⊕ B)) (I₁ ⊕ (I₂ ⊕ B)) α) : Matrix ((I₁ ⊕ I₂) ⊕ B) ((I₁ ⊕ I₂) ⊕ B) α :=
  L.submatrix (Equiv.sumAssoc I₁ I₂ B) (Equiv.sumAssoc I₁ I₂ B)

/-- [proved-derived; formal-checked] The joint interior block in blocks: the `I₁` block, the `I₁`–`I₂` coupling
and the `I₂` block of the remaining operator. -/
theorem joint_toBlocks₁₁ (L : Matrix (I₁ ⊕ (I₂ ⊕ B)) (I₁ ⊕ (I₂ ⊕ B)) α) :
    (joint L).toBlocks₁₁ = fromBlocks L.toBlocks₁₁ (L.toBlocks₁₂.submatrix id Sum.inl)
      (L.toBlocks₂₁.submatrix Sum.inl id) L.toBlocks₂₂.toBlocks₁₁ := by
  ext (i | i) (j | j) <;> rfl

/-- [definition] **The other order.** The relabelling that lists the station `I₂` before `I₁`. -/
def swapStations : I₂ ⊕ (I₁ ⊕ B) ≃ I₁ ⊕ (I₂ ⊕ B) :=
  (Equiv.sumAssoc I₂ I₁ B).symm.trans
    ((Equiv.sumCongr (Equiv.sumComm I₂ I₁) (Equiv.refl B)).trans (Equiv.sumAssoc I₁ I₂ B))

/-- [proved-derived; formal-checked] Listing `I₂` first changes the joint interior only by the swap of its two
summands. -/
theorem joint_swap (L : Matrix (I₁ ⊕ (I₂ ⊕ B)) (I₁ ⊕ (I₂ ⊕ B)) α) :
    joint (L.submatrix swapStations swapStations) =
      (joint L).submatrix (Sum.map (Equiv.sumComm I₂ I₁) id) (Sum.map (Equiv.sumComm I₂ I₁) id) := by
  ext ((i | i) | b) ((j | j) | c) <;> rfl

end Reindex

/-! ## 1. Staged elimination is joint elimination -/

section Elimination

variable {K : Type*} [Field K] {I B : Type*} [Fintype I] [DecidableEq I]

/-- [proved-derived; formal-checked] **The harmonic extension is balanced.** Extending boundary values by the
interior values `−A⁻¹ B u_B` gives a state with no interior response; read from `kron_exact`'s extension and
`interior_elimination`'s uniqueness. -/
theorem harmonicExtension_balanced [Fintype B] (L : Matrix (I ⊕ B) (I ⊕ B) K) (hA : IsUnit L.toBlocks₁₁.det)
    (uB : B → K) : ∀ i, (L *ᵥ Sum.elim (harmonicExtension L uB) uB) (Sum.inl i) = 0 := by
  obtain ⟨u, hbal, hB⟩ := (Holonics.HolonCore.kron_exact L hA).2 uB
  have hI := (interior_elimination L hA u hbal).1
  rw [hB] at hI
  have hu : u = Sum.elim (harmonicExtension L uB) uB := by
    funext x
    rcases x with i | b
    · exact congrFun hI i
    · exact congrFun hB b
  rw [← hu]
  exact hbal

/-- [proved-standard; formal-checked] **`Λ_DN` does not see how its interior is labelled.** -/
theorem dtn_reindex_interior {I' : Type*} [Fintype I'] [DecidableEq I'] (L : Matrix (I ⊕ B) (I ⊕ B) K)
    (e : I' ≃ I) : dtn (L.submatrix (Sum.map e id) (Sum.map e id)) = dtn L := by
  have h11 : (L.submatrix (Sum.map e id) (Sum.map e id)).toBlocks₁₁ = L.toBlocks₁₁.submatrix e e := rfl
  have h12 : (L.submatrix (Sum.map e id) (Sum.map e id)).toBlocks₁₂ = L.toBlocks₁₂.submatrix e id := rfl
  have h21 : (L.submatrix (Sum.map e id) (Sum.map e id)).toBlocks₂₁ = L.toBlocks₂₁.submatrix id e := rfl
  have h22 : (L.submatrix (Sum.map e id) (Sum.map e id)).toBlocks₂₂ = L.toBlocks₂₂ := rfl
  rw [dtn, dtn, h11, h12, h21, h22, inv_submatrix_equiv, submatrix_mul_equiv, submatrix_mul_equiv,
    submatrix_id_id]

/-- [proved-standard; formal-checked] **`Λ_DN` follows a relabelling of its boundary.** -/
theorem dtn_reindex_boundary {B' : Type*} (L : Matrix (I ⊕ B) (I ⊕ B) K) (e : B' → B) :
    dtn (L.submatrix (Sum.map id e) (Sum.map id e)) = (dtn L).submatrix e e := rfl

/-- [proved-standard; formal-checked] **A segment off the interior passes through its elimination.** Placing the
boundary along any `E` and adding a boundary-only term `N` commutes with eliminating the interior:
`Λ(A, B E, Eᵀ C, Eᵀ D E + N) = Eᵀ Λ(A, B, C, D) E + N`. -/
theorem dtn_embed {B' : Type*} [Fintype B] (A : Matrix I I K) (Bm : Matrix I B K) (C : Matrix B I K)
    (D : Matrix B B K) (E : Matrix B B' K) (N : Matrix B' B' K) :
    dtn (fromBlocks A (Bm * E) (Eᵀ * C) (Eᵀ * D * E + N)) = Eᵀ * dtn (fromBlocks A Bm C D) * E + N := by
  simp only [dtn, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁,
    toBlocks_fromBlocks₂₂, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  abel

end Elimination

section Staged

variable {K : Type*} [Field K] {I₁ I₂ B : Type*} [Fintype I₁] [Fintype I₂] [Fintype B] [DecidableEq I₁]
  [DecidableEq I₂]

omit [Fintype B] in
/-- [proved-standard; formal-checked] **The joint determinant factors through the stages**:
`det A_(I₁ ⊕ I₂) = det A₁ · det S₂`, with `S₂` the `I₂` block of `dtn L`. -/
theorem det_joint (L : Matrix (I₁ ⊕ (I₂ ⊕ B)) (I₁ ⊕ (I₂ ⊕ B)) K) (h₁ : IsUnit L.toBlocks₁₁.det) :
    (joint L).toBlocks₁₁.det = L.toBlocks₁₁.det * (dtn L).toBlocks₁₁.det := by
  let _ := L.toBlocks₁₁.invertibleOfIsUnitDet h₁
  rw [joint_toBlocks₁₁, det_fromBlocks₁₁, invOf_eq_nonsing_inv]
  rfl

omit [Fintype B] in
/-- [proved-standard; formal-checked] If both stages are invertible, so is the joint interior. -/
theorem isUnit_det_joint (L : Matrix (I₁ ⊕ (I₂ ⊕ B)) (I₁ ⊕ (I₂ ⊕ B)) K) (h₁ : IsUnit L.toBlocks₁₁.det)
    (h₂ : IsUnit (dtn L).toBlocks₁₁.det) : IsUnit (joint L).toBlocks₁₁.det := by
  rw [det_joint L h₁]
  exact h₁.mul h₂

/-- [proved-standard; formal-checked] **The staged state.** For every boundary value, the joint elimination's
response equals the staged one, and the joint harmonic extension is `I₁`'s extension of `I₂`'s extension. -/
theorem staged_state (L : Matrix (I₁ ⊕ (I₂ ⊕ B)) (I₁ ⊕ (I₂ ⊕ B)) K) (h₁ : IsUnit L.toBlocks₁₁.det)
    (h₂ : IsUnit (dtn L).toBlocks₁₁.det) (uB : B → K) :
    dtn (joint L) *ᵥ uB = dtn (dtn L) *ᵥ uB ∧
      harmonicExtension (joint L) uB =
        Sum.elim (harmonicExtension L (Sum.elim (harmonicExtension (dtn L) uB) uB))
          (harmonicExtension (dtn L) uB) := by
  have hJ := isUnit_det_joint L h₁ h₂
  obtain ⟨w, hw⟩ : ∃ w : I₂ ⊕ B → K, w = Sum.elim (harmonicExtension (dtn L) uB) uB := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u : I₁ ⊕ (I₂ ⊕ B) → K, u = Sum.elim (harmonicExtension L w) w := ⟨_, rfl⟩
  have hbal₁ : ∀ i, (L *ᵥ u) (Sum.inl i) = 0 := by rw [hu]; exact harmonicExtension_balanced L h₁ w
  have hbal₂ : ∀ j, (dtn L *ᵥ w) (Sum.inl j) = 0 := by
    rw [hw]; exact harmonicExtension_balanced (dtn L) h₂ uB
  have hLu : (L *ᵥ u) ∘ Sum.inr = dtn L *ᵥ w := by
    rw [(interior_elimination L h₁ u hbal₁).2, hu, Sum.elim_comp_inr]
  have hLw : (dtn L *ᵥ w) ∘ Sum.inr = dtn (dtn L) *ᵥ uB := by
    rw [(interior_elimination (dtn L) h₂ w hbal₂).2, hw, Sum.elim_comp_inr]
  have hJu : joint L *ᵥ (u ∘ Equiv.sumAssoc I₁ I₂ B) = (L *ᵥ u) ∘ Equiv.sumAssoc I₁ I₂ B := by
    unfold joint
    rw [submatrix_mulVec_equiv]
    congr 2
    funext x
    simp
  have hbalJ : ∀ i, (joint L *ᵥ (u ∘ Equiv.sumAssoc I₁ I₂ B)) (Sum.inl i) = 0 := by
    intro i
    rw [hJu]
    rcases i with i | j
    · exact hbal₁ i
    · have := congrFun hLu (Sum.inl j)
      simp only [Function.comp_apply] at this
      simp only [Function.comp_apply, Equiv.sumAssoc_apply_inl_inr, this]
      exact hbal₂ j
  have hB : (u ∘ Equiv.sumAssoc I₁ I₂ B) ∘ Sum.inr = uB := by
    funext b; simp [hu, hw]
  obtain ⟨hext, hresp⟩ := interior_elimination (joint L) hJ _ hbalJ
  rw [hB] at hext hresp
  refine ⟨?_, ?_⟩
  · rw [← hresp, hJu, ← hLw, ← hLu]
    funext b
    simp
  · rw [← hext]
    funext x
    rcases x with i | j <;> simp [hu, hw]

/-- [proved-standard; formal-checked] **Staged elimination is joint elimination** (the quotient formula):
eliminating `I₁` and then `I₂` returns the elimination of `I₁ ⊕ I₂` at once. -/
theorem staged_elimination [DecidableEq B] (L : Matrix (I₁ ⊕ (I₂ ⊕ B)) (I₁ ⊕ (I₂ ⊕ B)) K)
    (h₁ : IsUnit L.toBlocks₁₁.det) (h₂ : IsUnit (dtn L).toBlocks₁₁.det) : dtn (dtn L) = dtn (joint L) :=
  ext_of_mulVec_single fun _ => (staged_state L h₁ h₂ _).1.symm

/-- [proved-standard; formal-checked] **The harmonic extensions agree**: the joint extension is the staged one. -/
theorem staged_harmonicExtension (L : Matrix (I₁ ⊕ (I₂ ⊕ B)) (I₁ ⊕ (I₂ ⊕ B)) K)
    (h₁ : IsUnit L.toBlocks₁₁.det) (h₂ : IsUnit (dtn L).toBlocks₁₁.det) (uB : B → K) :
    harmonicExtension (joint L) uB =
      Sum.elim (harmonicExtension L (Sum.elim (harmonicExtension (dtn L) uB) uB))
        (harmonicExtension (dtn L) uB) :=
  (staged_state L h₁ h₂ uB).2

/-! ## 2. The tube: stations in any order, segments in series -/

/-- [proved-derived; formal-checked] **Stations eliminate in any order.** If `I₁` then `I₂` can be eliminated and
the `I₂` block is invertible, then `I₂` then `I₁` can be eliminated, and both orders return one boundary
relation. -/
theorem stations_eliminate_in_any_order [DecidableEq B] (L : Matrix (I₁ ⊕ (I₂ ⊕ B)) (I₁ ⊕ (I₂ ⊕ B)) K)
    (h₁ : IsUnit L.toBlocks₁₁.det) (h₂ : IsUnit (dtn L).toBlocks₁₁.det)
    (h₂' : IsUnit (L.submatrix swapStations swapStations).toBlocks₁₁.det) :
    IsUnit (dtn (L.submatrix swapStations swapStations)).toBlocks₁₁.det ∧
      dtn (dtn (L.submatrix swapStations swapStations)) = dtn (dtn L) := by
  have hdet : (joint (L.submatrix swapStations swapStations)).toBlocks₁₁.det =
      (joint L).toBlocks₁₁.det := by
    rw [joint_swap]
    exact det_submatrix_equiv_self (Equiv.sumComm I₂ I₁) (joint L).toBlocks₁₁
  have hS : IsUnit (dtn (L.submatrix swapStations swapStations)).toBlocks₁₁.det := by
    have := isUnit_det_joint L h₁ h₂
    rw [← hdet, det_joint _ h₂'] at this
    exact isUnit_of_mul_isUnit_right this
  refine ⟨hS, ?_⟩
  rw [staged_elimination _ h₂' hS, staged_elimination L h₁ h₂, joint_swap, dtn_reindex_interior]

end Staged

section Glue

variable {K : Type*} [Field K] {S P Q : Type*} [Fintype S] [DecidableEq S]

/-- [definition] **Two segments glued at a shared station `S`.** On `S` the two segments' blocks add; each
segment's ports couple to `S` through their own segment, and the two port sets do not couple directly. -/
def glue (L₁ : Matrix (S ⊕ P) (S ⊕ P) K) (L₂ : Matrix (S ⊕ Q) (S ⊕ Q) K) :
    Matrix (S ⊕ (P ⊕ Q)) (S ⊕ (P ⊕ Q)) K :=
  fromBlocks (L₁.toBlocks₁₁ + L₂.toBlocks₁₁) (fromCols L₁.toBlocks₁₂ L₂.toBlocks₁₂)
    (fromRows L₁.toBlocks₂₁ L₂.toBlocks₂₁) (fromBlocks L₁.toBlocks₂₂ 0 0 L₂.toBlocks₂₂)

/-- [proved-standard; formal-checked] **The glued segments eliminate at the station to the Schur complement of
their block sum** `M = A₁ + A₂`: each end keeps `D − C M⁻¹ B` and the ends couple by `−C₁ M⁻¹ B₂`. -/
theorem glue_dtn (L₁ : Matrix (S ⊕ P) (S ⊕ P) K) (L₂ : Matrix (S ⊕ Q) (S ⊕ Q) K) :
    dtn (glue L₁ L₂) =
      fromBlocks
        (L₁.toBlocks₂₂ - L₁.toBlocks₂₁ * (L₁.toBlocks₁₁ + L₂.toBlocks₁₁)⁻¹ * L₁.toBlocks₁₂)
        (-(L₁.toBlocks₂₁ * (L₁.toBlocks₁₁ + L₂.toBlocks₁₁)⁻¹ * L₂.toBlocks₁₂))
        (-(L₂.toBlocks₂₁ * (L₁.toBlocks₁₁ + L₂.toBlocks₁₁)⁻¹ * L₁.toBlocks₁₂))
        (L₂.toBlocks₂₂ - L₂.toBlocks₂₁ * (L₁.toBlocks₁₁ + L₂.toBlocks₁₁)⁻¹ * L₂.toBlocks₁₂) := by
  simp only [dtn, glue, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁,
    toBlocks_fromBlocks₂₂, fromRows_mul, mul_fromCols, fromCols_fromRows_eq_fromBlocks, sub_eq_add_neg,
    fromBlocks_neg, fromBlocks_add, zero_add]

end Glue

section TwoPort

variable {K : Type*} [Field K]

/-- [definition] **A two-port contact of conductance `c`**: `c [[1, −1], [−1, 1]]` on its two stations. -/
def twoPort (c : K) : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) K :=
  of fun x y => if x = y then c else -c

/-- [proved-standard; formal-checked] The inverse of a nonzero one-site block. -/
theorem inv_fin_one (c : K) (hc : c ≠ 0) : (of fun _ _ : Fin 1 => c)⁻¹ = of fun _ _ : Fin 1 => c⁻¹ := by
  apply inv_eq_left_inv
  ext i j
  fin_cases i; fin_cases j
  simp [mul_apply, inv_mul_cancel₀ hc]

/-- [proved-standard; formal-checked] The station block of two glued two-ports is their summed conductance. -/
theorem glue_twoPort_toBlocks₁₁ (a b : K) :
    (glue (twoPort a) (twoPort b)).toBlocks₁₁ = of fun _ _ : Fin 1 => a + b := by
  ext i j; fin_cases i; fin_cases j; simp [glue, twoPort, toBlocks₁₁]

/-- [proved-standard; formal-checked] **The series law.** Two two-ports of conductances `a`, `b` glued at a
station and eliminated there give one two-port of conductance `ab/(a + b)`. -/
theorem series_conductance (a b : K) (hab : a + b ≠ 0) :
    dtn (glue (twoPort a) (twoPort b)) = twoPort (a * b / (a + b)) := by
  have h11 : (twoPort a).toBlocks₁₁ + (twoPort b).toBlocks₁₁ = of fun _ _ : Fin 1 => a + b := by
    ext i j; fin_cases i; fin_cases j; simp [twoPort, toBlocks₁₁]
  rw [glue_dtn, h11, inv_fin_one _ hab]
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
    simp [twoPort, toBlocks₁₂, toBlocks₂₁, toBlocks₂₂, mul_apply] <;> field_simp <;> ring

/-- [definition] The old path's ends placed in the longer path: its left end at the far end `inr (inl 0)`, its
right end at the station `inl 0` that the new edge meets. -/
def oldEnds : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ (Fin 1 ⊕ Fin 1)) K :=
  of fun a y => match a, y with
    | Sum.inl _, Sum.inr (Sum.inl _) => 1
    | Sum.inr _, Sum.inl _ => 1
    | _, _ => 0

/-- [definition] The new edge's ends placed in the longer path: the station `inl 0` and the new end
`inr (inr 0)`. -/
def newEnds : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ (Fin 1 ⊕ Fin 1)) K :=
  of fun a y => match a, y with
    | Sum.inl _, Sum.inl _ => 1
    | Sum.inr _, Sum.inr (Sum.inr _) => 1
    | _, _ => 0

/-- [definition] **One more edge at the right end.** The path operator `L` on `Fin n ⊕ (left ⊕ right)` with a
two-port of conductance `c` glued at its right end; the old right end becomes the station `inl 0`. -/
def extendStep {n : ℕ} (L : Matrix (Fin n ⊕ (Fin 1 ⊕ Fin 1)) (Fin n ⊕ (Fin 1 ⊕ Fin 1)) K) (c : K) :
    Matrix (Fin n ⊕ (Fin 1 ⊕ (Fin 1 ⊕ Fin 1))) (Fin n ⊕ (Fin 1 ⊕ (Fin 1 ⊕ Fin 1))) K :=
  fromBlocks L.toBlocks₁₁ (L.toBlocks₁₂ * oldEnds) (oldEndsᵀ * L.toBlocks₂₁)
    (oldEndsᵀ * L.toBlocks₂₂ * oldEnds + newEndsᵀ * twoPort c * newEnds)

/-- [definition] **The path of `n + 1` edges** with conductances `g 0, …, g n`: `n` interior stations and the two
ends. It is glued edge by edge (`extendStep`), each old end becoming an interior station. -/
def pathOp (g : ℕ → K) : (n : ℕ) → Matrix (Fin n ⊕ (Fin 1 ⊕ Fin 1)) (Fin n ⊕ (Fin 1 ⊕ Fin 1)) K
  | 0 => (twoPort (g 0)).submatrix (Sum.elim Fin.elim0 id) (Sum.elim Fin.elim0 id)
  | n + 1 => (joint (extendStep (pathOp g n) (g (n + 1)))).submatrix
      (Sum.map finSumFinEquiv.symm id) (Sum.map finSumFinEquiv.symm id)

/-- [proved-derived; formal-checked] Two placed two-ports are the two glued segments. -/
theorem placed_twoPorts (a b : K) :
    oldEndsᵀ * twoPort a * oldEnds + newEndsᵀ * twoPort b * newEnds = glue (twoPort a) (twoPort b) := by
  ext (i | i | i) (j | j | j) <;> fin_cases i <;> fin_cases j <;>
    simp [oldEnds, newEnds, twoPort, glue, mul_apply, Fintype.sum_sum_type, toBlocks₁₁, toBlocks₁₂,
      toBlocks₂₁, toBlocks₂₂]

/-- [proved-derived; formal-checked] **Eliminating the old interior first** leaves the old path's two-port glued
to the new edge (`dtn_embed`), and keeps the old interior block. -/
theorem extendStep_dtn {n : ℕ} (L : Matrix (Fin n ⊕ (Fin 1 ⊕ Fin 1)) (Fin n ⊕ (Fin 1 ⊕ Fin 1)) K)
    (G c : K) (hL : dtn L = twoPort G) :
    (extendStep L c).toBlocks₁₁ = L.toBlocks₁₁ ∧ dtn (extendStep L c) = glue (twoPort G) (twoPort c) := by
  refine ⟨toBlocks_fromBlocks₁₁ _ _ _ _, ?_⟩
  rw [extendStep, dtn_embed, fromBlocks_toBlocks, hL, placed_twoPorts]

variable [LinearOrder K] [IsStrictOrderedRing K]

/-- [proved-standard; formal-checked] **Resistances add.** A path of `n + 1` edges with positive conductances has
an invertible interior block and eliminates to the two-port of conductance `(Σ_k 1/g_k)⁻¹`. -/
theorem path_eliminates_in_series (g : ℕ → K) (hg : ∀ k, 0 < g k) (n : ℕ) :
    IsUnit (pathOp g n).toBlocks₁₁.det ∧
      dtn (pathOp g n) = twoPort (∑ k ∈ Finset.range (n + 1), (g k)⁻¹)⁻¹ := by
  induction n with
  | zero =>
    refine ⟨by simp, ?_⟩
    ext i j
    simp [dtn, pathOp, toBlocks₂₂]
  | succ n ih =>
    obtain ⟨hu, hd⟩ := ih
    obtain ⟨h11, hX⟩ := extendStep_dtn (pathOp g n) _ (g (n + 1)) hd
    have hs : 0 < ∑ k ∈ Finset.range (n + 1), (g k)⁻¹ :=
      Finset.sum_pos (fun k _ => inv_pos.mpr (hg k)) Finset.nonempty_range_add_one
    have hsum : (∑ k ∈ Finset.range (n + 1), (g k)⁻¹)⁻¹ + g (n + 1) ≠ 0 :=
      (add_pos (inv_pos.mpr hs) (hg (n + 1))).ne'
    have h₁ : IsUnit (extendStep (pathOp g n) (g (n + 1))).toBlocks₁₁.det := by rw [h11]; exact hu
    have h₂ : IsUnit (dtn (extendStep (pathOp g n) (g (n + 1)))).toBlocks₁₁.det := by
      rw [hX, glue_twoPort_toBlocks₁₁, det_unique]
      exact hsum.isUnit
    refine ⟨?_, ?_⟩
    · have := isUnit_det_joint _ h₁ h₂
      rw [← det_submatrix_equiv_self (finSumFinEquiv.symm : Fin (n + 1) ≃ Fin n ⊕ Fin 1)] at this
      exact this
    · show dtn ((joint (extendStep (pathOp g n) (g (n + 1)))).submatrix
        (Sum.map finSumFinEquiv.symm id) (Sum.map finSumFinEquiv.symm id)) = _
      rw [dtn_reindex_interior, ← staged_elimination _ h₁ h₂, hX, series_conductance _ _ hsum,
        Finset.sum_range_succ (fun k => (g k)⁻¹) (n + 1)]
      congr 1
      have hc := (hg (n + 1)).ne'
      generalize ∑ k ∈ Finset.range (n + 1), (g k)⁻¹ = s at hs ⊢
      have hs' := hs.ne'
      field_simp
      ring

/-- [proved-derived; formal-checked] **Witness**: conductances `1` and `2` in series eliminate to `2/3`, the value
of `MembraneJoin.series_path_dtn`. -/
theorem path_witness : dtn (pathOp (fun k => (k : ℚ) + 1) 1) = twoPort (2 / 3) := by
  rw [(path_eliminates_in_series _ (fun k => by positivity) 1).2]
  norm_num [Finset.sum_range_succ]

end TwoPort

/-! ## 3. Dirichlet's principle and Rayleigh monotonicity -/

section Energy

variable {I B : Type*} [Fintype I] [Fintype B] [DecidableEq I]

omit [Fintype B] in
/-- [proved-standard; formal-checked] `Λ_DN` of a Hermitian operator is Hermitian. -/
theorem dtn_isHermitian {K : Type*} [Field K] [StarRing K] (L : Matrix (I ⊕ B) (I ⊕ B) K)
    (hL : L.IsHermitian) : (dtn L).IsHermitian := by
  rw [← fromBlocks_toBlocks L] at hL
  obtain ⟨hA, hBC, -, hD⟩ := isHermitian_fromBlocks_iff.mp hL
  unfold dtn
  rw [← hBC]
  exact hD.sub (isHermitian_conjTranspose_mul_mul _ hA.inv)

omit [Fintype I] [DecidableEq I] [Fintype B] in
/-- [proved-standard; formal-checked] The interior block of a positive definite operator is positive definite. -/
theorem posDef_toBlocks₁₁ {L : Matrix (I ⊕ B) (I ⊕ B) ℝ} (hL : L.PosDef) : L.toBlocks₁₁.PosDef :=
  hL.submatrix Sum.inl_injective

omit [Fintype B] in
/-- [proved-standard; formal-checked] A positive definite block has a unit determinant. -/
theorem isUnit_det_of_posDef {A : Matrix I I ℝ} (hA : A.PosDef) : IsUnit A.det :=
  (isUnit_iff_isUnit_det A).mp hA.isUnit

/-- [proved-standard; formal-checked] **The least energy is attained at the harmonic extension**:
`⟨h, L h⟩ = ⟨u_B, Λ u_B⟩` for `h` the harmonic extension of `u_B`. -/
theorem dirichlet_attained (L : Matrix (I ⊕ B) (I ⊕ B) ℝ) (hA : IsUnit L.toBlocks₁₁.det) (uB : B → ℝ) :
    Sum.elim (harmonicExtension L uB) uB ⬝ᵥ (L *ᵥ Sum.elim (harmonicExtension L uB) uB) =
      uB ⬝ᵥ (dtn L *ᵥ uB) := by
  rw [energy_on_boundary L hA _ (harmonicExtension_balanced L hA uB), Sum.elim_comp_inr]

/-- [proved-standard; formal-checked] **Dirichlet's principle.** For `L` positive semidefinite with an invertible
interior block, every state `u` has energy at least `⟨u_B, Λ u_B⟩` of its boundary values. -/
theorem dirichlet_principle (L : Matrix (I ⊕ B) (I ⊕ B) ℝ) (hL : L.PosSemidef)
    (hA : IsUnit L.toBlocks₁₁.det) (u : I ⊕ B → ℝ) :
    (u ∘ Sum.inr) ⬝ᵥ (dtn L *ᵥ (u ∘ Sum.inr)) ≤ u ⬝ᵥ (L *ᵥ u) := by
  obtain ⟨h, hh⟩ : ∃ h : I ⊕ B → ℝ, h = Sum.elim (harmonicExtension L (u ∘ Sum.inr)) (u ∘ Sum.inr) :=
    ⟨_, rfl⟩
  have hbal : ∀ i, (L *ᵥ h) (Sum.inl i) = 0 := by rw [hh]; exact harmonicExtension_balanced L hA _
  have hE : h ⬝ᵥ (L *ᵥ h) = (u ∘ Sum.inr) ⬝ᵥ (dtn L *ᵥ (u ∘ Sum.inr)) := by
    rw [hh]; exact dirichlet_attained L hA _
  have hsymm : Lᵀ = L := by
    have := hL.isHermitian
    rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
  have hcross : (u - h) ⬝ᵥ (L *ᵥ h) = 0 := by
    simp only [dotProduct, Fintype.sum_sum_type, hbal, mul_zero, Finset.sum_const_zero, zero_add]
    refine Finset.sum_eq_zero fun b _ => ?_
    simp [hh]
  have hsym' : h ⬝ᵥ (L *ᵥ (u - h)) = (u - h) ⬝ᵥ (L *ᵥ h) := by
    rw [dotProduct_mulVec, ← mulVec_transpose, hsymm, dotProduct_comm]
  have hw : 0 ≤ (u - h) ⬝ᵥ (L *ᵥ (u - h)) := by
    simpa using hL.dotProduct_mulVec_nonneg (u - h)
  have hexp : u ⬝ᵥ (L *ᵥ u) =
      h ⬝ᵥ (L *ᵥ h) + 2 * ((u - h) ⬝ᵥ (L *ᵥ h)) + (u - h) ⬝ᵥ (L *ᵥ (u - h)) := by
    have hu : u = h + (u - h) := by abel
    conv_lhs => rw [hu]
    rw [mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add, hsym']
    ring
  rw [← hE, hexp, hcross]
  linarith

/-- [proved-standard; formal-checked] **`Λ_DN` is positive semidefinite** when `L` is and its interior block is
invertible: its quadratic form is the least energy over extensions. -/
theorem dtn_posSemidef (L : Matrix (I ⊕ B) (I ⊕ B) ℝ) (hL : L.PosSemidef) (hA : IsUnit L.toBlocks₁₁.det) :
    (dtn L).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg (dtn_isHermitian L hL.1) fun uB => ?_
  rw [star_trivial, ← dirichlet_attained L hA uB]
  simpa using hL.dotProduct_mulVec_nonneg (Sum.elim (harmonicExtension L uB) uB)

/-- [proved-standard; formal-checked] **`Λ_DN` of a positive definite operator is positive definite.** -/
theorem dtn_posDef (L : Matrix (I ⊕ B) (I ⊕ B) ℝ) (hL : L.PosDef) : (dtn L).PosDef := by
  have hA := isUnit_det_of_posDef (posDef_toBlocks₁₁ hL)
  refine PosDef.of_dotProduct_mulVec_pos (dtn_isHermitian L hL.1) fun uB huB => ?_
  rw [star_trivial, ← dirichlet_attained L hA uB]
  have hne : Sum.elim (harmonicExtension L uB) uB ≠ 0 := by
    intro h0
    apply huB
    funext b
    simpa using congrFun h0 (Sum.inr b)
  simpa using hL.dotProduct_mulVec_pos hne

/-- [proved-standard; formal-checked] **Rayleigh monotonicity.** For `L` positive semidefinite with a positive
definite interior block and `L' − L` positive semidefinite, `Λ(L') − Λ(L)` is positive semidefinite: raising a
conductance never lowers the boundary relation. -/
theorem rayleigh_monotone (L L' : Matrix (I ⊕ B) (I ⊕ B) ℝ) (hL : L.PosSemidef) (hA : L.toBlocks₁₁.PosDef)
    (hLL' : (L' - L).PosSemidef) : (dtn L' - dtn L).PosSemidef := by
  have hL' : L'.PosSemidef := by simpa using hL.add hLL'
  have hA' : L'.toBlocks₁₁.PosDef := by
    have h : L'.toBlocks₁₁ = L.toBlocks₁₁ + (L' - L).toBlocks₁₁ := by
      ext i j; simp [toBlocks₁₁]
    rw [h]
    exact hA.add_posSemidef (hLL'.submatrix Sum.inl)
  have hAu := isUnit_det_of_posDef hA
  have hAu' := isUnit_det_of_posDef hA'
  refine PosSemidef.of_dotProduct_mulVec_nonneg
    ((dtn_isHermitian L' hL'.1).sub (dtn_isHermitian L hL.1)) fun uB => ?_
  rw [star_trivial, sub_mulVec, dotProduct_sub, sub_nonneg]
  have e1 := dirichlet_attained L' hAu' uB
  have e2 := dirichlet_principle L hL hAu (Sum.elim (harmonicExtension L' uB) uB)
  rw [Sum.elim_comp_inr] at e2
  have e3 := hLL'.dotProduct_mulVec_nonneg (Sum.elim (harmonicExtension L' uB) uB)
  rw [star_trivial, sub_mulVec, dotProduct_sub] at e3
  linarith

end Energy

/-! ## 4. The tower: restriction by elimination -/

section Tower

open Holonics.Foundation.ContinuingTower

/-- [definition] **Level `n` split at level `m`**: the top `n − m` sites (interior) and the first `m` sites
(boundary). -/
def siteSplit {m n : ℕ} (h : m ≤ n) : Fin (n - m) ⊕ Fin m ≃ Fin n :=
  (Equiv.sumComm _ _).trans (finSumFinEquiv.trans (finCongr (Nat.add_sub_cancel' h)))

/-- [proved-derived; formal-checked] The boundary sites of the split are the first `m` sites. -/
theorem siteSplit_inr {m n : ℕ} (h : m ≤ n) (j : Fin m) : (siteSplit h (Sum.inr j) : ℕ) = j := by
  simp [siteSplit]

/-- [definition] The two top blocks of a staged split read as the top block of the joint split. -/
def topJoin {k m n : ℕ} (hkm : k ≤ m) (hmn : m ≤ n) : Fin (n - m) ⊕ Fin (m - k) ≃ Fin (n - k) :=
  (Equiv.sumComm _ _).trans (finSumFinEquiv.trans (finCongr (by omega)))

/-- [proved-derived; formal-checked] Splitting `n` at `m` and then `m` at `k` is splitting `n` at `k`, with the two
top blocks joined. -/
theorem siteSplit_comp {k m n : ℕ} (hkm : k ≤ m) (hmn : m ≤ n) :
    (siteSplit hmn ∘ Sum.map id (siteSplit hkm)) ∘ Equiv.sumAssoc _ _ _ =
      siteSplit (hkm.trans hmn) ∘ Sum.map (topJoin hkm hmn) id := by
  funext x
  rcases x with (i | j) | b
  · apply Fin.ext; simp [siteSplit, topJoin]; omega
  · apply Fin.ext; simp [siteSplit, topJoin]
  · apply Fin.ext; simp [siteSplit, topJoin]

/-- [definition] **Restriction by elimination**: the boundary relation of the first `m` sites, the top `n − m`
eliminated. -/
def eliminateTop {m n : ℕ} (h : m ≤ n) (X : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  dtn (X.submatrix (siteSplit h) (siteSplit h))

/-- [proved-standard; formal-checked] Elimination keeps positive definiteness. -/
theorem eliminateTop_posDef {m n : ℕ} (h : m ≤ n) {X : Matrix (Fin n) (Fin n) ℝ} (hX : X.PosDef) :
    (eliminateTop h X).PosDef :=
  dtn_posDef _ (hX.submatrix (siteSplit h).injective)

/-- [proved-derived; formal-checked] **`restrict_refl`**: eliminating no site changes nothing. -/
theorem eliminateTop_refl (m : ℕ) (X : Matrix (Fin m) (Fin m) ℝ) : eliminateTop (le_refl m) X = X := by
  have : IsEmpty (Fin (m - m)) := ⟨fun k => by have := k.isLt; omega⟩
  ext i j
  have hi : siteSplit (le_refl m) (Sum.inr i) = i := Fin.ext (siteSplit_inr _ i)
  have hj : siteSplit (le_refl m) (Sum.inr j) = j := Fin.ext (siteSplit_inr _ j)
  simp [eliminateTop, dtn, mul_apply, toBlocks₂₂, hi, hj]

/-- [proved-derived; formal-checked] **`restrict_trans`**: eliminating the top `n − m` sites and then the top
`m − k` is eliminating the top `n − k` at once (`staged_elimination`). -/
theorem eliminateTop_trans {k m n : ℕ} (hkm : k ≤ m) (hmn : m ≤ n) {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : X.PosDef) : eliminateTop hkm (eliminateTop hmn X) = eliminateTop (hkm.trans hmn) X := by
  have hZ : ((X.submatrix (siteSplit hmn) (siteSplit hmn)).submatrix (Sum.map id (siteSplit hkm))
      (Sum.map id (siteSplit hkm))).PosDef :=
    (hX.submatrix (siteSplit hmn).injective).submatrix
      (Sum.map_injective.mpr ⟨Function.injective_id, (siteSplit hkm).injective⟩)
  have h₁ := isUnit_det_of_posDef (posDef_toBlocks₁₁ hZ)
  have h₂ := isUnit_det_of_posDef (posDef_toBlocks₁₁ (dtn_posDef _ hZ))
  unfold eliminateTop
  rw [← dtn_reindex_boundary, staged_elimination _ h₁ h₂]
  have hJ : joint ((X.submatrix (siteSplit hmn) (siteSplit hmn)).submatrix
      (Sum.map id (siteSplit hkm)) (Sum.map id (siteSplit hkm))) =
      (X.submatrix (siteSplit (hkm.trans hmn)) (siteSplit (hkm.trans hmn))).submatrix
        (Sum.map (topJoin hkm hmn) id) (Sum.map (topJoin hkm hmn) id) := by
    unfold joint
    simp only [submatrix_submatrix]
    rw [siteSplit_comp]
  rw [hJ, dtn_reindex_interior]

/-- [definition] **The face at level `n`**: a positive definite symmetric real relation on `n` sites. -/
def RelationFace (n : ℕ) : Type := {X : Matrix (Fin n) (Fin n) ℝ // X.PosDef}

/-- [definition] **The elimination tower**: faces `RelationFace n`, restriction `eliminateTop`. -/
def eliminationTower : Tower.{0, 0} ℕ where
  Face := RelationFace
  restrict h X := ⟨eliminateTop h X.1, eliminateTop_posDef h X.2⟩
  restrict_refl m X := Subtype.ext (eliminateTop_refl m X.1)
  restrict_trans hkm hmn X := Subtype.ext (eliminateTop_trans hkm hmn X.2)

/-- [proved-derived; formal-checked] **Each restriction is `kron_exact`'s**: every interior-balanced state's
boundary bond lies on the graph of the restricted face with the full power preserved, and every boundary value
extends. -/
theorem eliminationTower_restrict_is_kron {m n : ℕ} (h : m ≤ n) (X : eliminationTower.Face n) :
    (∀ u : Fin (n - m) ⊕ Fin m → ℝ,
      (∀ i, (X.1.submatrix (siteSplit h) (siteSplit h) *ᵥ u) (Sum.inl i) = 0) →
        (Holonics.HolonCore.boundaryBond (X.1.submatrix (siteSplit h) (siteSplit h)) u).1 =
            (eliminationTower.restrict h X).1 *ᵥ
              (Holonics.HolonCore.boundaryBond (X.1.submatrix (siteSplit h) (siteSplit h)) u).2 ∧
          Holonics.HolonCore.power
              (Holonics.HolonCore.boundaryBond (X.1.submatrix (siteSplit h) (siteSplit h)) u) =
            u ⬝ᵥ (X.1.submatrix (siteSplit h) (siteSplit h) *ᵥ u)) ∧
      ∀ uB : Fin m → ℝ, ∃ u : Fin (n - m) ⊕ Fin m → ℝ,
        (∀ i, (X.1.submatrix (siteSplit h) (siteSplit h) *ᵥ u) (Sum.inl i) = 0) ∧ u ∘ Sum.inr = uB :=
  Holonics.HolonCore.kron_exact _
    (isUnit_det_of_posDef (posDef_toBlocks₁₁ (X.2.submatrix (siteSplit h).injective)))

/-- [proved-derived; formal-checked] Decoupled grounded sites restrict to themselves. -/
theorem eliminateTop_smul_one {m n : ℕ} (h : m ≤ n) (c : ℝ) :
    eliminateTop h (c • (1 : Matrix (Fin n) (Fin n) ℝ)) = c • 1 := by
  ext i j
  simp [eliminateTop, dtn, mul_apply, toBlocks₂₁, toBlocks₂₂, one_apply]

/-- [definition] **A continuing object**: the decoupled grounded sites of conductance `c > 0` at every level. -/
def scaledSection (c : ℝ) (hc : 0 < c) : eliminationTower.CompatibleSection where
  witness n := ⟨c • (1 : Matrix (Fin n) (Fin n) ℝ), PosDef.one.smul hc⟩
  compatible h := Subtype.ext (eliminateTop_smul_one h c)

/-- [proved-derived; formal-checked] **The elimination tower's gluing is plural**: `scaledSection 1` and
`scaledSection 2` are two continuing objects. -/
theorem eliminationTower_gluing : eliminationTower.GluingResult := by
  refine .plural ⟨scaledSection 1 one_pos⟩ fun hs => ?_
  have h := congrArg (fun s : eliminationTower.CompatibleSection => (s.witness 1).1 0 0)
    (hs.elim (scaledSection 1 one_pos) (scaledSection 2 two_pos))
  norm_num [scaledSection] at h

end Tower

/-! ## 5. The neck -/

section Neck

variable {K : Type*} [Field K] {I P Q : Type*} [Fintype I] [Fintype P] [Fintype Q] [DecidableEq I]

omit [Fintype P] [Fintype Q] in
/-- [proved-derived; formal-checked] **The neck block.** With no direct left–right coupling, the left–right block
of `Λ_DN` is `−B_L A⁻¹ B_R`: everything one end passes to the other passes through the interior. -/
theorem neck_block (L : Matrix (I ⊕ (P ⊕ Q)) (I ⊕ (P ⊕ Q)) K)
    (h0 : ∀ p q, L (Sum.inr (Sum.inl p)) (Sum.inr (Sum.inr q)) = 0) :
    (dtn L).toBlocks₁₂ =
      -(L.toBlocks₂₁.submatrix Sum.inl id * L.toBlocks₁₁⁻¹ * L.toBlocks₁₂.submatrix id Sum.inr) := by
  ext p q
  show L (Sum.inr (Sum.inl p)) (Sum.inr (Sum.inr q)) - _ = _
  rw [h0, zero_sub]
  rfl

omit [Fintype P] in
/-- [proved-derived; formal-checked] **The neck rank.** The left–right block of `Λ_DN` has rank at most
`rank B_L`, at most `rank B_R` and at most the interior's size. -/
theorem neck_rank (L : Matrix (I ⊕ (P ⊕ Q)) (I ⊕ (P ⊕ Q)) K)
    (h0 : ∀ p q, L (Sum.inr (Sum.inl p)) (Sum.inr (Sum.inr q)) = 0) :
    (dtn L).toBlocks₁₂.rank ≤ (L.toBlocks₂₁.submatrix Sum.inl id).rank ∧
      (dtn L).toBlocks₁₂.rank ≤ (L.toBlocks₁₂.submatrix id Sum.inr).rank ∧
      (dtn L).toBlocks₁₂.rank ≤ Fintype.card I := by
  have hl : (dtn L).toBlocks₁₂ = L.toBlocks₂₁.submatrix Sum.inl id *
      (L.toBlocks₁₁⁻¹ * -L.toBlocks₁₂.submatrix id Sum.inr) := by
    rw [neck_block L h0, Matrix.mul_neg, Matrix.mul_assoc, Matrix.mul_neg]
  have hr : (dtn L).toBlocks₁₂ = (-L.toBlocks₂₁.submatrix Sum.inl id * L.toBlocks₁₁⁻¹) *
      L.toBlocks₁₂.submatrix id Sum.inr := by
    rw [neck_block L h0, Matrix.neg_mul, Matrix.neg_mul]
  have h1 : (dtn L).toBlocks₁₂.rank ≤ (L.toBlocks₂₁.submatrix Sum.inl id).rank := by
    rw [hl]; exact rank_mul_le_left _ _
  refine ⟨h1, ?_, h1.trans (rank_le_card_width _)⟩
  rw [hr]; exact rank_mul_le_right _ _

end Neck

end Holonics.Holon.DtNTubeTower
