import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Dimension.Constructions
import Holonics.Holon.Complex
import Holonics.Transport.HolonicInteraction

/-!
# The contact material is a sheaf Laplacian

Source: #410's box "The contact material is a sheaf Laplacian (#408)", and the record
`research/records/2026-10-23_THE_CONTACTS_ARE_A_SHEAF_WEIGHT_TYING_REPRESENTS_THE_WORDS_AND_THE_SQUARE_LAW_IS_THE_SCATTERING_READ.md`,
§1. The record assembles a cellular sheaf from objects that already stand: the vertex stalks are the participating
Holons' states, an edge stalk is a contact's comparison space, the restriction maps are the contact charts, the
coboundary `δ` is the slip, and the sheaf Laplacian `δᵀ W δ` is the contact material `Σ_e w_e J_e* D J_e`
(`Transport/HolonicInteraction.contactForm`, atlas `contact.material`). This file proves that table's equations.

**Coordinates.** A stalk is a set of coordinates: the configuration's coordinates `ι` each lie over one vertex
(`vertexOf`) and the slip's coordinates `κ` each over one edge (`edgeOf`), so the stalk of `v` is the fibre of
`vertexOf` over `v`, and vertex and edge stalks may have any widths. The restriction maps of an edge `e` are the
blocks of two matrices `κ × ι` at the rows over `e`: the source's chart (`restrictSrc`) reads only the source's
stalk and the target's chart (`restrictTgt`) only the target's (`src_local`, `tgt_local`). This avoids dependent
stalk types; a block is recovered by restricting rows and columns to the fibres.

[proved-derived; formal-checked] What is proved.

1. **The slip is the coboundary** (§1). `(δx)_e = F_(tgt◁e) x_(tgt e) − F_(src◁e) x_(src e)`, each chart reading
   only its own end's stalk (`coboundary_apply`, through `restrictTgt_reads_tgt`, `restrictSrc_reads_src`), and
   `δx = 0` exactly when the two ends' restrictions agree on every edge: the kernel is the global sections, the
   states on which every contact agrees, where the contacts lock (`coboundary_eq_zero_iff`).
2. **The material is the sheaf Laplacian** (§2). With `J_e = P_e δ` the slip read on the edge's stalk (`edgeSlip`,
   `P_e` the stalk's mask) and `W = Σ_e w_e P_e D P_e` the block-diagonal weight (`edgeWeight`, whose entries are
   `w_e D` on each edge's block and zero between edges, `edgeWeight_apply`),
   `Σ_e w_e J_eᵀ D J_e = δᵀ W δ` (`material_eq_laplacian`), and the Dirichlet energy is the weighted sum of the
   slips' quadrances, `⟨x, M x⟩ = Σ_e w_e ⟨J_e x, D J_e x⟩` (`reading_material`).
3. **Positivity and the locks** (§3). Over an ordered field, with `w ≥ 0` and `D` positive semidefinite on each
   edge stalk, the material is positive semidefinite (`material_nonneg`); with `w > 0` and `D` definite on each
   edge stalk its kernel is `ker δ` (`material_ker_iff`), hence the global sections
   (`material_ker_iff_globalSection`). The plain sheaf Laplacian `D = 1` meets both hypotheses
   (`identity_definite`).
4. **The obstruction is the cokernel** (§4). An edge assignment `y` is glued by some state, `δx = y`, exactly when
   its class in `coker δ = (slip space)/(range δ)` vanishes (`glues_iff_class_zero`), and the index is the stalks'
   count: `dim ker δ − dim coker δ = |ι| − |κ| = Σ_v d_v − Σ_e d_e` (`index_eq`, `index_eq_stalks`, with
   `card_eq_sum_stalks`), by rank–nullity.
5. **The joins** (§5). The repository's contact form is this Laplacian: with the contacts' slip maps stacked into one
   coboundary over `Fin m × Fin r` (`stackSlip`) and their materials into one block-diagonal weight
   (`stackMaterial`), `contactForm w J D = material (stackSlip J) Prod.fst w (stackMaterial D)`
   (`contactForm_eq_material`), so `contactForm w J D = δᵀ W δ` (`contactForm_eq_laplacian`). A graph with one
   linear transport per edge on uniform stalks `𝕜^d` (`ofTransports`) is a sheaf whose coboundary is
   `Holon/Complex.blockIncidence`, the covariant incidence `T_e φ(t e) − φ(s e)` (`ofTransports_coboundary`).
6. **Holonomy decides the cohomology on a cycle** (§6). On the triangle with scalar stalks over `ℚ`: the constant
   sheaf (every transport `1`) has the nonzero global section `x = 1` (`constant_triangle_section`) and an edge
   assignment that does not glue, because every slip sums to zero around the cycle (`constant_triangle_slip_sum`,
   `constant_triangle_obstruction`); the twisted sheaf (one transport `−1`, holonomy `−1`) has no global section but
   zero (`twisted_triangle_no_section`) and glues every edge assignment, by the explicit state
   `x₀ = −(y₀ + y₁ + y₂)/2` (`twisted_triangle_glues`): `1 − hol = 2` is invertible.

Limits. Stalks are coordinate sets, not modules attached to cells, and the restriction maps are matrices; the sheaf
is on a graph (vertices and edges), not on a higher cell complex, so `H¹` here is the edge cokernel and no
`H²` is defined. The record's claim that, with invertible restriction maps, a global section exists exactly when the
holonomy around each cycle fixes it is shown only on the triangle's two witnesses (§6), not for every graph; its
general form stands beside `Holon/Complex.block_cell_curvature`. The offsets' least squares (`‖δx − b‖²_W`, the
residual `b − δx*` as an `H¹` representative) and the tower's three returns read as unique, plural and obstructed
sections (`Foundation/ContinuingTower`, `Foundation/GluingPassage`) are not restated. The weight `D` is one matrix on
the slip space of which only the edge blocks are read.

The computational object is the helical pair interaction: a contact compares two Holons through their charts, and
its slip is the coboundary's value on that edge. Of the winding guide's six general objects this touches the pair
(the contact's slip, its material and its quadrance) and cell holonomy (the global sections, the obstruction class
and the triangle's holonomy deciding them); the helix, faces and placement, the tube and the tower thread stay
attached.

Consumers: #410's box on the contact material as a sheaf Laplacian, and #408 (the contact and chain laws);
`Transport/HolonicInteraction.contactForm` (atlas `contact.material`), `Holon/Complex.blockIncidence`.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.Holon.SheafLaplacian

open Matrix Module

/-! ## 1. The cellular sheaf and its coboundary -/

/-- [definition] **A cellular sheaf on a finite graph, in coordinates.** Edges `ε` run from `src` to `tgt` among the
vertices `ν`; each configuration coordinate lies over a vertex and each slip coordinate over an edge, so a stalk is a
fibre. The two restriction maps are the rows of `restrictSrc` and `restrictTgt` over an edge; each reads only the
stalk of its own end. -/
structure GraphSheaf (𝕜 ν ε ι κ : Type*) [Zero 𝕜] where
  /-- The source of an edge. -/
  src : ε → ν
  /-- The target of an edge. -/
  tgt : ε → ν
  /-- The vertex a configuration coordinate lies over. -/
  vertexOf : ι → ν
  /-- The edge a slip coordinate lies over. -/
  edgeOf : κ → ε
  /-- The source's restriction maps, all edges at once. -/
  restrictSrc : Matrix κ ι 𝕜
  /-- The target's restriction maps, all edges at once. -/
  restrictTgt : Matrix κ ι 𝕜
  src_local : ∀ k j, vertexOf j ≠ src (edgeOf k) → restrictSrc k j = 0
  tgt_local : ∀ k j, vertexOf j ≠ tgt (edgeOf k) → restrictTgt k j = 0

namespace GraphSheaf

variable {𝕜 ν ε ι κ : Type*} [CommRing 𝕜] [Fintype ι] [DecidableEq ν] (S : GraphSheaf 𝕜 ν ε ι κ)

/-- [definition] **The coboundary, the slip**: `δ = F_tgt − F_src`. -/
def coboundary : Matrix κ ι 𝕜 := S.restrictTgt - S.restrictSrc

/-- [definition] A state read at one vertex's stalk (zero off it). -/
def atVertex (x : ι → 𝕜) (v : ν) : ι → 𝕜 := fun j => if S.vertexOf j = v then x j else 0

/-- [proved-derived; formal-checked] The target's chart reads only the target's stalk. -/
theorem restrictTgt_reads_tgt (x : ι → 𝕜) (k : κ) :
    (S.restrictTgt *ᵥ x) k = (S.restrictTgt *ᵥ S.atVertex x (S.tgt (S.edgeOf k))) k := by
  simp only [mulVec, dotProduct, atVertex]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : S.vertexOf j = S.tgt (S.edgeOf k)
  · simp [h]
  · simp [h, S.tgt_local k j h]

/-- [proved-derived; formal-checked] The source's chart reads only the source's stalk. -/
theorem restrictSrc_reads_src (x : ι → 𝕜) (k : κ) :
    (S.restrictSrc *ᵥ x) k = (S.restrictSrc *ᵥ S.atVertex x (S.src (S.edgeOf k))) k := by
  simp only [mulVec, dotProduct, atVertex]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : S.vertexOf j = S.src (S.edgeOf k)
  · simp [h]
  · simp [h, S.src_local k j h]

/-- [proved-derived; formal-checked] **The slip on an edge**:
`(δx)_e = F_(tgt◁e) x_(tgt e) − F_(src◁e) x_(src e)`. -/
theorem coboundary_apply (x : ι → 𝕜) (k : κ) :
    (S.coboundary *ᵥ x) k =
      (S.restrictTgt *ᵥ S.atVertex x (S.tgt (S.edgeOf k))) k -
        (S.restrictSrc *ᵥ S.atVertex x (S.src (S.edgeOf k))) k := by
  rw [coboundary, sub_mulVec, Pi.sub_apply, ← restrictTgt_reads_tgt, ← restrictSrc_reads_src]

/-- [definition] **A global section**: on every edge the two ends' restrictions agree. -/
def IsGlobalSection (x : ι → 𝕜) : Prop :=
  ∀ k, (S.restrictTgt *ᵥ S.atVertex x (S.tgt (S.edgeOf k))) k =
    (S.restrictSrc *ᵥ S.atVertex x (S.src (S.edgeOf k))) k

/-- [proved-derived; formal-checked] **`H⁰ = ker δ` is the global sections**: no slip exactly where every contact
agrees. -/
theorem coboundary_eq_zero_iff (x : ι → 𝕜) : S.coboundary *ᵥ x = 0 ↔ S.IsGlobalSection x := by
  constructor
  · intro h k
    have := congrFun h k
    rw [coboundary_apply, Pi.zero_apply, sub_eq_zero] at this
    exact this
  · intro h
    funext k
    rw [coboundary_apply, Pi.zero_apply, sub_eq_zero]
    exact h k

end GraphSheaf

/-! ## 2. The material is the sheaf Laplacian -/

section Material

variable {𝕜 ε ι κ : Type*} [CommRing 𝕜] [Fintype κ] [DecidableEq κ] [DecidableEq ε]

/-- [definition] The mask of an edge's stalk on the slip space. -/
def edgeMask (edgeOf : κ → ε) (e : ε) : Matrix κ κ 𝕜 :=
  diagonal fun k => if edgeOf k = e then 1 else 0

/-- [definition] **An edge's slip map** `J_e = P_e δ`: the coboundary read on that edge's stalk. -/
def edgeSlip (δ : Matrix κ ι 𝕜) (edgeOf : κ → ε) (e : ε) : Matrix κ ι 𝕜 := edgeMask edgeOf e * δ

/-- [proved-derived; formal-checked] An edge's slip is the coboundary on its stalk and zero off it. -/
theorem edgeSlip_mulVec_apply [Fintype ι] (δ : Matrix κ ι 𝕜) (edgeOf : κ → ε) (e : ε) (x : ι → 𝕜)
    (k : κ) : (edgeSlip δ edgeOf e *ᵥ x) k = if edgeOf k = e then (δ *ᵥ x) k else 0 := by
  rw [edgeSlip, edgeMask]
  simp only [mulVec, dotProduct, diagonal_mul]
  split_ifs <;> simp

variable [Fintype ε]

/-- [definition] **The contact material** `Σ_e w_e J_eᵀ D J_e`, summed over the edges. -/
def material (δ : Matrix κ ι 𝕜) (edgeOf : κ → ε) (w : ε → 𝕜) (D : Matrix κ κ 𝕜) : Matrix ι ι 𝕜 :=
  ∑ e, w e • ((edgeSlip δ edgeOf e)ᵀ * D * edgeSlip δ edgeOf e)

/-- [definition] **The block-diagonal weight** `W = Σ_e w_e P_e D P_e`. -/
def edgeWeight (edgeOf : κ → ε) (w : ε → 𝕜) (D : Matrix κ κ 𝕜) : Matrix κ κ 𝕜 :=
  ∑ e, w e • (edgeMask edgeOf e * D * edgeMask edgeOf e)

/-- [proved-derived; formal-checked] The weight is `w_e D` on each edge's block and zero between edges. -/
theorem edgeWeight_apply (edgeOf : κ → ε) (w : ε → 𝕜) (D : Matrix κ κ 𝕜) (k k' : κ) :
    edgeWeight edgeOf w D k k' = if edgeOf k = edgeOf k' then w (edgeOf k) * D k k' else 0 := by
  simp only [edgeWeight, edgeMask, Matrix.sum_apply, Matrix.smul_apply, diagonal_mul,
    mul_diagonal, smul_eq_mul]
  by_cases h : edgeOf k = edgeOf k'
  · rw [if_pos h, Finset.sum_eq_single (edgeOf k)]
    · simp [h]
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun e _ => ?_
    by_cases he : edgeOf k = e
    · subst he; simp [Ne.symm h]
    · simp [he]

/-- [proved-derived; formal-checked] **The material is the sheaf Laplacian**: `Σ_e w_e J_eᵀ D J_e = δᵀ W δ`. -/
theorem material_eq_laplacian (δ : Matrix κ ι 𝕜) (edgeOf : κ → ε) (w : ε → 𝕜) (D : Matrix κ κ 𝕜) :
    material δ edgeOf w D = δᵀ * edgeWeight edgeOf w D * δ := by
  rw [material, edgeWeight, Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Matrix.mul_smul, Matrix.smul_mul, edgeSlip, transpose_mul, edgeMask, diagonal_transpose]
  simp only [Matrix.mul_assoc]

variable [Fintype ι]

/-- [definition] The quadratic reading `⟨x, M x⟩`. -/
def reading (M : Matrix ι ι 𝕜) (x : ι → 𝕜) : 𝕜 := x ⬝ᵥ (M *ᵥ x)

/-- [proved-derived; formal-checked] **The Dirichlet energy** is the weighted sum of the slips' quadrances,
`⟨x, M x⟩ = Σ_e w_e ⟨J_e x, D J_e x⟩`. -/
theorem reading_material (δ : Matrix κ ι 𝕜) (edgeOf : κ → ε) (w : ε → 𝕜) (D : Matrix κ κ 𝕜)
    (x : ι → 𝕜) :
    reading (material δ edgeOf w D) x =
      ∑ e, w e * ((edgeSlip δ edgeOf e *ᵥ x) ⬝ᵥ (D *ᵥ (edgeSlip δ edgeOf e *ᵥ x))) := by
  rw [reading, material, Matrix.sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Matrix.mul_assoc, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

/-- [proved-derived; formal-checked] The material acts through the slip: `M x = δᵀ W δ x`. -/
theorem material_mulVec (δ : Matrix κ ι 𝕜) (edgeOf : κ → ε) (w : ε → 𝕜) (D : Matrix κ κ 𝕜)
    (x : ι → 𝕜) :
    material δ edgeOf w D *ᵥ x = δᵀ *ᵥ (edgeWeight edgeOf w D *ᵥ (δ *ᵥ x)) := by
  rw [material_eq_laplacian, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

end Material

/-! ## 3. Positivity and the locks -/

section Ordered

variable {𝕜 ε ι κ : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [Fintype ι] [Fintype κ] [DecidableEq κ] [DecidableEq ε]

/-- [definition] A slip vector supported on one edge's stalk. -/
def SupportedOn (edgeOf : κ → ε) (e : ε) (s : κ → 𝕜) : Prop := ∀ k, edgeOf k ≠ e → s k = 0

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- [proved-derived; formal-checked] An edge's slip lies on its own stalk. -/
theorem edgeSlip_supported (δ : Matrix κ ι 𝕜) (edgeOf : κ → ε) (e : ε) (x : ι → 𝕜) :
    SupportedOn edgeOf e (edgeSlip δ edgeOf e *ᵥ x) := fun k hk => by
  rw [edgeSlip_mulVec_apply, if_neg hk]

variable [Fintype ε]

/-- [proved-derived; formal-checked] **The material is positive semidefinite** for nonnegative weights and an edge
material positive semidefinite on each edge's stalk. -/
theorem material_nonneg (δ : Matrix κ ι 𝕜) (edgeOf : κ → ε) (w : ε → 𝕜) (D : Matrix κ κ 𝕜)
    (hw : ∀ e, 0 ≤ w e) (hD : ∀ e s, SupportedOn edgeOf e s → 0 ≤ s ⬝ᵥ (D *ᵥ s)) (x : ι → 𝕜) :
    0 ≤ reading (material δ edgeOf w D) x := by
  rw [reading_material]
  exact Finset.sum_nonneg fun e _ => mul_nonneg (hw e) (hD e _ (edgeSlip_supported δ edgeOf e x))

/-- [proved-derived; formal-checked] **The material's kernel is `ker δ`** for positive weights and an edge material
definite on each edge's stalk. -/
theorem material_ker_iff (δ : Matrix κ ι 𝕜) (edgeOf : κ → ε) (w : ε → 𝕜) (D : Matrix κ κ 𝕜)
    (hw : ∀ e, 0 < w e) (hD : ∀ e s, SupportedOn edgeOf e s → 0 ≤ s ⬝ᵥ (D *ᵥ s))
    (hdef : ∀ e s, SupportedOn edgeOf e s → s ⬝ᵥ (D *ᵥ s) = 0 → s = 0) (x : ι → 𝕜) :
    material δ edgeOf w D *ᵥ x = 0 ↔ δ *ᵥ x = 0 := by
  constructor
  · intro h
    have hread : reading (material δ edgeOf w D) x = 0 := by rw [reading, h, dotProduct_zero]
    rw [reading_material] at hread
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg fun e _ =>
      mul_nonneg (hw e).le (hD e _ (edgeSlip_supported δ edgeOf e x))).mp hread
    funext k
    have he := hterm (edgeOf k) (Finset.mem_univ _)
    have hq : (edgeSlip δ edgeOf (edgeOf k) *ᵥ x) ⬝ᵥ
        (D *ᵥ (edgeSlip δ edgeOf (edgeOf k) *ᵥ x)) = 0 :=
      (mul_eq_zero.mp he).resolve_left (hw _).ne'
    have hs := congrFun (hdef _ _ (edgeSlip_supported δ edgeOf (edgeOf k) x) hq) k
    rw [edgeSlip_mulVec_apply, if_pos rfl] at hs
    exact hs
  · intro h
    rw [material_mulVec, h, mulVec_zero, mulVec_zero]

/-- [proved-derived; formal-checked] **The locks**: the material of a sheaf's coboundary vanishes on a state exactly
when the state is a global section. -/
theorem material_ker_iff_globalSection {ν : Type*} [DecidableEq ν] (S : GraphSheaf 𝕜 ν ε ι κ)
    (w : ε → 𝕜) (D : Matrix κ κ 𝕜) (hw : ∀ e, 0 < w e)
    (hD : ∀ e s, SupportedOn S.edgeOf e s → 0 ≤ s ⬝ᵥ (D *ᵥ s))
    (hdef : ∀ e s, SupportedOn S.edgeOf e s → s ⬝ᵥ (D *ᵥ s) = 0 → s = 0) (x : ι → 𝕜) :
    material S.coboundary S.edgeOf w D *ᵥ x = 0 ↔ S.IsGlobalSection x := by
  rw [material_ker_iff _ _ w D hw hD hdef, GraphSheaf.coboundary_eq_zero_iff]

omit [Fintype ε] [DecidableEq ε] in
/-- [proved-derived; formal-checked] The plain sheaf Laplacian's material `D = 1` is positive semidefinite and
definite on every stalk. -/
theorem identity_definite (edgeOf : κ → ε) :
    (∀ e (s : κ → 𝕜), SupportedOn edgeOf e s → 0 ≤ s ⬝ᵥ ((1 : Matrix κ κ 𝕜) *ᵥ s)) ∧
      ∀ e (s : κ → 𝕜), SupportedOn edgeOf e s → s ⬝ᵥ ((1 : Matrix κ κ 𝕜) *ᵥ s) = 0 → s = 0 := by
  refine ⟨fun e s _ => ?_, fun e s _ h => ?_⟩
  · rw [one_mulVec]; exact Finset.sum_nonneg fun k _ => mul_self_nonneg (s k)
  · rw [one_mulVec, dotProduct_self_eq_zero] at h; exact h

end Ordered

/-! ## 4. The obstruction is the cokernel -/

section Cokernel

variable {𝕜 ι κ : Type*} [Field 𝕜] [Fintype ι]

/-- [definition] An edge assignment **glues** when some state's slip is it. -/
def Glues (δ : Matrix κ ι 𝕜) (y : κ → 𝕜) : Prop := ∃ x, δ *ᵥ x = y

/-- [definition] **`H¹ = coker δ`**: edge assignments modulo the slips. -/
abbrev Cokernel (δ : Matrix κ ι 𝕜) := (κ → 𝕜) ⧸ LinearMap.range δ.mulVecLin

/-- [proved-derived; formal-checked] **The gluing obstruction**: an edge assignment glues exactly when its class in
the cokernel vanishes. -/
theorem glues_iff_class_zero (δ : Matrix κ ι 𝕜) (y : κ → 𝕜) :
    Glues δ y ↔ (Submodule.Quotient.mk y : Cokernel δ) = 0 := by
  rw [Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]
  simp [Glues]

variable [Fintype κ]

/-- [proved-derived; formal-checked] **The index**: `dim ker δ − dim coker δ = |ι| − |κ|`, by rank–nullity. -/
theorem index_eq (δ : Matrix κ ι 𝕜) :
    (finrank 𝕜 (LinearMap.ker δ.mulVecLin) : ℤ) - finrank 𝕜 (Cokernel δ) =
      Fintype.card ι - Fintype.card κ := by
  have h1 := LinearMap.finrank_range_add_finrank_ker δ.mulVecLin
  have h2 : finrank 𝕜 (Cokernel δ) + finrank 𝕜 (LinearMap.range δ.mulVecLin) = Fintype.card κ := by
    rw [Submodule.finrank_quotient_add_finrank, Module.finrank_fintype_fun_eq_card]
  rw [Module.finrank_fintype_fun_eq_card] at h1
  omega

omit [Field 𝕜] [Fintype ι] [Fintype κ] in
/-- [proved-standard; formal-checked] A coordinate set's size is the sum of its fibres' sizes. -/
theorem card_eq_sum_stalks {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β] (f : α → β) :
    Fintype.card α = ∑ b, (Finset.univ.filter fun a => f a = b).card := by
  rw [← Finset.card_univ]
  exact Finset.card_eq_sum_card_fiberwise fun a _ => Finset.mem_univ (f a)

/-- [proved-derived; formal-checked] **The index is the stalks' count**:
`dim ker δ − dim coker δ = Σ_v d_v − Σ_e d_e`. -/
theorem index_eq_stalks {ν ε : Type*} [Fintype ν] [DecidableEq ν] [Fintype ε] [DecidableEq ε]
    (S : GraphSheaf 𝕜 ν ε ι κ) :
    (finrank 𝕜 (LinearMap.ker S.coboundary.mulVecLin) : ℤ) - finrank 𝕜 (Cokernel S.coboundary) =
      (∑ v, ((Finset.univ.filter fun j => S.vertexOf j = v).card : ℤ)) -
        ∑ e, ((Finset.univ.filter fun k => S.edgeOf k = e).card : ℤ) := by
  rw [index_eq, card_eq_sum_stalks S.vertexOf, card_eq_sum_stalks S.edgeOf]
  push_cast
  rfl

end Cokernel

/-! ## 5. The joins: the contact form and the block incidence -/

section ContactForm

open Holonics.Transport.HolonicInteraction

variable {n r m : ℕ}

/-- [definition] The contacts' slip maps stacked into one coboundary over `Fin m × Fin r`. -/
def stackSlip (J : Fin m → Matrix (Fin r) (Fin n) ℚ) : Matrix (Fin m × Fin r) (Fin n) ℚ :=
  Matrix.of fun k j => J k.1 k.2 j

/-- [definition] The contacts' materials as one weight on the stacked slip space (only the edge blocks are read). -/
def stackMaterial (D : Fin m → Matrix (Fin r) (Fin r) ℚ) : Matrix (Fin m × Fin r) (Fin m × Fin r) ℚ :=
  Matrix.of fun k k' => D k.1 k.2 k'.2

/-- [definition] The embedding of one contact's comparison space into the stacked slip space. -/
def stackEmbed (f : Fin m) : Matrix (Fin m × Fin r) (Fin r) ℚ :=
  Matrix.of fun k i => if k.1 = f ∧ k.2 = i then 1 else 0

/-- [proved-derived; formal-checked] An edge's slip in the stacked coboundary is its contact's slip map, embedded. -/
theorem edgeSlip_stackSlip (J : Fin m → Matrix (Fin r) (Fin n) ℚ) (f : Fin m) :
    edgeSlip (stackSlip J) Prod.fst f = stackEmbed f * J f := by
  ext ⟨g, i⟩ j
  rw [edgeSlip, edgeMask, diagonal_mul, mul_apply]
  by_cases h : g = f
  · subst h
    simp [stackSlip, stackEmbed]
  · simp [stackSlip, stackEmbed, h]

/-- [proved-derived; formal-checked] The stacked material read back on one contact's space is its material. -/
theorem stackEmbed_material (D : Fin m → Matrix (Fin r) (Fin r) ℚ) (f : Fin m) :
    (stackEmbed f)ᵀ * stackMaterial D * stackEmbed f = D f := by
  ext i i'
  simp only [mul_apply, transpose_apply, stackEmbed, stackMaterial, Matrix.of_apply,
    Fintype.sum_prod_type, ite_and, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero]
  simp [Finset.sum_ite_eq']

/-- [proved-derived; formal-checked] **The repository's contact form is this material**:
`contactForm w J D = Σ_e w_e (P_e δ)ᵀ D̂ (P_e δ)` for the stacked coboundary. -/
theorem contactForm_eq_material (w : Fin m → ℚ) (J : Fin m → Matrix (Fin r) (Fin n) ℚ)
    (D : Fin m → Matrix (Fin r) (Fin r) ℚ) :
    contactForm w J D = material (stackSlip J) Prod.fst w (stackMaterial D) := by
  rw [contactForm, material]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [faceForm, edgeSlip_stackSlip, transpose_mul, ← stackEmbed_material D f]
  simp only [Matrix.mul_assoc]

/-- [proved-derived; formal-checked] **`Σ_e w_e J_e* D J_e = δᵀ W δ`** for the repository's contact form. -/
theorem contactForm_eq_laplacian (w : Fin m → ℚ) (J : Fin m → Matrix (Fin r) (Fin n) ℚ)
    (D : Fin m → Matrix (Fin r) (Fin r) ℚ) :
    contactForm w J D = (stackSlip J)ᵀ * edgeWeight Prod.fst w (stackMaterial D) * stackSlip J := by
  rw [contactForm_eq_material, material_eq_laplacian]

end ContactForm

section BlockIncidence

variable {𝕜 ν ε : Type*} [Field 𝕜] [Fintype ν] [DecidableEq ν] {d : ℕ}

/-- [definition] **A graph with one linear transport per edge** on uniform stalks `𝕜^d`, as a sheaf: the source's
chart is the identity on the source's stalk and the target's chart is the transport `T_e` on the target's. -/
def ofTransports (src tgt : ε → ν) (T : ε → Matrix (Fin d) (Fin d) 𝕜) :
    GraphSheaf 𝕜 ν ε (ν × Fin d) (ε × Fin d) where
  src := src
  tgt := tgt
  vertexOf := Prod.fst
  edgeOf := Prod.fst
  restrictSrc := Matrix.of fun k j => if j.1 = src k.1 ∧ k.2 = j.2 then 1 else 0
  restrictTgt := Matrix.of fun k j => if j.1 = tgt k.1 then T k.1 k.2 j.2 else 0
  src_local k j h := by simp [h]
  tgt_local k j h := by simp [h]

/-- [proved-derived; formal-checked] **The join to `Holon/Complex`**: the coboundary of a transport sheaf is the
block incidence `T_e φ(t e) − φ(s e)`. -/
theorem ofTransports_coboundary (src tgt : ε → ν) (T : ε → Matrix (Fin d) (Fin d) 𝕜)
    (x : ν × Fin d → 𝕜) (e : ε) (i : Fin d) :
    ((ofTransports src tgt T).coboundary *ᵥ x) (e, i) =
      Holonics.HolonCore.blockIncidence src tgt (fun e => (T e).mulVecLin) (fun v a => x (v, a)) e i := by
  have h1 : ∀ y : ν × Fin d → 𝕜, ∑ v, ∑ a, (if v = tgt e then T e i a else 0) * y (v, a) =
      ∑ a, T e i a * y (tgt e, a) := fun y => by
    rw [Finset.sum_eq_single (tgt e)]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  have h2 : ∀ y : ν × Fin d → 𝕜,
      ∑ v, ∑ a, (if v = src e then (if i = a then (1 : 𝕜) else 0) else 0) * y (v, a) = y (src e, i) :=
    fun y => by
    rw [Finset.sum_eq_single (src e)]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  simp only [GraphSheaf.coboundary, ofTransports, Pi.sub_apply, mulVec, dotProduct,
    Fintype.sum_prod_type, ite_and, Holonics.HolonCore.blockIncidence, Matrix.mulVecLin_apply]
  simp only [sub_mul, Finset.sum_sub_distrib, Matrix.sub_apply, Matrix.of_apply]
  rw [h1, h2]

end BlockIncidence

/-! ## 6. Holonomy decides the cohomology on a cycle -/

section Triangle

/-- [definition] The triangle `0 → 1 → 2 → 0` with scalar stalks and edge transports `t`. -/
def triangle (t : Fin 3 → ℚ) : GraphSheaf ℚ (Fin 3) (Fin 3) (Fin 3 × Fin 1) (Fin 3 × Fin 1) :=
  ofTransports id (fun e => e + 1) fun e => !![t e]

theorem triangle_slip (t : Fin 3 → ℚ) (x : Fin 3 × Fin 1 → ℚ) (e : Fin 3) :
    ((triangle t).coboundary *ᵥ x) (e, 0) = t e * x (e + 1, 0) - x (e, 0) := by
  rw [triangle, ofTransports_coboundary]
  simp [Holonics.HolonCore.blockIncidence, dotProduct]

/-- [definition] The constant sheaf on the triangle: every transport `1`, holonomy `1`. -/
def constantTriangle : GraphSheaf ℚ (Fin 3) (Fin 3) (Fin 3 × Fin 1) (Fin 3 × Fin 1) := triangle fun _ => 1

/-- [definition] The twisted sheaf on the triangle: the closing transport `−1`, holonomy `−1`. -/
def twistedTriangle : GraphSheaf ℚ (Fin 3) (Fin 3) (Fin 3 × Fin 1) (Fin 3 × Fin 1) :=
  triangle ![1, 1, -1]

theorem fin1_eq (i : Fin 1) : i = 0 := Subsingleton.elim _ _

/-- [proved-derived; formal-checked] The constant sheaf has the nonzero global section `x = 1`. -/
theorem constant_triangle_section : constantTriangle.coboundary *ᵥ (fun _ => 1) = 0 := by
  funext ⟨e, i⟩
  rw [fin1_eq i, constantTriangle, triangle_slip]
  simp

/-- [proved-derived; formal-checked] On the constant sheaf every slip sums to zero around the cycle. -/
theorem constant_triangle_slip_sum (x : Fin 3 × Fin 1 → ℚ) :
    ∑ e : Fin 3, (constantTriangle.coboundary *ᵥ x) (e, 0) = 0 := by
  simp only [constantTriangle, triangle_slip, Fin.sum_univ_three, one_mul]
  have h1 : (0 : Fin 3) + 1 = 1 := rfl
  have h2 : (1 : Fin 3) + 1 = 2 := rfl
  have h3 : (2 : Fin 3) + 1 = 0 := rfl
  rw [h1, h2, h3]
  ring

/-- [proved-derived; formal-checked] **A nonzero obstruction class**: on the constant sheaf the assignment `1` on one
edge and `0` on the others does not glue. -/
theorem constant_triangle_obstruction :
    ¬ Glues constantTriangle.coboundary (fun k => if k = ((0 : Fin 3), (0 : Fin 1)) then 1 else 0) := by
  rintro ⟨x, hx⟩
  have h := constant_triangle_slip_sum x
  rw [hx] at h
  simp at h

/-- [proved-derived; formal-checked] **Holonomy `−1` leaves no global section but zero.** -/
theorem twisted_triangle_no_section (x : Fin 3 × Fin 1 → ℚ) (hx : twistedTriangle.coboundary *ᵥ x = 0) :
    x = 0 := by
  have e0 := congrFun hx ((0 : Fin 3), (0 : Fin 1))
  have e1 := congrFun hx ((1 : Fin 3), (0 : Fin 1))
  have e2 := congrFun hx ((2 : Fin 3), (0 : Fin 1))
  rw [twistedTriangle, triangle_slip] at e0 e1 e2
  norm_num [Matrix.vecHead, Matrix.vecTail] at e0 e1 e2
  have h2 : (1 : Fin 3) + 1 = 2 := rfl
  have h3 : (2 : Fin 3) + 1 = 0 := rfl
  have t2 : (![1, 1, -1] : Fin 3 → ℚ) 2 = -1 := rfl
  rw [h2] at e1
  rw [h3, t2] at e2
  have z0 : x (0, 0) = 0 := by linarith
  have z1 : x (1, 0) = 0 := by linarith
  have z2 : x (2, 0) = 0 := by linarith
  funext ⟨v, i⟩
  rw [fin1_eq i]
  fin_cases v <;> simp [z0, z1, z2]

/-- [proved-derived; formal-checked] **Holonomy `−1` glues every edge assignment**, by the state
`x₀ = −(y₀ + y₁ + y₂)/2`, `x₁ = x₀ + y₀`, `x₂ = x₁ + y₁`: `1 − hol = 2` is invertible. -/
theorem twisted_triangle_glues (y : Fin 3 × Fin 1 → ℚ) : Glues twistedTriangle.coboundary y := by
  set x0 := -(y (0, 0) + y (1, 0) + y (2, 0)) / 2
  refine ⟨fun k => if k.1 = 0 then x0 else if k.1 = 1 then x0 + y (0, 0) else x0 + y (0, 0) + y (1, 0), ?_⟩
  funext ⟨e, i⟩
  rw [fin1_eq i, twistedTriangle, triangle_slip]
  fin_cases e
  · simp
  · simp
  · simp only [Fin.reduceFinMk, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    have h3 : (2 : Fin 3) + 1 = 0 := rfl
    simp [h3, x0]
    ring

end Triangle

end Holonics.Holon.SheafLaplacian
