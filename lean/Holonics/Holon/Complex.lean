import Holonics.Holon.Dirac
import Holonics.Transport.CellHolonomy

/-!
# Holon.Complex: connection-valued incidence and its curvature face

[definition] The complex facet `K, ∂_A`: on the triangle, the covariant incidence
`(d_A φ)_(ij) = g_ij φ_j − φ_i` with edge transports `g ∈ 𝕜ˣ`, and the covariant face coboundary
transporting to vertex `0`.

[proved-derived; formal-checked] `d_A² = (hol − 1)` on the base value, with `hol` the owner's
`CellHolonomy.triangleHolonomy` (`dA_squared`); the Kirchhoff structure of `d_A` is Dirac for
every connection (`connection_isDirac`: neutrality uses only the adjoint pair); every exact effort
is closed exactly when the holonomy is trivial (`exact_closed_iff_flat`), so a pure gauge is flat
(`pure_gauge_is_flat`, composing `pure_gauge_has_trivial_holonomy`). Witness: holonomy `2`, Dirac
structure intact, `d_A² δ₀ = 1` (`curved_witness`).

On a general graph with edge transports (`connectionIncidence`), the covariant difference
telescopes along any walk (`walkRead_connection`), so on every cell given as a closed walk the
exact effort reads `(hol − 1) φ(base)` (`cell_curvature`), while the Kirchhoff structure is Dirac
for every connection (`connectionIncidence_isDirac`). Witness: an orientation-reversing seam
(`hol = −1`) reads `−2` (`seam_curvature_witness`).

[proved-derived; formal-checked] **Block transports** (rebuild step 4 addition 2, review F4): each
vertex carries a value in a module `V` and each edge a linear transport `T_e : V → V`, not
necessarily invertible (a partial isometry is admitted), with `(d_A φ)_e = T_e φ(t e) − φ(s e)`
(`blockIncidence`). The scalar incidence is its unit-width case
(`blockIncidence_eq_connectionIncidence`). The covariant difference telescopes along every walk
(`blockWalkRead_incidence`), so on a cell given as a closed walk the exact effort reads
`(hol − 1) φ(base)` (`block_cell_curvature`), and a flat cell (`hol = 1`) closes every exact
effort: the covariant face coboundary composes with `d_A` to zero (`block_flat_closed`, `∂² = 0`
covariantly). Vertices of different widths embed in one `V`; the Kirchhoff structure of the block
matrix is Dirac for every block (`Holon/Dirac.kirchhoff_isDirac`, stated for every incidence).
-/

noncomputable section

namespace Holonics.HolonCore

open Matrix
open Holonics.Transport.CellHolonomy

variable {𝕜 : Type*} [Field 𝕜]

/-- [definition] **The connection-valued incidence** of the triangle with edge transports
`g₀₁, g₁₂, g₂₀ ∈ 𝕜ˣ`: `(d_A φ)_(ij) = g_ij φ_j − φ_i` (covariant difference). -/
def dA0 (g01 g12 g20 : 𝕜ˣ) : Matrix (Fin 3) (Fin 3) 𝕜 :=
  !![-1, (g01 : 𝕜), 0; 0, -1, (g12 : 𝕜); (g20 : 𝕜), 0, -1]

/-- [definition] The covariant face coboundary, transporting each edge value to vertex `0`:
`(d_A ω)_f = ω₀₁ + g₀₁ ω₁₂ + g₀₁ g₁₂ ω₂₀`. -/
def dA1 (g01 g12 : 𝕜ˣ) : Matrix (Fin 1) (Fin 3) 𝕜 :=
  !![1, (g01 : 𝕜), (g01 : 𝕜) * g12]

/-- [proved-derived; formal-checked] **`d_A² = F_A`.** The square of the covariant incidence is
multiplication of the base value by the curvature `hol − 1`, where `hol` is
`CellHolonomy.triangleHolonomy`. -/
theorem dA_squared (g01 g12 g20 : 𝕜ˣ) (φ : Fin 3 → 𝕜) :
    (dA1 g01 g12 *ᵥ (dA0 g01 g12 g20 *ᵥ φ)) 0 =
      (((triangleHolonomy g01 g12 g20 : 𝕜ˣ) : 𝕜) - 1) * φ 0 := by
  simp [dA0, dA1, triangleHolonomy, mulVec, dotProduct, Fin.sum_univ_three]
  ring

/-- [proved-derived; formal-checked] **Power neutrality holds for every connection**: the
Kirchhoff structure of `d_A` is Dirac whatever the transports (neutrality uses only the adjoint
pair `d_A`, `d_Aᵀ`). -/
theorem connection_isDirac (g01 g12 g20 : 𝕜ˣ) :
    IsDirac (bondForm 𝕜 (Fin 3)) (kirchhoff (dA0 g01 g12 g20)) :=
  kirchhoff_isDirac _

/-- [proved-derived; formal-checked] **Exactness needs zero curvature.** Every exact effort is
covariantly closed exactly when the holonomy is trivial. -/
theorem exact_closed_iff_flat (g01 g12 g20 : 𝕜ˣ) :
    (∀ φ, dA1 g01 g12 *ᵥ (dA0 g01 g12 g20 *ᵥ φ) = 0) ↔ triangleHolonomy g01 g12 g20 = 1 := by
  constructor
  · intro h
    have := congrFun (h (Pi.single 0 1)) 0
    rw [dA_squared] at this
    simp at this
    exact Units.val_eq_one.mp (sub_eq_zero.mp this)
  · intro h φ
    funext i
    fin_cases i
    simp only [Fin.zero_eta, Fin.isValue, Pi.zero_apply]
    rw [dA_squared, h, Units.val_one, sub_self, zero_mul]

/-- [proved-derived; formal-checked] A pure gauge is flat (`CellHolonomy.pure_gauge_has_trivial_holonomy`). -/
theorem pure_gauge_is_flat (k0 k1 k2 : 𝕜ˣ) (φ : Fin 3 → 𝕜) :
    dA1 (regauge k0 k1 1) (regauge k1 k2 1) *ᵥ
      (dA0 (regauge k0 k1 1) (regauge k1 k2 1) (regauge k2 k0 1) *ᵥ φ) = 0 :=
  (exact_closed_iff_flat _ _ _).mpr (pure_gauge_has_trivial_holonomy k0 k1 k2) φ

/-- [counterexample; formal-checked] **Witness: nonzero holonomy.** With `g₀₁ = 2`, `g₁₂ = g₂₀ = 1`
the holonomy is `2`, the Kirchhoff structure is still Dirac, and the exact effort of `φ = δ₀` is
not closed: `d_A² φ = 1`. -/
theorem curved_witness :
    IsDirac (bondForm ℚ (Fin 3)) (kirchhoff (dA0 (Units.mk0 2 two_ne_zero) 1 1)) ∧
      (dA1 (Units.mk0 (2 : ℚ) two_ne_zero) 1 *ᵥ (dA0 (Units.mk0 2 two_ne_zero) 1 1 *ᵥ Pi.single 0 1)) 0
        = 1 := by
  refine ⟨connection_isDirac _ _ _, ?_⟩
  rw [dA_squared]
  simp [triangleHolonomy]
  norm_num

/-! ## The connection incidence on a general graph with cells as closed walks -/

section General

variable {ν ε : Type*} [Fintype ν] [Fintype ε] [DecidableEq ν]

/-- [definition] The covariant incidence of a graph with edge transports: `(d_A φ)_e =
g_e φ(t e) − φ(s e)`. -/
def connectionIncidence (src tgt : ε → ν) (g : ε → 𝕜ˣ) : Matrix ε ν 𝕜 :=
  Matrix.of fun e v => (if v = tgt e then (g e : 𝕜) else 0) - if v = src e then 1 else 0

omit [Fintype ε] in
theorem connectionIncidence_mulVec (src tgt : ε → ν) (g : ε → 𝕜ˣ) (φ : ν → 𝕜) (e : ε) :
    (connectionIncidence src tgt g *ᵥ φ) e = (g e : 𝕜) * φ (tgt e) - φ (src e) := by
  simp [connectionIncidence, mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib, ite_mul]

/-- [definition] A walk of edges from `a` to `b`. -/
def IsWalk (src tgt : ε → ν) : ν → ν → List ε → Prop
  | a, b, [] => a = b
  | a, b, e :: rest => src e = a ∧ IsWalk src tgt (tgt e) b rest

/-- [definition] The covariant reading of an edge cochain along a walk, transported to its start. -/
def walkRead (g : ε → 𝕜ˣ) (ω : ε → 𝕜) : List ε → 𝕜
  | [] => 0
  | e :: rest => ω e + (g e : 𝕜) * walkRead g ω rest

/-- [definition] The transport along a walk. -/
def walkTransport (g : ε → 𝕜ˣ) : List ε → 𝕜
  | [] => 1
  | e :: rest => (g e : 𝕜) * walkTransport g rest

omit [Fintype ε] in
/-- [proved-derived; formal-checked] **The covariant difference telescopes along a walk**:
`Σ_walk d_A φ = T_walk φ(b) − φ(a)`. -/
theorem walkRead_connection (src tgt : ε → ν) (g : ε → 𝕜ˣ) (φ : ν → 𝕜) :
    ∀ (walk : List ε) (a b : ν), IsWalk src tgt a b walk →
      walkRead g (connectionIncidence src tgt g *ᵥ φ) walk = walkTransport g walk * φ b - φ a
  | [], a, b, h => by
      simp only [IsWalk] at h; subst h; simp [walkRead, walkTransport]
  | e :: rest, a, b, h => by
      obtain ⟨hs, hrest⟩ := h
      rw [walkRead, walkRead_connection src tgt g φ rest (tgt e) b hrest,
        connectionIncidence_mulVec, hs, walkTransport]
      ring

omit [Fintype ε] in
/-- [proved-derived; formal-checked] **`d_A² = F_A` on every cell.** For a cell given as a closed
walk based at `a`, the covariant face reading of an exact effort is `(hol − 1) φ(a)`, with `hol`
the transport around the cell; exact efforts close on the cell iff `hol = 1` (or `φ(a) = 0`). -/
theorem cell_curvature (src tgt : ε → ν) (g : ε → 𝕜ˣ) (φ : ν → 𝕜) (cell : List ε) (a : ν)
    (hcell : IsWalk src tgt a a cell) :
    walkRead g (connectionIncidence src tgt g *ᵥ φ) cell = (walkTransport g cell - 1) * φ a := by
  rw [walkRead_connection src tgt g φ cell a a hcell]; ring

/-- [proved-derived; formal-checked] Power neutrality on a general graph, for every connection. -/
theorem connectionIncidence_isDirac [DecidableEq ε] (src tgt : ε → ν) (g : ε → 𝕜ˣ) :
    IsDirac (bondForm 𝕜 ε) (kirchhoff (connectionIncidence src tgt g)) :=
  kirchhoff_isDirac _

end General

/-! ## Block transports -/

section Block

variable {ν ε V : Type*} [AddCommGroup V] [Module 𝕜 V]

/-- [definition] **The block incidence**: each edge carries a linear transport `T_e : V → V` from
its target's value to its source's, `(d_A φ)_e = T_e φ(t e) − φ(s e)`. -/
def blockIncidence (src tgt : ε → ν) (T : ε → V →ₗ[𝕜] V) (φ : ν → V) : ε → V :=
  fun e => T e (φ (tgt e)) - φ (src e)

/-- [definition] The covariant reading of a block edge cochain along a walk, transported to its
start. -/
def blockWalkRead (T : ε → V →ₗ[𝕜] V) (ω : ε → V) : List ε → V
  | [] => 0
  | e :: rest => ω e + T e (blockWalkRead T ω rest)

/-- [definition] The block transport along a walk, `T_(e₁) ∘ ⋯ ∘ T_(e_k)`. -/
def blockWalkTransport (T : ε → V →ₗ[𝕜] V) : List ε → V →ₗ[𝕜] V
  | [] => LinearMap.id
  | e :: rest => (T e).comp (blockWalkTransport T rest)

/-- [proved-derived; formal-checked] **The block difference telescopes along a walk**:
`Σ_walk d_A φ = T_walk φ(b) − φ(a)`, with no inverse of any transport. -/
theorem blockWalkRead_incidence (src tgt : ε → ν) (T : ε → V →ₗ[𝕜] V) (φ : ν → V) :
    ∀ (walk : List ε) (a b : ν), IsWalk src tgt a b walk →
      blockWalkRead T (blockIncidence src tgt T φ) walk = blockWalkTransport T walk (φ b) - φ a
  | [], a, b, h => by
      simp only [IsWalk] at h; subst h; simp [blockWalkRead, blockWalkTransport]
  | e :: rest, a, b, h => by
      obtain ⟨hs, hrest⟩ := h
      rw [blockWalkRead, blockWalkRead_incidence src tgt T φ rest (tgt e) b hrest, blockIncidence,
        hs, blockWalkTransport, LinearMap.comp_apply, map_sub]
      abel

/-- [proved-derived; formal-checked] **`d_A² = F_A` on every cell, for block transports**: the
covariant face reading of an exact effort on a cell given as a closed walk at `a` is
`(hol − 1) φ(a)`. -/
theorem block_cell_curvature (src tgt : ε → ν) (T : ε → V →ₗ[𝕜] V) (φ : ν → V) (cell : List ε)
    (a : ν) (hcell : IsWalk src tgt a a cell) :
    blockWalkRead T (blockIncidence src tgt T φ) cell = blockWalkTransport T cell (φ a) - φ a :=
  blockWalkRead_incidence src tgt T φ cell a a hcell

/-- [proved-derived; formal-checked] **A flat block cell closes every exact effort**: when the
transport around the cell is the identity, the covariant face coboundary of `d_A φ` vanishes
(`∂² = 0`, covariantly), whatever the transports' ranks. -/
theorem block_flat_closed (src tgt : ε → ν) (T : ε → V →ₗ[𝕜] V) (φ : ν → V) (cell : List ε)
    (a : ν) (hcell : IsWalk src tgt a a cell) (hflat : blockWalkTransport T cell = LinearMap.id) :
    blockWalkRead T (blockIncidence src tgt T φ) cell = 0 := by
  rw [block_cell_curvature src tgt T φ cell a hcell, hflat, LinearMap.id_apply, sub_self]

/-- [proved-derived; formal-checked] **The scalar incidence is the unit-width block**: with `V = 𝕜`
and `T_e = g_e · 1`, the block incidence is `connectionIncidence`. -/
theorem blockIncidence_eq_connectionIncidence [Fintype ν] [DecidableEq ν] (src tgt : ε → ν)
    (g : ε → 𝕜ˣ) (φ : ν → 𝕜) :
    blockIncidence src tgt (fun e => (g e : 𝕜) • (LinearMap.id : 𝕜 →ₗ[𝕜] 𝕜)) φ =
      connectionIncidence src tgt g *ᵥ φ := by
  funext e
  rw [connectionIncidence_mulVec]
  simp [blockIncidence]

end Block

/-- [counterexample; formal-checked] **Witness on a two-edge loop.** Vertices `0, 1`, edges
`0 → 1` with transport `1` and `1 → 0` with transport `−1` (an orientation-reversing seam): the
holonomy is `−1` and the exact effort of `φ = δ₀` reads `−2` around the cell. -/
theorem seam_curvature_witness :
    walkRead (fun e : Fin 2 => if e = 0 then (1 : ℚˣ) else -1)
      (connectionIncidence (![0, 1] : Fin 2 → Fin 2) ![1, 0]
        (fun e : Fin 2 => if e = 0 then (1 : ℚˣ) else -1) *ᵥ Pi.single 0 1) [0, 1] = -2 := by
  have hw : IsWalk (![0, 1] : Fin 2 → Fin 2) ![1, 0] (0 : Fin 2) 0 [(0 : Fin 2), 1] :=
    ⟨rfl, rfl, rfl⟩
  rw [cell_curvature _ _ _ _ [0, 1] 0 hw]
  simp [walkTransport]
  norm_num

end Holonics.HolonCore
