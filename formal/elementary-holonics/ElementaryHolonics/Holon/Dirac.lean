import ElementaryHolonics.Holon.Port
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# Holon.Dirac: interconnection structures, their constructors and their composition

[definition] The interconnection facet `𝒟`. A **Dirac structure** is a subspace equal to its own
orthogonal for the bond pairing (`IsDirac`).

[proved-derived; formal-checked] What is proved, over a field `𝕜`.

1. **Power neutrality** `⟨e, f⟩ = 0` on every Dirac structure (`IsDirac.power_eq_zero`, char 0).
2. **Three constructors.** The graph of a skew map `f = J e` (`skewGraph_isDirac`); the
   Kirchhoff–Stokes–Dirac structure of any incidence `d` — KCL `dᵀ f = 0`, KVL `e = d φ`
   (`kirchhoff_isDirac`), whose isotropy is Tellegen = `ExteriorBoundary.stokes_pairing`
   (`tellegen`); and the **kernel form** `{(f,e) | F f + E e = 0}`, Dirac when `F Eᵀ + E Fᵀ = 0` and
   `rank [F | E] = n` (`kernelForm_isDirac`, via `orthogonal_kernelForm`: its orthogonal is the
   image form `{(Eᵀλ, Fᵀλ)}`). The skew graph is the kernel form `(1, −J)`
   (`skewGraph_eq_kernelForm`, hypotheses in `skewGraph_kernel_hypotheses`) and the Kirchhoff
   structure is the kernel form `([dᵀ;0], [0;Cᵀ])` for a cycle matrix `C` spanning `ker dᵀ`
   (`kirchhoff_eq_kernelForm`; witness `triangle_kernelForm`). A cycle matrix always exists (a
   basis of `ker dᵀ`, `exists_cycleMatrix`), so every Kirchhoff structure is a kernel form with no
   hypothesis (`kirchhoff_is_kernelForm`).
3. **Composition.** Composing a Dirac structure on `P × Q` with a Dirac link on `Q` is Dirac
   (`compose_isDirac`, through `(A ⊓ C)^⊥ = A^⊥ ⊔ C^⊥`, `orthogonal_inf`) — Cervera,
   van der Schaft and Baños, *Automatica* 43 (2007), in finite dimension. Interconnecting two
   Dirac structures at shared ports (flows opposite, efforts equal: `link`) is Dirac
   (`interconnect_isDirac`, membership `mem_interconnect`), with exact power balance: the shared
   terms cancel (`interconnect_power`). Relabelling ports preserves Dirac structures
   (`IsDirac.reindex`).

Witnesses: a gyrator bond with nonzero flow and zero power; the identity graph and the zero
subspace are not Dirac; a loop current against a potential on the triangle; two gyrators
interconnected form a transformer (`gyrator_chain_witness`).
-/

noncomputable section

namespace Soma.Holonics.HolonCore

open Matrix LinearMap

/-! ## 1. Dirac structures of a symmetric pairing -/

section Abstract

variable {𝕜 : Type*} [Field 𝕜] {M : Type*} [AddCommGroup M] [Module 𝕜 M]

/-- [definition] A **Dirac structure** of a pairing `B`: a subspace equal to its own orthogonal. -/
def IsDirac (B : LinearMap.BilinForm 𝕜 M) (D : Submodule 𝕜 M) : Prop := B.orthogonal D = D

theorem IsDirac.pairing_eq_zero {B : LinearMap.BilinForm 𝕜 M} {D : Submodule 𝕜 M}
    (hD : IsDirac B D) {x y : M} (hx : x ∈ D) (hy : y ∈ D) : B x y = 0 := by
  have hy' : y ∈ B.orthogonal D := by rw [hD]; exact hy
  exact hy' x hx

/-- [proved-derived; formal-checked] To prove `D` Dirac it suffices: isotropic (`D ⊆ D^⊥`) and
co-isotropic (`D^⊥ ⊆ D`). -/
theorem isDirac_of (B : LinearMap.BilinForm 𝕜 M) (D : Submodule 𝕜 M)
    (iso : ∀ x ∈ D, ∀ y ∈ D, B x y = 0) (coiso : ∀ y, (∀ x ∈ D, B x y = 0) → y ∈ D) :
    IsDirac B D :=
  le_antisymm (fun y hy => coiso y hy) (fun y hy x hx => iso x hx y hy)

end Abstract

section Bonds0

variable {𝕜 : Type*} [Field 𝕜] {ι : Type*} [Fintype ι]

/-- [proved-derived; formal-checked] **Power neutrality.** Every bond of a Dirac structure carries
zero power: `⟨e, f⟩ = 0` on `D` (Tellegen). -/
theorem IsDirac.power_eq_zero [CharZero 𝕜] {D : Submodule 𝕜 (Bond 𝕜 ι)}
    (hD : IsDirac (bondForm 𝕜 ι) D) {b : Bond 𝕜 ι} (hb : b ∈ D) : power b = 0 := by
  have h := hD.pairing_eq_zero hb hb
  rw [bondForm_self] at h
  exact (mul_eq_zero.mp h).resolve_left two_ne_zero
/-! ## 3. The graph of a skew map -/

/-- [definition] The graph `{(J e, e)}` of an effort-to-flow map `J`. -/
def skewGraph (J : Matrix ι ι 𝕜) : Submodule 𝕜 (Bond 𝕜 ι) where
  carrier := {b | b.1 = J *ᵥ b.2}
  add_mem' {a b} ha hb := by simp only [Set.mem_ofPred_eq] at *; simp [ha, hb, mulVec_add]
  zero_mem' := by simp
  smul_mem' c b hb := by simp only [Set.mem_ofPred_eq] at *; simp [hb, mulVec_smul]

theorem skew_dot {J : Matrix ι ι 𝕜} (hJ : Jᵀ = -J) (x y : ι → 𝕜) :
    x ⬝ᵥ (J *ᵥ y) = -(y ⬝ᵥ (J *ᵥ x)) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hJ, neg_mulVec, neg_dotProduct, dotProduct_comm]

/-- [proved-derived; formal-checked] **The graph of a skew map is a Dirac structure.** -/
theorem skewGraph_isDirac [DecidableEq ι] {J : Matrix ι ι 𝕜} (hJ : Jᵀ = -J) :
    IsDirac (bondForm 𝕜 ι) (skewGraph J) := by
  apply isDirac_of
  · intro x hx y hy
    simp only [skewGraph, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
      Set.mem_ofPred_eq] at hx hy
    rw [bondForm_apply, hx, hy, skew_dot hJ]
    ring
  · intro y hy
    show y.1 = J *ᵥ y.2
    ext i
    have h := hy (J *ᵥ Pi.single i 1, Pi.single i 1) rfl
    rw [bondForm_apply, skew_dot hJ] at h
    simp only [single_dotProduct, one_mul] at h
    linear_combination h

end Bonds0

/-! ## 4. The Kirchhoff (Stokes–Dirac) structure of an incidence -/

section Kirchhoff

variable {𝕜 : Type*} [Field 𝕜] {ι : Type*} [Fintype ι] {ν : Type*} [Fintype ν]

/-- [definition] **The Kirchhoff–Stokes–Dirac structure** of an incidence `d : edges × nodes`
(the coboundary `d₀`): edge flows satisfy KCL `dᵀ f = 0` and edge efforts are exact, `e = d φ`
(KVL). -/
def kirchhoff (d : Matrix ι ν 𝕜) : Submodule 𝕜 (Bond 𝕜 ι) where
  carrier := {b | dᵀ *ᵥ b.1 = 0 ∧ ∃ φ, d *ᵥ φ = b.2}
  add_mem' {a b} ha hb := by
    obtain ⟨ha1, φ, hφ⟩ := ha
    obtain ⟨hb1, ψ, hψ⟩ := hb
    exact ⟨by simp [mulVec_add, ha1, hb1], φ + ψ, by simp [mulVec_add, hφ, hψ]⟩
  zero_mem' := ⟨by simp, 0, by simp⟩
  smul_mem' c b hb := by
    obtain ⟨hb1, φ, hφ⟩ := hb
    exact ⟨by simp [mulVec_smul, hb1], c • φ, by simp [mulVec_smul, hφ]⟩

/-- [proved-derived; formal-checked] **Tellegen is Stokes.** `⟨dφ, f⟩ = ⟨φ, dᵀ f⟩`: the effort of
an exact potential paired with a flow is the potential paired with the flow's boundary,
`ExteriorBoundary.stokes_pairing` for the boundary `f ↦ dᵀ f` and the form `⟨φ, ·⟩`. -/
theorem tellegen (d : Matrix ι ν 𝕜) (φ : ν → 𝕜) (f : ι → 𝕜) :
    (d *ᵥ φ) ⬝ᵥ f = (Matrix.mulVecLin dᵀ).dualMap (dotProductBilin 𝕜 𝕜 φ) f := by
  rw [Soma.Holonics.Geometry.ExteriorBoundary.stokes_pairing]
  simp only [Matrix.mulVecLin_apply, dotProductBilin]
  change (d *ᵥ φ) ⬝ᵥ f = φ ⬝ᵥ (dᵀ *ᵥ f)
  rw [dotProduct_mulVec, vecMul_transpose, dotProduct_comm]

/-- [proved-derived; formal-checked] **The Kirchhoff structure is Dirac**, for every incidence:
isotropy is Tellegen; co-isotropy is KCL from exact probes and KVL from the Fredholm alternative
against KCL probes. -/
theorem kirchhoff_isDirac [DecidableEq ι] [DecidableEq ν] (d : Matrix ι ν 𝕜) :
    IsDirac (bondForm 𝕜 ι) (kirchhoff d) := by
  apply isDirac_of
  · rintro x ⟨hx1, φ, hφ⟩ y ⟨hy1, ψ, hψ⟩
    rw [bondForm_apply, ← hφ, ← hψ]
    have h1 : (d *ᵥ φ) ⬝ᵥ y.1 = φ ⬝ᵥ (dᵀ *ᵥ y.1) := by
      rw [dotProduct_mulVec, vecMul_transpose, dotProduct_comm]
    have h2 : (d *ᵥ ψ) ⬝ᵥ x.1 = ψ ⬝ᵥ (dᵀ *ᵥ x.1) := by
      rw [dotProduct_mulVec, vecMul_transpose, dotProduct_comm]
    rw [h1, h2, hx1, hy1]; simp
  · intro y hy
    have hkcl : dᵀ *ᵥ y.1 = 0 := by
      funext j
      have h := hy (0, d *ᵥ Pi.single j 1) ⟨by simp, Pi.single j 1, rfl⟩
      rw [bondForm_apply] at h
      rw [dotProduct_zero, add_zero, dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose,
        dotProduct_single, mul_one] at h
      exact h
    refine ⟨hkcl, (mem_range_iff_annihilators_vanish d y.2).mpr ?_⟩
    intro w hw
    have h := hy (w, 0) ⟨hw, 0, by simp⟩
    rw [bondForm_apply] at h
    simpa [dotProduct_comm] using h

end Kirchhoff
/-! ## 5. Witnesses -/

set_option linter.unnecessarySeqFocus false

/-- [definition] The quarter-turn gyrator `J = [[0, −1], [1, 0]]`. -/
def gyrator : Matrix (Fin 2) (Fin 2) ℚ := !![0, -1; 1, 0]

theorem gyrator_skew : gyratorᵀ = -gyrator := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [gyrator]

/-- [proved-derived; formal-checked] **Witness: a gyrator bond moves and carries no power.** The
effort `(1, 1)` drives the flow `(−1, 1)` on the gyrator's Dirac structure, with power `0`. -/
theorem gyrator_witness :
    ((![-1, 1], ![1, 1]) : Bond ℚ (Fin 2)) ∈ skewGraph gyrator ∧
      power ((![-1, 1], ![1, 1]) : Bond ℚ (Fin 2)) = 0 ∧
      (![-1, 1] : Fin 2 → ℚ) ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩
  · show ![-1, 1] = gyrator *ᵥ ![1, 1]
    ext i; fin_cases i <;> simp [gyrator, mulVec, dotProduct, Fin.sum_univ_two]
  · simp [power, dotProduct, Fin.sum_univ_two]
  · intro h; have := congrFun h 0; simp at this

/-- [counterexample; formal-checked] **A non-skew graph is not Dirac**: the identity graph
`{(e, e)}` carries power `e·e`, which is `1` at `e = (1, 0)`. -/
theorem identity_graph_not_dirac :
    ¬ IsDirac (bondForm ℚ (Fin 2)) (skewGraph (1 : Matrix (Fin 2) (Fin 2) ℚ)) := by
  intro h
  have hb : ((![1, 0], ![1, 0]) : Bond ℚ (Fin 2)) ∈ skewGraph (1 : Matrix (Fin 2) (Fin 2) ℚ) := by
    show ![1, 0] = (1 : Matrix (Fin 2) (Fin 2) ℚ) *ᵥ ![1, 0]
    simp
  have := h.power_eq_zero hb
  simp [power, dotProduct, Fin.sum_univ_two] at this

/-- [counterexample; formal-checked] **Isotropy is not enough**: the zero subspace is isotropic
and its orthogonal is everything. -/
theorem zero_not_dirac : ¬ IsDirac (bondForm ℚ (Fin 2)) ⊥ := by
  intro h
  have hmem : ((![1, 0], 0) : Bond ℚ (Fin 2)) ∈ (bondForm ℚ (Fin 2)).orthogonal ⊥ := by
    intro x hx; rw [Submodule.mem_bot] at hx; subst hx; simp
  rw [h, Submodule.mem_bot] at hmem
  have := congrArg (fun b : Bond ℚ (Fin 2) => b.1 0) hmem
  simp at this

/-- [definition] The oriented triangle: edges `0→1`, `1→2`, `2→0`, as `edges × nodes`. -/
def triangle : Matrix (Fin 3) (Fin 3) ℚ := !![-1, 1, 0; 0, -1, 1; 1, 0, -1]

/-- [proved-derived; formal-checked] **Witness: a loop current against a potential.** The unit
circulation `(1,1,1)` satisfies KCL, the drops of `φ = (0, 1, 3)` are `(1, 2, −3)`, the bond lies in
the Kirchhoff structure and its power `1 + 2 − 3` is `0`. -/
theorem triangle_witness :
    ((![1, 1, 1], ![1, 2, -3]) : Bond ℚ (Fin 3)) ∈ kirchhoff triangle ∧
      power ((![1, 1, 1], ![1, 2, -3]) : Bond ℚ (Fin 3)) = 0 := by
  refine ⟨⟨?_, ![0, 1, 3], ?_⟩, ?_⟩
  · ext i; fin_cases i <;> simp [triangle, mulVec, dotProduct, Fin.sum_univ_three]
  · ext i; fin_cases i <;> simp [triangle, mulVec, dotProduct, Fin.sum_univ_three] <;> norm_num
  · simp [power, dotProduct, Fin.sum_univ_three]; norm_num


/-! ## 6. Composition of a Dirac structure with a Dirac link -/

section Compose

variable {𝕜 : Type*} [Field 𝕜]
variable {P Q : Type*} [AddCommGroup P] [Module 𝕜 P] [AddCommGroup Q] [Module 𝕜 Q]

/-- [definition] The orthogonal sum of two pairings on `P × Q`. -/
def prodForm (Bp : LinearMap.BilinForm 𝕜 P) (Bq : LinearMap.BilinForm 𝕜 Q) :
    LinearMap.BilinForm 𝕜 (P × Q) :=
  Bp.comp (LinearMap.fst 𝕜 P Q) (LinearMap.fst 𝕜 P Q) +
    Bq.comp (LinearMap.snd 𝕜 P Q) (LinearMap.snd 𝕜 P Q)

@[simp] theorem prodForm_apply (Bp : LinearMap.BilinForm 𝕜 P) (Bq : LinearMap.BilinForm 𝕜 Q)
    (x y : P × Q) : prodForm Bp Bq x y = Bp x.1 y.1 + Bq x.2 y.2 := rfl

/-- [definition] **Composition through a link**: `{p | ∃ q ∈ L, (p, q) ∈ D}`. -/
def compose (D : Submodule 𝕜 (P × Q)) (L : Submodule 𝕜 Q) : Submodule 𝕜 P :=
  (D ⊓ L.comap (LinearMap.snd 𝕜 P Q)).map (LinearMap.fst 𝕜 P Q)

theorem mem_compose {D : Submodule 𝕜 (P × Q)} {L : Submodule 𝕜 Q} {p : P} :
    p ∈ compose D L ↔ ∃ q ∈ L, (p, q) ∈ D := by
  constructor
  · rintro ⟨⟨p', q⟩, ⟨hD, hL⟩, rfl⟩; exact ⟨q, hL, hD⟩
  · rintro ⟨q, hL, hD⟩; exact ⟨(p, q), ⟨hD, hL⟩, rfl⟩

theorem prodForm_isRefl {Bp : LinearMap.BilinForm 𝕜 P} {Bq : LinearMap.BilinForm 𝕜 Q}
    (hp : ∀ x y, Bp x y = Bp y x) (hq : ∀ x y, Bq x y = Bq y x) :
    (prodForm Bp Bq).IsRefl := fun x y h => by
  rw [prodForm_apply] at *; rw [hp, hq]; exact h

theorem prodForm_nondegenerate {Bp : LinearMap.BilinForm 𝕜 P} {Bq : LinearMap.BilinForm 𝕜 Q}
    (hp : ∀ x y, Bp x y = Bp y x) (hq : ∀ x y, Bq x y = Bq y x)
    (np : ∀ x, (∀ y, Bp x y = 0) → x = 0) (nq : ∀ x, (∀ y, Bq x y = 0) → x = 0) :
    (prodForm Bp Bq).Nondegenerate := by
  have sep : ∀ x : P × Q, (∀ y, prodForm Bp Bq x y = 0) → x = 0 := by
    intro x h
    ext
    · exact congrArg Prod.fst (show (x.1, (0 : Q)) = (0, 0) from by
        rw [np x.1 fun y => by simpa using h (y, 0)]) ▸ rfl
    · exact congrArg Prod.snd (show ((0 : P), x.2) = (0, 0) from by
        rw [nq x.2 fun y => by simpa using h (0, y)]) ▸ rfl
  exact ⟨sep, fun x h => sep x fun y => by rw [prodForm_apply, hp, hq]; simpa using h y⟩

variable [FiniteDimensional 𝕜 P] [FiniteDimensional 𝕜 Q]

/-- [proved-derived; formal-checked] In finite dimension, for a nondegenerate reflexive pairing,
`(A ⊓ C)^⊥ = A^⊥ ⊔ C^⊥`. -/
theorem orthogonal_inf {V : Type*} [AddCommGroup V] [Module 𝕜 V] [FiniteDimensional 𝕜 V]
    {B : LinearMap.BilinForm 𝕜 V} (hB : B.Nondegenerate) (hR : B.IsRefl) (A C : Submodule 𝕜 V) :
    B.orthogonal (A ⊓ C) = B.orthogonal A ⊔ B.orthogonal C := by
  have hsup : B.orthogonal (B.orthogonal A ⊔ B.orthogonal C) = A ⊓ C := by
    ext v
    constructor
    · intro hv
      rw [← LinearMap.BilinForm.orthogonal_orthogonal hB hR A,
        ← LinearMap.BilinForm.orthogonal_orthogonal hB hR C]
      exact ⟨fun n hn => hv n (Submodule.mem_sup_left hn),
        fun n hn => hv n (Submodule.mem_sup_right hn)⟩
    · rintro ⟨hA, hC⟩ n hn
      obtain ⟨a, ha, c, hc, rfl⟩ := Submodule.mem_sup.mp hn
      rw [map_add, LinearMap.add_apply, hR v a (ha v hA), hR v c (hc v hC), add_zero]
  rw [← hsup, LinearMap.BilinForm.orthogonal_orthogonal hB hR]

/-- [proved-derived; formal-checked] **Composing a Dirac structure with a Dirac link is Dirac**
(finite dimension; Cervera, van der Schaft and Baños, *Automatica* 43 (2007), standard). -/
theorem compose_isDirac {Bp : LinearMap.BilinForm 𝕜 P} {Bq : LinearMap.BilinForm 𝕜 Q}
    (hp : ∀ x y, Bp x y = Bp y x) (hq : ∀ x y, Bq x y = Bq y x)
    (np : ∀ x, (∀ y, Bp x y = 0) → x = 0) (nq : ∀ x, (∀ y, Bq x y = 0) → x = 0)
    {D : Submodule 𝕜 (P × Q)} {L : Submodule 𝕜 Q}
    (hD : IsDirac (prodForm Bp Bq) D) (hL : IsDirac Bq L) :
    IsDirac Bp (compose D L) := by
  apply isDirac_of
  · intro x hx y hy
    obtain ⟨qx, hqx, hDx⟩ := mem_compose.mp hx
    obtain ⟨qy, hqy, hDy⟩ := mem_compose.mp hy
    have h1 := hD.pairing_eq_zero hDx hDy
    have h2 := hL.pairing_eq_zero hqx hqy
    rw [prodForm_apply] at h1
    simp only at h1
    rw [h2, add_zero] at h1
    exact h1
  · intro p hp'
    -- `(p, 0)` is orthogonal to `D ⊓ comap snd L`
    have hperp : (p, (0 : Q)) ∈ (prodForm Bp Bq).orthogonal (D ⊓ L.comap (LinearMap.snd 𝕜 P Q)) := by
      rintro ⟨p', q'⟩ ⟨hD', hL'⟩
      rw [prodForm_apply]
      simp only [map_zero, add_zero]
      exact hp' p' (mem_compose.mpr ⟨q', hL', hD'⟩)
    rw [orthogonal_inf (prodForm_nondegenerate hp hq np nq) (prodForm_isRefl hp hq), hD] at hperp
    obtain ⟨d, hd, z, hz, hdz⟩ := Submodule.mem_sup.mp hperp
    -- `z ⊥ comap snd L` forces `z = (0, l)` with `l ∈ L`
    have hz1 : z.1 = 0 := np z.1 fun y => by
      have := hz (y, 0) (by simp)
      rw [prodForm_apply] at this
      simpa [hp] using this
    have hz2 : z.2 ∈ L := by
      rw [← hL]
      intro n hn
      have := hz (0, n) (by simpa using hn)
      rw [prodForm_apply] at this
      simpa using this
    refine mem_compose.mpr ⟨-z.2, L.neg_mem hz2, ?_⟩
    have hd' : d = (p, -z.2) := by
      have := hdz
      ext
      · have h := congrArg Prod.fst this; simp [hz1] at h; exact h
      · have h := congrArg Prod.snd this; simp at h; exact eq_neg_of_add_eq_zero_left h
    rw [← hd']; exact hd

end Compose

/-! ## 7. Interconnecting two Dirac structures at a shared port set -/

section Bonds

variable {𝕜 : Type*} [Field 𝕜]
variable {α τ β : Type*} [Fintype α] [Fintype τ] [Fintype β]

/-- [definition] The `A`-side bond: the `α` ports of `p` with the shared bond `q`. -/
def partA (p : Bond 𝕜 (α ⊕ β)) (q : Bond 𝕜 τ) : Bond 𝕜 (α ⊕ τ) :=
  (Sum.elim (p.1 ∘ Sum.inl) q.1, Sum.elim (p.2 ∘ Sum.inl) q.2)

/-- [definition] The `B`-side bond: the shared bond `q` with the `β` ports of `p`. -/
def partB (p : Bond 𝕜 (α ⊕ β)) (q : Bond 𝕜 τ) : Bond 𝕜 (τ ⊕ β) :=
  (Sum.elim q.1 (p.1 ∘ Sum.inr), Sum.elim q.2 (p.2 ∘ Sum.inr))

/-- [definition] `partA` as a linear map on `P × (Q × Q)`. -/
def partALin : (Bond 𝕜 (α ⊕ β) × (Bond 𝕜 τ × Bond 𝕜 τ)) →ₗ[𝕜] Bond 𝕜 (α ⊕ τ) where
  toFun x := partA x.1 x.2.1
  map_add' x y := by ext i <;> cases i <;> rfl
  map_smul' c x := by ext i <;> cases i <;> rfl

/-- [definition] `partB` as a linear map on `P × (Q × Q)`. -/
def partBLin : (Bond 𝕜 (α ⊕ β) × (Bond 𝕜 τ × Bond 𝕜 τ)) →ₗ[𝕜] Bond 𝕜 (τ ⊕ β) where
  toFun x := partB x.1 x.2.2
  map_add' x y := by ext i <;> cases i <;> rfl
  map_smul' c x := by ext i <;> cases i <;> rfl

/-- [proved-derived; formal-checked] **The pairing splits across the cut.** -/
theorem split_form (p p' : Bond 𝕜 (α ⊕ β)) (q₁ q₁' q₂ q₂' : Bond 𝕜 τ) :
    bondForm 𝕜 (α ⊕ β) p p' + (bondForm 𝕜 τ q₁ q₁' + bondForm 𝕜 τ q₂ q₂') =
      bondForm 𝕜 (α ⊕ τ) (partA p q₁) (partA p' q₁') +
        bondForm 𝕜 (τ ⊕ β) (partB p q₂) (partB p' q₂') := by
  simp only [bondForm_apply, partA, partB, dotProduct, Fintype.sum_sum_type, Sum.elim_inl,
    Sum.elim_inr, Function.comp_apply]
  ring

/-- [proved-derived; formal-checked] The power splits the same way. -/
theorem split_power (p : Bond 𝕜 (α ⊕ β)) (q₁ q₂ : Bond 𝕜 τ) :
    power p + (power q₁ + power q₂) = power (partA p q₁) + power (partB p q₂) := by
  simp only [power, partA, partB, dotProduct, Fintype.sum_sum_type, Sum.elim_inl,
    Sum.elim_inr, Function.comp_apply]
  ring

/-- [definition] The two structures side by side, indexed by the cut. -/
def pairedD (DA : Submodule 𝕜 (Bond 𝕜 (α ⊕ τ))) (DB : Submodule 𝕜 (Bond 𝕜 (τ ⊕ β))) :
    Submodule 𝕜 (Bond 𝕜 (α ⊕ β) × (Bond 𝕜 τ × Bond 𝕜 τ)) :=
  DA.comap partALin ⊓ DB.comap partBLin

/-- [definition] **The shared-port link**: flows opposite, efforts equal. -/
def link (𝕜 τ : Type*) [Field 𝕜] [Fintype τ] : Submodule 𝕜 (Bond 𝕜 τ × Bond 𝕜 τ) where
  carrier := {x | x.2.1 = -x.1.1 ∧ x.2.2 = x.1.2}
  add_mem' ha hb := ⟨by simp [ha.1, hb.1, add_comm], by simp [ha.2, hb.2]⟩
  zero_mem' := ⟨by simp, by simp⟩
  smul_mem' c x hx := ⟨by simp [hx.1], by simp [hx.2]⟩

variable [DecidableEq α] [DecidableEq τ] [DecidableEq β]

/-- [proved-derived; formal-checked] The link is a Dirac structure. -/
theorem link_isDirac : IsDirac (prodForm (bondForm 𝕜 τ) (bondForm 𝕜 τ)) (link 𝕜 τ) := by
  apply isDirac_of
  · rintro x ⟨hx1, hx2⟩ y ⟨hy1, hy2⟩
    rw [prodForm_apply, bondForm_apply, bondForm_apply, hx1, hx2, hy1, hy2]
    simp [dotProduct_neg]; ring
  · intro y hy
    have h1 : ∀ i, y.2.1 i + y.1.1 i = 0 := by
      intro i
      have := hy ((0, Pi.single i 1), (0, Pi.single i 1)) ⟨by simp, rfl⟩
      simpa [prodForm_apply, bondForm_apply, add_comm] using this
    have h2 : ∀ i, y.1.2 i - y.2.2 i = 0 := by
      intro i
      have := hy ((Pi.single i 1, 0), (-Pi.single i 1, 0)) ⟨rfl, by simp⟩
      simp [prodForm_apply, bondForm_apply] at this
      linear_combination this
    exact ⟨funext fun i => eq_neg_of_add_eq_zero_left (h1 i),
      funext fun i => (sub_eq_zero.mp (h2 i)).symm⟩

theorem bondForm_symm' (ι : Type*) [Fintype ι] :
    ∀ x y : Bond 𝕜 ι, bondForm 𝕜 ι x y = bondForm 𝕜 ι y x := bondForm_symm

omit [DecidableEq α] [DecidableEq τ] [DecidableEq β] in
/-- [proved-derived; formal-checked] Two Dirac structures side by side form a Dirac structure of
the cut pairing. -/
theorem pairedD_isDirac {DA : Submodule 𝕜 (Bond 𝕜 (α ⊕ τ))} {DB : Submodule 𝕜 (Bond 𝕜 (τ ⊕ β))}
    (hA : IsDirac (bondForm 𝕜 (α ⊕ τ)) DA) (hB : IsDirac (bondForm 𝕜 (τ ⊕ β)) DB) :
    IsDirac (prodForm (bondForm 𝕜 (α ⊕ β)) (prodForm (bondForm 𝕜 τ) (bondForm 𝕜 τ)))
      (pairedD DA DB) := by
  apply isDirac_of
  · rintro x ⟨hxA, hxB⟩ y ⟨hyA, hyB⟩
    rw [prodForm_apply, prodForm_apply, split_form]
    have h1 : bondForm 𝕜 (α ⊕ τ) (partA x.1 x.2.1) (partA y.1 y.2.1) = 0 :=
      hA.pairing_eq_zero hxA hyA
    have h2 : bondForm 𝕜 (τ ⊕ β) (partB x.1 x.2.2) (partB y.1 y.2.2) = 0 :=
      hB.pairing_eq_zero hxB hyB
    rw [h1, h2, add_zero]
  · intro y hy
    constructor
    · show partA y.1 y.2.1 ∈ DA
      rw [← hA]
      intro xA hxA
      let x : Bond 𝕜 (α ⊕ β) × (Bond 𝕜 τ × Bond 𝕜 τ) :=
        ((Sum.elim (xA.1 ∘ Sum.inl) 0, Sum.elim (xA.2 ∘ Sum.inl) 0),
          ((xA.1 ∘ Sum.inr, xA.2 ∘ Sum.inr), 0))
      have hxa : partA x.1 x.2.1 = xA := by
        ext i <;> cases i <;> rfl
      have hxb : partB x.1 x.2.2 = 0 := by
        ext i <;> cases i <;> rfl
      have h := hy x ⟨by show partA x.1 x.2.1 ∈ DA; rw [hxa]; exact hxA,
        by show partB x.1 x.2.2 ∈ DB; rw [hxb]; exact DB.zero_mem⟩
      rw [prodForm_apply, prodForm_apply, split_form, hxa, hxb] at h
      simpa using h
    · show partB y.1 y.2.2 ∈ DB
      rw [← hB]
      intro xB hxB
      let x : Bond 𝕜 (α ⊕ β) × (Bond 𝕜 τ × Bond 𝕜 τ) :=
        ((Sum.elim 0 (xB.1 ∘ Sum.inr), Sum.elim 0 (xB.2 ∘ Sum.inr)),
          (0, (xB.1 ∘ Sum.inl, xB.2 ∘ Sum.inl)))
      have hxa : partA x.1 x.2.1 = 0 := by
        ext i <;> cases i <;> rfl
      have hxb : partB x.1 x.2.2 = xB := by
        ext i <;> cases i <;> rfl
      have h := hy x ⟨by show partA x.1 x.2.1 ∈ DA; rw [hxa]; exact DA.zero_mem,
        by show partB x.1 x.2.2 ∈ DB; rw [hxb]; exact hxB⟩
      rw [prodForm_apply, prodForm_apply, split_form, hxa, hxb] at h
      simpa using h

/-- [definition] **Interconnection** of `DA` (ports `α ⊕ τ`) and `DB` (ports `τ ⊕ β`) at the
shared ports `τ`: flows opposite, efforts equal, shared bond eliminated. -/
def interconnect (DA : Submodule 𝕜 (Bond 𝕜 (α ⊕ τ))) (DB : Submodule 𝕜 (Bond 𝕜 (τ ⊕ β))) :
    Submodule 𝕜 (Bond 𝕜 (α ⊕ β)) :=
  compose (pairedD DA DB) (link 𝕜 τ)

omit [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq τ] [DecidableEq β] in
theorem mem_interconnect {DA : Submodule 𝕜 (Bond 𝕜 (α ⊕ τ))}
    {DB : Submodule 𝕜 (Bond 𝕜 (τ ⊕ β))} {b : Bond 𝕜 (α ⊕ β)} :
    b ∈ interconnect DA DB ↔ ∃ q : Bond 𝕜 τ, partA b q ∈ DA ∧ partB b (-q.1, q.2) ∈ DB := by
  rw [interconnect, mem_compose]
  constructor
  · rintro ⟨⟨q₁, q₂⟩, ⟨h1, h2⟩, hA, hB⟩
    refine ⟨q₁, hA, ?_⟩
    have : q₂ = (-q₁.1, q₁.2) := Prod.ext h1 h2
    rw [← this]; exact hB
  · rintro ⟨q, hA, hB⟩
    exact ⟨(q, (-q.1, q.2)), ⟨rfl, rfl⟩, hA, hB⟩

/-- [proved-derived; formal-checked] **The interconnection of two Dirac structures is Dirac.** -/
theorem interconnect_isDirac {DA : Submodule 𝕜 (Bond 𝕜 (α ⊕ τ))}
    {DB : Submodule 𝕜 (Bond 𝕜 (τ ⊕ β))}
    (hA : IsDirac (bondForm 𝕜 (α ⊕ τ)) DA) (hB : IsDirac (bondForm 𝕜 (τ ⊕ β)) DB) :
    IsDirac (bondForm 𝕜 (α ⊕ β)) (interconnect DA DB) :=
  compose_isDirac bondForm_symm
    (fun x y => by rw [prodForm_apply, prodForm_apply, bondForm_symm x.1, bondForm_symm x.2])
    bondForm_separating
    (fun x h => by
      have h1 := bondForm_separating x.1 fun y => by simpa using h (y, 0)
      have h2 := bondForm_separating x.2 fun y => by simpa using h (0, y)
      exact Prod.ext h1 h2)
    (pairedD_isDirac hA hB) link_isDirac

omit [DecidableEq α] [DecidableEq τ] [DecidableEq β] in
/-- [proved-derived; formal-checked] **Power balance of the composite.** For any shared bond, the
two sides' powers sum to the composite's external power: the shared terms cancel exactly
(`e_τ·f_τ + e_τ·(−f_τ) = 0`). -/
theorem interconnect_power (b : Bond 𝕜 (α ⊕ β)) (q : Bond 𝕜 τ) :
    power (partA b q) + power (partB b (-q.1, q.2)) = power b := by
  rw [← split_power b q (-q.1, q.2)]
  simp [power, dotProduct_neg]

end Bonds

/-! ## 8. The kernel form, and every constructor is one -/

section KernelForm

variable {𝕜 : Type*} [Field 𝕜] {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- [definition] The kernel map `(f, e) ↦ F f + E e`. -/
def kernelMap (F E : Matrix κ ι 𝕜) : Bond 𝕜 ι →ₗ[𝕜] (κ → 𝕜) :=
  (Matrix.mulVecLin F).comp (LinearMap.fst 𝕜 _ _) + (Matrix.mulVecLin E).comp (LinearMap.snd 𝕜 _ _)

omit [Fintype κ] in
@[simp] theorem kernelMap_apply (F E : Matrix κ ι 𝕜) (b : Bond 𝕜 ι) :
    kernelMap F E b = F *ᵥ b.1 + E *ᵥ b.2 := rfl

/-- [definition] The image map `λ ↦ (Eᵀ λ, Fᵀ λ)`. -/
def imageMap (F E : Matrix κ ι 𝕜) : (κ → 𝕜) →ₗ[𝕜] Bond 𝕜 ι :=
  (Matrix.mulVecLin Eᵀ).prod (Matrix.mulVecLin Fᵀ)

omit [Fintype ι] in
@[simp] theorem imageMap_apply (F E : Matrix κ ι 𝕜) (l : κ → 𝕜) :
    imageMap F E l = (Eᵀ *ᵥ l, Fᵀ *ᵥ l) := rfl

/-- [definition] **The kernel form** `{(f, e) | F f + E e = 0}`. -/
def kernelForm (F E : Matrix κ ι 𝕜) : Submodule 𝕜 (Bond 𝕜 ι) := LinearMap.ker (kernelMap F E)

theorem transpose_dot (A : Matrix κ ι 𝕜) (l : κ → 𝕜) (v : ι → 𝕜) :
    v ⬝ᵥ (Aᵀ *ᵥ l) = l ⬝ᵥ (A *ᵥ v) := by
  rw [dotProduct_mulVec, vecMul_transpose, dotProduct_comm]

/-- [proved-derived; formal-checked] The image map is the pairing-adjoint of the kernel map:
`⟨⟨b, (Eᵀλ, Fᵀλ)⟩⟩ = ⟨λ, F f + E e⟩`. -/
theorem bondForm_imageMap (F E : Matrix κ ι 𝕜) (b : Bond 𝕜 ι) (l : κ → 𝕜) :
    bondForm 𝕜 ι b (imageMap F E l) = l ⬝ᵥ kernelMap F E b := by
  rw [bondForm_apply, imageMap_apply, kernelMap_apply]
  simp only
  rw [transpose_dot, dotProduct_comm (Fᵀ *ᵥ l), transpose_dot, dotProduct_add]
  ring

variable [DecidableEq ι] [DecidableEq κ]

/-- [proved-derived; formal-checked] **The orthogonal of a kernel form is the image form.** -/
theorem orthogonal_kernelForm (F E : Matrix κ ι 𝕜) :
    (bondForm 𝕜 ι).orthogonal (kernelForm F E) = LinearMap.range (imageMap F E) := by
  ext c
  constructor
  · intro hc
    let ψ : Module.Dual 𝕜 (Bond 𝕜 ι) := (bondForm 𝕜 ι).flip c
    have hψ : ψ ∈ (LinearMap.ker (kernelMap F E)).dualAnnihilator := by
      rw [Submodule.mem_dualAnnihilator]
      intro b hb
      exact hc b hb
    rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hψ
    obtain ⟨χ, hχ⟩ := hψ
    set w : κ → 𝕜 := fun i => χ (Pi.single i 1)
    refine ⟨w, sub_eq_zero.mp (bondForm_separating _ fun b => ?_)⟩
    have h1 : bondForm 𝕜 ι c b = ψ b := by rw [bondForm_symm]; rfl
    have h2 : ψ b = w ⬝ᵥ kernelMap F E b := by
      rw [← hχ, LinearMap.dualMap_apply, dual_eq_dotProduct χ, dotProduct_comm]
    rw [map_sub, LinearMap.sub_apply, bondForm_symm (imageMap F E w), bondForm_imageMap, h1, h2,
      sub_self]
  · rintro ⟨l, rfl⟩ b hb
    rw [bondForm_imageMap, LinearMap.mem_ker.mp hb, dotProduct_zero]

/-- [proved-derived; formal-checked] **A kernel form is Dirac** when `F Eᵀ + E Fᵀ = 0` and
`rank [F | E] = n`. -/
theorem kernelForm_isDirac (F E : Matrix κ ι 𝕜) (hFE : F * Eᵀ + E * Fᵀ = 0)
    (hrank : Module.finrank 𝕜 (LinearMap.range (kernelMap F E)) = Fintype.card ι) :
    IsDirac (bondForm 𝕜 ι) (kernelForm F E) := by
  have hle : LinearMap.range (imageMap F E) ≤ kernelForm F E := by
    rintro _ ⟨l, rfl⟩
    rw [kernelForm, LinearMap.mem_ker, imageMap_apply, kernelMap_apply, mulVec_mulVec,
      mulVec_mulVec, ← add_mulVec, hFE, zero_mulVec]
  have hdim : Module.finrank 𝕜 (Bond 𝕜 ι) = 2 * Fintype.card ι := by
    simp [Module.finrank_prod]; ring
  have hker : Module.finrank 𝕜 (kernelForm F E) = Fintype.card ι := by
    have := LinearMap.finrank_range_add_finrank_ker (kernelMap F E)
    rw [hrank, hdim] at this
    unfold kernelForm; omega
  have horth : Module.finrank 𝕜 ((bondForm 𝕜 ι).orthogonal (kernelForm F E)) =
      Fintype.card ι := by
    rw [LinearMap.BilinForm.finrank_orthogonal bondForm_nondegenerate, hdim, hker]; omega
  unfold IsDirac
  rw [orthogonal_kernelForm] at horth ⊢
  exact Submodule.eq_of_le_of_finrank_eq hle (by rw [horth, hker])

/-- [proved-derived; formal-checked] **The skew graph is a kernel form**: `F = 1`, `E = −J`, with
the Dirac hypotheses discharged. -/
theorem skewGraph_eq_kernelForm (J : Matrix ι ι 𝕜) :
    skewGraph J = kernelForm 1 (-J) := by
  ext b
  simp only [kernelForm, LinearMap.mem_ker, kernelMap_apply, one_mulVec, neg_mulVec]
  show b.1 = J *ᵥ b.2 ↔ _
  constructor
  · intro h; rw [h]; abel
  · intro h; exact eq_of_sub_eq_zero (by simpa [sub_eq_add_neg] using h)

theorem skewGraph_kernel_hypotheses {J : Matrix ι ι 𝕜} (hJ : Jᵀ = -J) :
    (1 : Matrix ι ι 𝕜) * (-J)ᵀ + (-J) * (1 : Matrix ι ι 𝕜)ᵀ = 0 ∧
      Module.finrank 𝕜 (LinearMap.range (kernelMap (1 : Matrix ι ι 𝕜) (-J))) = Fintype.card ι := by
  refine ⟨by rw [Matrix.transpose_neg, hJ]; simp, ?_⟩
  have htop : LinearMap.range (kernelMap (1 : Matrix ι ι 𝕜) (-J)) = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro v; exact ⟨(v, 0), by simp⟩
  rw [htop, finrank_top, Module.finrank_fintype_fun_eq_card]

/-- [proved-derived; formal-checked] **The Kirchhoff structure is a kernel form**, given a cycle
matrix `C` whose columns span `ker dᵀ`: `F = [dᵀ; 0]`, `E = [0; Cᵀ]` (KCL rows, KVL rows). -/
theorem kirchhoff_eq_kernelForm {ν γ : Type*} [Fintype ν] [Fintype γ] [DecidableEq ν]
    [DecidableEq γ] (d : Matrix ι ν 𝕜) (C : Matrix ι γ 𝕜)
    (hC : ∀ w, dᵀ *ᵥ w = 0 ↔ ∃ l, C *ᵥ l = w) :
    kirchhoff d = kernelForm (Matrix.fromRows dᵀ 0) (Matrix.fromRows 0 Cᵀ) := by
  have hkvl : ∀ e : ι → 𝕜, (∃ φ, d *ᵥ φ = e) ↔ Cᵀ *ᵥ e = 0 := by
    intro e
    rw [mem_range_iff_annihilators_vanish]
    constructor
    · intro h
      funext j
      have := h (C *ᵥ Pi.single j 1) ((hC _).mpr ⟨_, rfl⟩)
      rw [dotProduct_comm, ← transpose_dot, dotProduct_comm, dotProduct_single, mul_one] at this
      exact this
    · intro h w hw
      obtain ⟨l, rfl⟩ := (hC w).mp hw
      rw [dotProduct_comm, ← transpose_dot, dotProduct_comm, h, zero_dotProduct]
  ext b
  simp only [kernelForm, LinearMap.mem_ker, kernelMap_apply, Matrix.fromRows_mulVec,
    zero_mulVec]
  constructor
  · rintro ⟨h1, h2⟩
    rw [h1, (hkvl b.2).mp h2]; ext i <;> cases i <;> simp
  · intro h
    have h1 : dᵀ *ᵥ b.1 = 0 := funext fun i => by simpa using congrFun h (Sum.inl i)
    have h2 : Cᵀ *ᵥ b.2 = 0 := funext fun i => by simpa using congrFun h (Sum.inr i)
    exact ⟨h1, (hkvl b.2).mpr h2⟩

omit [DecidableEq ι] in
/-- [proved-derived; formal-checked] **A cycle matrix always exists.** Over a field, the columns of
`C` can be taken to be a basis of `ker dᵀ`, so `ker dᵀ = range C`. -/
theorem exists_cycleMatrix {ν : Type*} [Fintype ν] (d : Matrix ι ν 𝕜) :
    ∃ (k : ℕ) (C : Matrix ι (Fin k) 𝕜), ∀ w, dᵀ *ᵥ w = 0 ↔ ∃ l, C *ᵥ l = w := by
  let K := LinearMap.ker (Matrix.mulVecLin dᵀ)
  let b := Module.finBasis 𝕜 K
  refine ⟨Module.finrank 𝕜 K, Matrix.of fun i j => (b j : ι → 𝕜) i, fun w => ?_⟩
  have hC : ∀ l : Fin (Module.finrank 𝕜 K) → 𝕜,
      (Matrix.of fun i j => (b j : ι → 𝕜) i) *ᵥ l = ((∑ j, l j • b j : K) : ι → 𝕜) := by
    intro l; funext i
    simp [mulVec, dotProduct, Finset.sum_apply, mul_comm]
  constructor
  · intro hw
    have hwK : w ∈ K := by rw [LinearMap.mem_ker]; exact hw
    refine ⟨fun j => b.repr ⟨w, hwK⟩ j, ?_⟩
    rw [hC]
    have := b.sum_repr ⟨w, hwK⟩
    rw [this]
  · rintro ⟨l, rfl⟩
    rw [hC]
    have := (∑ j, l j • b j).2
    rw [LinearMap.mem_ker] at this
    exact this

/-- [proved-derived; formal-checked] **Every Kirchhoff structure is a kernel form**, with no
hypothesis: choose the cycle matrix by `exists_cycleMatrix`. -/
theorem kirchhoff_is_kernelForm {ν : Type*} [Fintype ν] [DecidableEq ν] (d : Matrix ι ν 𝕜) :
    ∃ (k : ℕ) (C : Matrix ι (Fin k) 𝕜),
      kirchhoff d = kernelForm (Matrix.fromRows dᵀ 0) (Matrix.fromRows 0 Cᵀ) := by
  obtain ⟨k, C, hC⟩ := exists_cycleMatrix d
  exact ⟨k, C, kirchhoff_eq_kernelForm d C hC⟩

end KernelForm

/-! ## 8b. Reindexing ports -/

section Reindex

variable {𝕜 : Type*} [Field 𝕜] {ι ι' : Type*} [Fintype ι] [Fintype ι']

/-- [definition] Relabel the ports of a bond along `e : ι ≃ ι'`. -/
def bondReindex (e : ι ≃ ι') : Bond 𝕜 ι ≃ₗ[𝕜] Bond 𝕜 ι' :=
  (LinearEquiv.funCongrLeft 𝕜 𝕜 e.symm).prodCongr (LinearEquiv.funCongrLeft 𝕜 𝕜 e.symm)

omit [Fintype ι] [Fintype ι'] in
@[simp] theorem bondReindex_apply (e : ι ≃ ι') (b : Bond 𝕜 ι) :
    bondReindex e b = (b.1 ∘ e.symm, b.2 ∘ e.symm) := rfl

/-- [proved-derived; formal-checked] Relabelling ports preserves the pairing. -/
theorem bondForm_reindex (e : ι ≃ ι') (b c : Bond 𝕜 ι) :
    bondForm 𝕜 ι' (bondReindex e b) (bondReindex e c) = bondForm 𝕜 ι b c := by
  simp only [bondForm_apply, bondReindex_apply, dotProduct, Function.comp_apply]
  rw [e.symm.sum_comp (fun i => b.2 i * c.1 i), e.symm.sum_comp (fun i => c.2 i * b.1 i)]

/-- [proved-derived; formal-checked] **Relabelling ports preserves Dirac structures.** -/
theorem IsDirac.reindex {D : Submodule 𝕜 (Bond 𝕜 ι)} (hD : IsDirac (bondForm 𝕜 ι) D)
    (e : ι ≃ ι') : IsDirac (bondForm 𝕜 ι') (D.map ((bondReindex (𝕜 := 𝕜) e).toLinearMap)) := by
  apply isDirac_of
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simp only [LinearEquiv.coe_coe]
    rw [bondForm_reindex]
    exact hD.pairing_eq_zero hx hy
  · intro y hy
    refine ⟨(bondReindex e).symm y, ?_, by simp⟩
    rw [← hD]
    intro x hx
    have := hy (bondReindex e x) ⟨x, hx, rfl⟩
    rw [← bondForm_reindex e, LinearEquiv.apply_symm_apply]
    exact this

end Reindex

/-! ## 9. Witnesses for the kernel form and the interconnection -/

/-- [definition] The triangle's cycle matrix: the one loop `(1, 1, 1)`. -/
def triangleCycle : Matrix (Fin 3) (Fin 1) ℚ := !![1; 1; 1]

/-- [proved-derived; formal-checked] The loop spans the triangle's KCL space. -/
theorem triangleCycle_spans (w : Fin 3 → ℚ) :
    triangleᵀ *ᵥ w = 0 ↔ ∃ l, triangleCycle *ᵥ l = w := by
  constructor
  · intro h
    have h0 := congrFun h 0; have h1 := congrFun h 1
    simp [triangle, mulVec, dotProduct, Fin.sum_univ_three] at h0 h1
    refine ⟨![w 0], ?_⟩
    ext i; fin_cases i <;> simp [triangleCycle, mulVec, dotProduct] <;> linarith
  · rintro ⟨l, rfl⟩
    ext i; fin_cases i <;> simp [triangle, triangleCycle, mulVec, dotProduct, Fin.sum_univ_three]

/-- [proved-derived; formal-checked] **Witness: the triangle's Kirchhoff structure in kernel form**
(`KCL` rows `dᵀ`, `KVL` row `(1,1,1)ᵀ`). -/
theorem triangle_kernelForm :
    kirchhoff triangle = kernelForm (Matrix.fromRows triangleᵀ 0) (Matrix.fromRows 0 triangleCycleᵀ) :=
  kirchhoff_eq_kernelForm triangle triangleCycle triangleCycle_spans

/-- [definition] A gyrator between an outer port and a shared port, as a skew map on `Fin 1 ⊕ Fin 1`. -/
def gyrator₂ : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℚ := Matrix.fromBlocks 0 (-1) 1 0

theorem gyrator₂_skew : gyrator₂ᵀ = -gyrator₂ := by
  rw [gyrator₂, Matrix.fromBlocks_transpose, Matrix.fromBlocks_neg]; simp

/-- [proved-derived; formal-checked] **Witness: two gyrators interconnected are a transformer.**
The composite of two gyrators through a shared port is Dirac, and it carries the bond
`f = (1, −1)`, `e = (2, 2)` through the shared bond `(f_s, e_s) = (2, −1)`, with power `0`. -/
theorem gyrator_chain_witness :
    IsDirac (bondForm ℚ (Fin 1 ⊕ Fin 1)) (interconnect (skewGraph gyrator₂) (skewGraph gyrator₂)) ∧
    ((Sum.elim ![1] ![-1], Sum.elim ![2] ![2]) : Bond ℚ (Fin 1 ⊕ Fin 1)) ∈
      interconnect (skewGraph gyrator₂) (skewGraph gyrator₂) ∧
    power ((Sum.elim ![1] ![-1], Sum.elim ![2] ![2]) : Bond ℚ (Fin 1 ⊕ Fin 1)) = 0 := by
  refine ⟨interconnect_isDirac (skewGraph_isDirac gyrator₂_skew) (skewGraph_isDirac gyrator₂_skew),
    mem_interconnect.mpr ⟨(![2], ![-1]), ?_, ?_⟩, ?_⟩
  · show _ = gyrator₂ *ᵥ _
    ext i; rcases i with i | i <;> fin_cases i <;>
      simp [partA, gyrator₂, mulVec, dotProduct, Matrix.fromBlocks, Fintype.sum_sum_type]
  · show _ = gyrator₂ *ᵥ _
    ext i; rcases i with i | i <;> fin_cases i <;>
      simp [partB, gyrator₂, mulVec, dotProduct, Matrix.fromBlocks, Fintype.sum_sum_type]
  · simp [power, dotProduct, Fintype.sum_sum_type]

end Soma.Holonics.HolonCore
