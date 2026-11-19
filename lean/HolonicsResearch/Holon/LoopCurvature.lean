import Mathlib
import Holonics.Holon.Complex

/-!
# Loop curvature: first Betti numbers, the zero-reduced-cost lemma, small resolving sets

Source: the loop-curvature record of September 28
(`research/records/2026-09-28_A_LOOP_READS_THE_CURVATURE_IT_ENCLOSES_RINGS_TUBES_EGGS_AND_NAVIGATION_BY_REWEIGHTING.md`,
§6 and §10), whose owed list (#62, carried as a box of #410) reads: "the first Betti numbers over
`Holon/Complex`; the zero-reduced-cost lemma; the small metric-dimension cases as finite checks".
They were checked only by `research/notebook/motion/loop_curvature_checks.py`.

## What is proved

* **The first Betti number of a two-term cochain complex over `ℚ`.** For an incidence
  `d₀ : Matrix E V ℚ` and a face coboundary `d₁ : Matrix F E ℚ` with `d₁ d₀ = 0`, the closed
  cochains contain the exact ones (`range_le_ker`), and
  `b₁ = dim ker d₁ − dim im d₀ = |E| − rank d₀ − rank d₁` (`betti1_eq_card_sub_ranks`). When the
  vertex kernel and the face kernel of the transpose are each one line (a connected graph, a
  connected closed oriented surface), `b₁ = |E| − |V| − |F| + 2` (`betti1_of_kernels_lines`).
* **The incidence is the owner's.** The vertex incidence of every complex here is
  `Holon/Complex.connectionIncidence` at the trivial connection (`torusIncidence`,
  `cubeIncidence`).
* **The square-celled torus `C_m × C_n`**, for every `m, n ≥ 1`: `∂² = 0`
  (`torusCoboundary_mul_incidence`), the vertex and face kernels are the constants, and
  `b₁(T²) = 2` (`torus_betti1`). The two loops are not exact: the cochain that counts the
  horizontal edges of one column is closed and reads `1` round a horizontal loop, where every exact
  cochain reads `0` (`torus_column_closed`, `torus_column_not_exact`).
* **The cube's surface**, a sphere with eight vertices, twelve edges and six square faces:
  `∂² = 0`, the kernels are the constants, `b₁(S²) = 0` (`cube_betti1`), so every closed cochain
  is exact (`cube_closed_is_exact`).
* **The zero-reduced-cost lemma** (§6). For a feasible potential `h` (`h u ≤ c(u, v) + h v` on
  every edge), the reduced cost `c′ = c − h(u) + h(v)` is nonnegative, telescopes along every walk
  (`walkCost_reduced`), every walk from `s` to `t` costs at least `h s − h t`, a walk along
  zero-reduced-cost edges attains it and is therefore least (`zero_reduced_walk_is_least`), and
  every edge of a walk that attains it has zero reduced cost (`attaining_walk_edges_zero`).
  Choosing the neighbour of least `h` is not optimal: `s → t` of cost 9, `s → b` and `b → t` of
  cost 1 (`least_h_neighbour_counterexample`).
* **Small metric dimensions as finite checks** (§6). A set of vertices resolves when the distances
  to it identify every vertex. Each distance table used is certified as the graph distance by its
  Bellman equation (`IsBellmanDistance`, decided), and a Bellman distance is unique
  (`bellman_unique`). Then: the path `P₃` needs 1 landmark and the star `K_(1,3)` needs 2, though
  both are contractible trees (`path3_metricDimension`, `star_metricDimension`); the grid
  `P₄ □ P₄` needs 2 (`grid44_metricDimension`); the prism `C₅ □ P₂` needs 2 and `C₆ □ P₂` needs 3
  (`prism5_metricDimension`, `prism6_metricDimension`).

## Limits

* `b₁` is the cohomological count over `ℚ`; the homological count is the same number by
  `Matrix.rank_transpose`, used in the proofs, and integral torsion is not read.
* The faces are new here: `Holon/Complex` reads a cell as a closed walk of forward edges, and a
  square's boundary traverses two of its edges backwards, so the face coboundary is given as a
  signed matrix and joined to the owner only through `∂² = 0` against its incidence.
* The zero-reduced-cost lemma is proved for finite walks that reach the goal; the termination rule
  against zero-cost cycles the record names is the walk's finiteness here, and no search procedure
  is built.
* The tori `C₄ □ C₄` (4) and `C₅ □ C₅` (3) are checked in `Holon/TorusMetricDimension`, whose
  refusals are read through the torus's translations on the triples and pairs that hold `0`; here
  their refusals over every triple or 625 pairs ran past this file's budget, and an enumeration by
  `Finset.powersetCard` ran the kernel out of memory on the grid. The distance tables are certified
  by their Bellman equation, not joined to Mathlib's `SimpleGraph.dist`.

The computational object is the helical pair interaction; of the winding guide's six objects this
touches cell holonomy (the face as a cycle and its Betti count), keeping the helix, the pair, faces
and placement, the tube and the tower thread attached through `Holon/Complex`.

Consumers: the record's §10 reading that the harmonic circulations a complex can hold number its
`b₁`, and the atlas rows on loop curvature and routing landmarks.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Holon.LoopCurvature

open Matrix Module Holonics.HolonCore

/-! ## 1. The first Betti number of a two-term cochain complex -/

section Betti

variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]

/-- [definition] The first Betti number of the cochain complex `d₀ : ℚ^V → ℚ^E`,
`d₁ : ℚ^E → ℚ^F`: the dimension of the closed cochains less that of the exact ones. -/
noncomputable def betti1 (d0 : Matrix E V ℚ) (d1 : Matrix F E ℚ) : ℤ :=
  (finrank ℚ (LinearMap.ker d1.mulVecLin) : ℤ) - (finrank ℚ (LinearMap.range d0.mulVecLin) : ℤ)

omit [Fintype F] in
/-- [proved-derived; formal-checked] `∂² = 0` puts the exact cochains inside the closed ones. -/
theorem range_le_ker (d0 : Matrix E V ℚ) (d1 : Matrix F E ℚ)
    (h : ∀ φ : V → ℚ, d1 *ᵥ (d0 *ᵥ φ) = 0) :
    LinearMap.range d0.mulVecLin ≤ LinearMap.ker d1.mulVecLin := by
  rintro _ ⟨φ, rfl⟩
  simpa [LinearMap.mem_ker] using h φ

omit [Fintype F] in
/-- [proved-derived; formal-checked] Rank–nullity on the closed cochains:
`b₁ = |E| − rank d₀ − rank d₁`. -/
theorem betti1_eq_card_sub_ranks (d0 : Matrix E V ℚ) (d1 : Matrix F E ℚ) :
    betti1 d0 d1 = (Fintype.card E : ℤ) - d0.rank - d1.rank := by
  have hrn := LinearMap.finrank_range_add_finrank_ker d1.mulVecLin
  rw [Module.finrank_fintype_fun_eq_card] at hrn
  unfold betti1 Matrix.rank
  omega

/-- [proved-derived; formal-checked] A matrix's rank is its source dimension less its kernel's. -/
theorem rank_eq_card_sub_ker {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℚ) :
    (A.rank : ℤ) = (Fintype.card n : ℤ) - finrank ℚ (LinearMap.ker A.mulVecLin) := by
  have hrn := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  rw [Module.finrank_fintype_fun_eq_card] at hrn
  unfold Matrix.rank
  omega

/-- [proved-derived; formal-checked] **Euler's count.** When the vertex kernel of `d₀` and the
face kernel of `d₁ᵀ` are one line each, `b₁ = |E| − |V| − |F| + 2`. -/
theorem betti1_of_kernels_lines (d0 : Matrix E V ℚ) (d1 : Matrix F E ℚ)
    (h0 : finrank ℚ (LinearMap.ker d0.mulVecLin) = 1)
    (h1 : finrank ℚ (LinearMap.ker d1ᵀ.mulVecLin) = 1) :
    betti1 d0 d1 =
      (Fintype.card E : ℤ) - Fintype.card V - Fintype.card F + 2 := by
  rw [betti1_eq_card_sub_ranks, rank_eq_card_sub_ker d0, ← Matrix.rank_transpose d1,
    rank_eq_card_sub_ker d1ᵀ, h0, h1]
  ring

omit [Fintype F] in
/-- [proved-derived; formal-checked] At `b₁ = 0` with `∂² = 0` every closed cochain is exact. -/
theorem closed_is_exact_of_betti1_zero (d0 : Matrix E V ℚ) (d1 : Matrix F E ℚ)
    (h : ∀ φ : V → ℚ, d1 *ᵥ (d0 *ᵥ φ) = 0) (hb : betti1 d0 d1 = 0) :
    LinearMap.ker d1.mulVecLin = LinearMap.range d0.mulVecLin := by
  have hle := range_le_ker d0 d1 h
  have heq : finrank ℚ (LinearMap.range d0.mulVecLin) =
      finrank ℚ (LinearMap.ker d1.mulVecLin) := by
    unfold betti1 at hb; omega
  exact (Submodule.eq_of_le_of_finrank_eq hle heq).symm

/-- [proved-derived; formal-checked] A kernel that is exactly the constant line has dimension one. -/
theorem finrank_ker_eq_one_of_constants {n m : Type*} [Fintype n] [Fintype m] [Nonempty n]
    (A : Matrix m n ℚ) (hconst : A *ᵥ (fun _ => (1 : ℚ)) = 0)
    (hker : ∀ φ : n → ℚ, A *ᵥ φ = 0 → ∀ i j, φ i = φ j) :
    finrank ℚ (LinearMap.ker A.mulVecLin) = 1 := by
  have hspan : LinearMap.ker A.mulVecLin = ℚ ∙ (fun _ : n => (1 : ℚ)) := by
    ext φ
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, Submodule.mem_span_singleton]
    constructor
    · intro hφ
      obtain ⟨i₀⟩ := ‹Nonempty n›
      refine ⟨φ i₀, ?_⟩
      funext j
      simp [hker φ hφ i₀ j]
    · rintro ⟨c, rfl⟩
      rw [Matrix.mulVec_smul, hconst, smul_zero]
  rw [hspan]
  apply finrank_span_singleton
  intro h
  obtain ⟨i₀⟩ := ‹Nonempty n›
  have := congrFun h i₀
  simp at this

end Betti

/-! ## 2. The square-celled torus `C_m × C_n` -/

section Torus

variable (m n : ℕ) [NeZero m] [NeZero n]

/-- [definition] The torus's vertices, `ℤ/m × ℤ/n`. -/
abbrev TorusVertex := ZMod m × ZMod n

/-- [definition] The torus's edges: a horizontal edge `(a, b) → (a + 1, b)` on the left, a
vertical edge `(a, b) → (a, b + 1)` on the right. -/
abbrev TorusEdge := TorusVertex m n ⊕ TorusVertex m n

/-- [definition] The source of an edge. -/
def torusSrc : TorusEdge m n → TorusVertex m n := Sum.elim id id

/-- [definition] The target of an edge. -/
def torusTgt : TorusEdge m n → TorusVertex m n :=
  Sum.elim (fun x => (x.1 + 1, x.2)) (fun x => (x.1, x.2 + 1))

/-- [definition] The torus's incidence: `Holon/Complex.connectionIncidence` at the trivial
connection, `(d₀ φ)_e = φ(t e) − φ(s e)`. -/
noncomputable def torusIncidence : Matrix (TorusEdge m n) (TorusVertex m n) ℚ :=
  connectionIncidence (torusSrc m n) (torusTgt m n) (fun _ => 1)

/-- [definition] The face coboundary of the square at `(a, b)`, whose boundary runs
`(a, b) → (a + 1, b) → (a + 1, b + 1) → (a, b + 1) → (a, b)`: its horizontal edges at `b` and
`b + 1` with signs `+, −`, its vertical edges at `a + 1` and `a` with signs `+, −`. -/
def torusCoboundary : Matrix (TorusVertex m n) (TorusEdge m n) ℚ :=
  Matrix.of fun f e =>
    (if e = Sum.inl f then 1 else 0) - (if e = Sum.inl (f.1, f.2 + 1) then 1 else 0) +
      (if e = Sum.inr (f.1 + 1, f.2) then 1 else 0) - (if e = Sum.inr f then 1 else 0)

variable {m n}

theorem torusIncidence_inl (φ : TorusVertex m n → ℚ) (x : TorusVertex m n) :
    (torusIncidence m n *ᵥ φ) (Sum.inl x) = φ (x.1 + 1, x.2) - φ x := by
  rw [torusIncidence, connectionIncidence_mulVec]
  simp [torusSrc, torusTgt]

theorem torusIncidence_inr (φ : TorusVertex m n → ℚ) (x : TorusVertex m n) :
    (torusIncidence m n *ᵥ φ) (Sum.inr x) = φ (x.1, x.2 + 1) - φ x := by
  rw [torusIncidence, connectionIncidence_mulVec]
  simp [torusSrc, torusTgt]

theorem torusCoboundary_mulVec (ω : TorusEdge m n → ℚ) (f : TorusVertex m n) :
    (torusCoboundary m n *ᵥ ω) f =
      ω (Sum.inl f) - ω (Sum.inl (f.1, f.2 + 1)) + ω (Sum.inr (f.1 + 1, f.2)) -
        ω (Sum.inr f) := by
  simp only [torusCoboundary, mulVec, dotProduct, of_apply, add_mul, sub_mul, ite_mul, one_mul,
    zero_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

/-- [proved-derived; formal-checked] **`∂² = 0` on the torus**: the face coboundary of an exact
cochain vanishes. -/
theorem torusCoboundary_mul_incidence (φ : TorusVertex m n → ℚ) :
    torusCoboundary m n *ᵥ (torusIncidence m n *ᵥ φ) = 0 := by
  funext f
  rw [torusCoboundary_mulVec, torusIncidence_inl, torusIncidence_inl, torusIncidence_inr,
    torusIncidence_inr]
  simp only [Pi.zero_apply]
  ring

/-- A sum over the vertices of an indicator at a shifted vertex reads the shift's preimage. -/
theorem sum_indicator_shift (c : TorusVertex m n → ℚ) (x y : TorusVertex m n)
    (σ : TorusVertex m n → TorusVertex m n) (hσ : ∀ f, σ f = x ↔ f = y) :
    (∑ f, if x = σ f then c f else 0) = c y := by
  rw [Finset.sum_eq_single y]
  · simp [((hσ y).mpr rfl).symm]
  · intro b _ hb
    rw [if_neg]
    intro h
    exact hb ((hσ b).mp h.symm)
  · simp

theorem torusCoboundary_transpose_inl (c : TorusVertex m n → ℚ) (x : TorusVertex m n) :
    ((torusCoboundary m n)ᵀ *ᵥ c) (Sum.inl x) = c x - c (x.1, x.2 - 1) := by
  simp only [torusCoboundary, mulVec, dotProduct, transpose_apply, of_apply, Sum.inl.injEq,
    reduceCtorEq, if_false, sub_zero, add_zero, sub_mul, ite_mul, one_mul, zero_mul,
    Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [sum_indicator_shift c x (x.1, x.2 - 1) (fun f => (f.1, f.2 + 1))]
  intro f
  constructor
  · rintro rfl; simp
  · rintro rfl; simp

theorem torusCoboundary_transpose_inr (c : TorusVertex m n → ℚ) (x : TorusVertex m n) :
    ((torusCoboundary m n)ᵀ *ᵥ c) (Sum.inr x) = c (x.1 - 1, x.2) - c x := by
  simp only [torusCoboundary, mulVec, dotProduct, transpose_apply, of_apply, Sum.inr.injEq,
    reduceCtorEq, if_false, sub_zero, zero_add, sub_mul, ite_mul, one_mul, zero_mul,
    Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [sum_indicator_shift c x (x.1 - 1, x.2) (fun f => (f.1 + 1, f.2))]
  · intro f
    constructor
    · rintro rfl; simp
    · rintro rfl; simp

/-- [proved-derived; formal-checked] A function on `ℤ/m` that returns after every step is
constant. -/
theorem zmod_const_of_step {k : ℕ} [NeZero k] (g : ZMod k → ℚ) (h : ∀ x, g (x + 1) = g x) :
    ∀ x, g x = g 0 := by
  intro x
  rw [← ZMod.natCast_zmod_val x]
  induction x.val with
  | zero => simp
  | succ j ih => rw [Nat.cast_succ, h, ih]

theorem torus_const_of_steps (g : TorusVertex m n → ℚ)
    (h1 : ∀ x : TorusVertex m n, g (x.1 + 1, x.2) = g x)
    (h2 : ∀ x : TorusVertex m n, g (x.1, x.2 + 1) = g x) :
    ∀ x y, g x = g y := by
  have hrow : ∀ a b, g (a, b) = g (a, 0) := fun a =>
    zmod_const_of_step (fun b => g (a, b)) (fun b => h2 (a, b))
  have hcol : ∀ a, g (a, 0) = g (0, 0) :=
    zmod_const_of_step (fun a => g (a, 0)) (fun a => h1 (a, 0))
  intro x y
  rw [hrow x.1 x.2, hrow y.1 y.2, hcol x.1, hcol y.1]

/-- [proved-derived; formal-checked] The torus's vertex kernel is the constant line. -/
theorem torusIncidence_ker :
    finrank ℚ (LinearMap.ker (torusIncidence m n).mulVecLin) = 1 := by
  apply finrank_ker_eq_one_of_constants
  · funext e
    cases e with
    | inl x => rw [torusIncidence_inl]; simp
    | inr x => rw [torusIncidence_inr]; simp
  · intro φ hφ
    apply torus_const_of_steps
    · intro x
      have := congrFun hφ (Sum.inl x)
      rw [torusIncidence_inl] at this
      simp only [Pi.zero_apply] at this
      linarith
    · intro x
      have := congrFun hφ (Sum.inr x)
      rw [torusIncidence_inr] at this
      simp only [Pi.zero_apply] at this
      linarith

/-- [proved-derived; formal-checked] The torus's face kernel (of the transpose) is the constant
line: the sum of all squares is the one two-cycle. -/
theorem torusCoboundary_transpose_ker :
    finrank ℚ (LinearMap.ker (torusCoboundary m n)ᵀ.mulVecLin) = 1 := by
  apply finrank_ker_eq_one_of_constants
  · funext e
    cases e with
    | inl x => rw [torusCoboundary_transpose_inl]; simp
    | inr x => rw [torusCoboundary_transpose_inr]; simp
  · intro c hc
    apply torus_const_of_steps
    · intro x
      have := congrFun hc (Sum.inr (x.1 + 1, x.2))
      rw [torusCoboundary_transpose_inr] at this
      simp only [Pi.zero_apply, add_sub_cancel_right] at this
      linarith
    · intro x
      have := congrFun hc (Sum.inl (x.1, x.2 + 1))
      rw [torusCoboundary_transpose_inl] at this
      simp only [Pi.zero_apply, add_sub_cancel_right] at this
      linarith

/-- [proved-derived; formal-checked] **`b₁(T²) = 2`** for the square-celled torus `C_m × C_n`,
every `m, n ≥ 1`: `2mn − mn − mn + 2`. -/
theorem torus_betti1 : betti1 (torusIncidence m n) (torusCoboundary m n) = 2 := by
  rw [betti1_of_kernels_lines _ _ torusIncidence_ker torusCoboundary_transpose_ker]
  simp only [Fintype.card_sum, Fintype.card_prod, ZMod.card]
  push_cast
  ring

/-- [definition] The cochain that counts the horizontal edges of the column `a = 0`. -/
def torusColumn : TorusEdge m n → ℚ :=
  Sum.elim (fun x => if x.1 = 0 then 1 else 0) (fun _ => 0)

/-- [proved-derived; formal-checked] The column cochain is closed. -/
theorem torus_column_closed : torusCoboundary m n *ᵥ torusColumn = 0 := by
  funext f
  rw [torusCoboundary_mulVec]
  simp [torusColumn]

/-- [proved-derived; formal-checked] **A harmonic loop is not exact.** The column cochain reads `1`
round the horizontal loop at `b = 0`, where every exact cochain reads `0`. -/
theorem torus_column_not_exact : ¬ ∃ φ, torusIncidence m n *ᵥ φ = torusColumn := by
  rintro ⟨φ, hφ⟩
  have hloop : (∑ a : ZMod m, (torusIncidence m n *ᵥ φ) (Sum.inl (a, 0))) = 0 := by
    simp only [torusIncidence_inl, Finset.sum_sub_distrib]
    rw [sub_eq_zero]
    exact Fintype.sum_equiv (Equiv.addRight 1) _ _ (fun a => rfl)
  rw [hφ] at hloop
  simp [torusColumn] at hloop

end Torus

/-! ## 3. The cube's surface, a sphere -/

section Cube

/-- [definition] The cube's vertices `4x + 2y + z`, its twelve edges oriented upward in the one
coordinate that changes: four in `x`, four in `y`, four in `z`. -/
def cubeSrc : Fin 12 → Fin 8 := ![0, 1, 2, 3, 0, 1, 4, 5, 0, 2, 4, 6]

/-- [definition] The edges' targets. -/
def cubeTgt : Fin 12 → Fin 8 := ![4, 5, 6, 7, 2, 3, 6, 7, 1, 3, 5, 7]

/-- [definition] The cube's incidence: `Holon/Complex.connectionIncidence` at the trivial
connection. -/
noncomputable def cubeIncidence : Matrix (Fin 12) (Fin 8) ℚ :=
  connectionIncidence cubeSrc cubeTgt (fun _ => 1)

/-- [definition] The six square faces, consistently oriented (each edge meets two faces with
opposite signs): `x = 0, x = 1, y = 0, y = 1, z = 0, z = 1`. -/
def cubeCoboundary : Matrix (Fin 6) (Fin 12) ℚ :=
  !![0, 0, 0, 0, -1, 1, 0, 0, 1, -1, 0, 0;
     0, 0, 0, 0, 0, 0, 1, -1, 0, 0, -1, 1;
     1, -1, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0;
     0, 0, -1, 1, 0, 0, 0, 0, 0, 1, 0, -1;
     -1, 0, 1, 0, 1, 0, -1, 0, 0, 0, 0, 0;
     0, 1, 0, -1, 0, -1, 0, 1, 0, 0, 0, 0]

theorem cubeIncidence_apply (φ : Fin 8 → ℚ) (e : Fin 12) :
    (cubeIncidence *ᵥ φ) e = φ (cubeTgt e) - φ (cubeSrc e) := by
  rw [cubeIncidence, connectionIncidence_mulVec]
  simp

/-- [proved-derived; formal-checked] `∂² = 0` on the cube's surface. -/
theorem cubeCoboundary_mul_incidence (φ : Fin 8 → ℚ) :
    cubeCoboundary *ᵥ (cubeIncidence *ᵥ φ) = 0 := by
  funext f
  have hω : ∀ e, (cubeIncidence *ᵥ φ) e = φ (cubeTgt e) - φ (cubeSrc e) := cubeIncidence_apply φ
  generalize cubeIncidence *ᵥ φ = ω at hω ⊢
  fin_cases f <;>
    simp [mulVec, dotProduct, Fin.sum_univ_succ, cubeCoboundary, hω, cubeSrc, cubeTgt] <;> ring

/-- [proved-derived; formal-checked] The cube's vertex kernel is the constant line. -/
theorem cubeIncidence_ker : finrank ℚ (LinearMap.ker cubeIncidence.mulVecLin) = 1 := by
  apply finrank_ker_eq_one_of_constants
  · funext e
    rw [cubeIncidence_apply]
    simp
  · intro φ hφ
    have h : ∀ e, φ (cubeTgt e) = φ (cubeSrc e) := fun e => by
      have := congrFun hφ e
      rw [cubeIncidence_apply] at this
      simp only [Pi.zero_apply] at this
      linarith
    have h0 : ∀ i, φ i = φ 0 := by
      have := h 0; have := h 1; have := h 2; have := h 3; have := h 4; have := h 5
      have := h 6; have := h 7; have := h 8; have := h 9; have := h 10; have := h 11
      simp only [cubeSrc, cubeTgt] at *
      intro i
      fin_cases i <;> simp at * <;> linarith
    intro i j
    rw [h0 i, h0 j]

/-- [proved-derived; formal-checked] The cube's face kernel (of the transpose) is the constant
line. -/
theorem cubeCoboundary_transpose_ker :
    finrank ℚ (LinearMap.ker cubeCoboundaryᵀ.mulVecLin) = 1 := by
  apply finrank_ker_eq_one_of_constants
  · funext e
    fin_cases e <;> simp [cubeCoboundary, mulVec, dotProduct, Fin.sum_univ_succ]
  · intro c hc
    have h : ∀ e, (cubeCoboundaryᵀ *ᵥ c) e = 0 := fun e => congrFun hc e
    have := h 0; have := h 1; have := h 2; have := h 3; have := h 4; have := h 5
    have := h 6; have := h 7; have := h 8; have := h 9; have := h 10; have := h 11
    simp [cubeCoboundary, mulVec, dotProduct, Fin.sum_univ_succ] at *
    have h0 : ∀ i, c i = c 0 := by
      intro i
      fin_cases i <;> simp <;> linarith
    intro i j
    rw [h0 i, h0 j]

/-- [proved-derived; formal-checked] **`b₁(S²) = 0`** on the cube's surface: `12 − 8 − 6 + 2`. -/
theorem cube_betti1 : betti1 cubeIncidence cubeCoboundary = 0 := by
  rw [betti1_of_kernels_lines _ _ cubeIncidence_ker cubeCoboundary_transpose_ker]
  simp

/-- [proved-derived; formal-checked] **On the sphere every closed cochain is exact**: a loop on
it holds no harmonic circulation. -/
theorem cube_closed_is_exact :
    LinearMap.ker cubeCoboundary.mulVecLin = LinearMap.range cubeIncidence.mulVecLin :=
  closed_is_exact_of_betti1_zero _ _ cubeCoboundary_mul_incidence cube_betti1

end Cube

/-! ## 4. Navigation by reweighting: the zero-reduced-cost lemma -/

section Reweighting

variable {α : Type*} (adj : α → α → Prop) (c : α → α → ℚ) (h : α → ℚ)

/-- [definition] The reduced cost of an edge under a potential: `c′(u, v) = c(u, v) − h u + h v`. -/
def reducedCost (u v : α) : ℚ := c u v - h u + h v

/-- [definition] The cost of a walk from `u` through the listed vertices. -/
def walkCost (c : α → α → ℚ) : α → List α → ℚ
  | _, [] => 0
  | u, v :: rest => c u v + walkCost c v rest

/-- [definition] The end of a walk from `u` through the listed vertices. -/
def walkEnd : α → List α → α
  | u, [] => u
  | _, v :: rest => walkEnd v rest

/-- [definition] Every step of the walk is an edge. -/
def IsEdgeWalk : α → List α → Prop
  | _, [] => True
  | u, v :: rest => adj u v ∧ IsEdgeWalk v rest

/-- [definition] Every step of the walk has zero reduced cost. -/
def AllZeroReduced : α → List α → Prop
  | _, [] => True
  | u, v :: rest => reducedCost c h u v = 0 ∧ AllZeroReduced v rest

/-- [definition] A feasible potential: `h u ≤ c(u, v) + h v` on every edge. -/
def Feasible : Prop := ∀ u v, adj u v → h u ≤ c u v + h v

/-- [proved-derived; formal-checked] **Reduced costs telescope**: along any walk the reduced cost is
the cost less `h` at the start plus `h` at the end. Reweighting is not a metric; path costs move
by their endpoints alone. -/
theorem walkCost_reduced : ∀ (u : α) (l : List α),
    walkCost (reducedCost c h) u l = walkCost c u l - h u + h (walkEnd u l)
  | u, [] => by simp [walkCost, walkEnd]
  | u, v :: rest => by
      rw [walkCost, walkCost, walkEnd, walkCost_reduced v rest, reducedCost]
      ring

variable {adj c h}

/-- [proved-derived; formal-checked] Under a feasible potential the reduced cost of an edge is
nonnegative. -/
theorem reducedCost_nonneg (hf : Feasible adj c h) {u v : α} (huv : adj u v) :
    0 ≤ reducedCost c h u v := by
  have := hf u v huv
  unfold reducedCost
  linarith

/-- [proved-derived; formal-checked] Under a feasible potential every walk along edges costs at
least `h(start) − h(end)`. -/
theorem walkCost_ge (hf : Feasible adj c h) :
    ∀ (u : α) (l : List α), IsEdgeWalk adj u l → h u - h (walkEnd u l) ≤ walkCost c u l
  | u, [], _ => by simp [walkCost, walkEnd]
  | u, v :: rest, ⟨huv, hrest⟩ => by
      have := walkCost_ge hf v rest hrest
      have := hf u v huv
      rw [walkCost, walkEnd]
      linarith

/-- [proved-derived; formal-checked] A walk along zero-reduced-cost edges costs exactly
`h(start) − h(end)`. -/
theorem walkCost_of_allZero : ∀ (u : α) (l : List α), AllZeroReduced c h u l →
    walkCost c u l = h u - h (walkEnd u l)
  | u, [], _ => by simp [walkCost, walkEnd]
  | u, v :: rest, ⟨hz, hrest⟩ => by
      have := walkCost_of_allZero v rest hrest
      unfold reducedCost at hz
      rw [walkCost, walkEnd]
      linarith

/-- [proved-derived; formal-checked] **The zero-reduced-cost lemma.** Under a feasible potential,
a walk along zero-reduced-cost edges is least among all edge walks with the same ends. -/
theorem zero_reduced_walk_is_least (hf : Feasible adj c h) {s : α} {l l' : List α}
    (hz : AllZeroReduced c h s l) (hw' : IsEdgeWalk adj s l')
    (hend : walkEnd s l' = walkEnd s l) : walkCost c s l ≤ walkCost c s l' := by
  rw [walkCost_of_allZero s l hz, ← hend]
  exact walkCost_ge hf s l' hw'

/-- [proved-derived; formal-checked] **A walk that attains the bound runs on zero-reduced-cost
edges**: with `h` the exact distance, the edges of shortest paths have `c′ = 0`. -/
theorem attaining_walk_edges_zero (hf : Feasible adj c h) :
    ∀ (u : α) (l : List α), IsEdgeWalk adj u l →
      walkCost c u l = h u - h (walkEnd u l) → AllZeroReduced c h u l
  | u, [], _, _ => trivial
  | u, v :: rest, ⟨huv, hrest⟩, heq => by
      have hge := walkCost_ge hf v rest hrest
      have hnn := reducedCost_nonneg hf huv
      rw [walkCost, walkEnd] at heq
      unfold reducedCost at hnn
      have hzero : reducedCost c h u v = 0 := by unfold reducedCost; linarith
      refine ⟨hzero, attaining_walk_edges_zero hf v rest hrest ?_⟩
      unfold reducedCost at hzero
      linarith

/-! The record's counterexample: `s = 0`, `b = 1`, `t = 2`. -/

/-- [definition] The three edges `s → t`, `s → b`, `b → t`. -/
def exampleAdj (u v : Fin 3) : Prop := (u = 0 ∧ v = 2) ∨ (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 2)

/-- [definition] Their costs `9, 1, 1`. -/
def exampleCost (u v : Fin 3) : ℚ :=
  if u = 0 ∧ v = 2 then 9 else if u = 0 ∧ v = 1 then 1 else if u = 1 ∧ v = 2 then 1 else 0

/-- [definition] The exact distance to `t`. -/
def exampleH (v : Fin 3) : ℚ := if v = 0 then 2 else if v = 1 then 1 else 0

/-- [counterexample; formal-checked] **Choosing the neighbour of least `h` is not optimal.** The
exact distance is feasible; the neighbour of `s` with least `h` is `t` (`h = 0 < 1`), whose walk
costs `9`, while the walk through `b` costs `2`; the zero-reduced-cost neighbour is `b` alone. -/
theorem least_h_neighbour_counterexample :
    Feasible exampleAdj exampleCost exampleH ∧
      exampleH 2 < exampleH 1 ∧
      walkCost exampleCost 0 [2] = 9 ∧ walkCost exampleCost 0 [1, 2] = 2 ∧
      reducedCost exampleCost exampleH 0 1 = 0 ∧ reducedCost exampleCost exampleH 0 2 = 7 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u v huv
    rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      norm_num +decide [exampleCost, exampleH]
  all_goals norm_num +decide [walkCost, exampleCost, exampleH, reducedCost]

end Reweighting

/-! ## 5. Landmarks that locate: small metric dimensions as finite checks -/

section MetricDimension

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- [definition] A set of vertices **resolves** a distance when the distances to it identify every
vertex. -/
def Resolves (d : α → α → ℕ) (S : Finset α) : Prop :=
  ∀ u v, (∀ s ∈ S, d s u = d s v) → u = v

instance (d : α → α → ℕ) (S : Finset α) : Decidable (Resolves d S) := by
  unfold Resolves; infer_instance

/-- [definition] `k` is the metric dimension: some `k` vertices resolve, and no fewer do. -/
def IsMetricDimension (d : α → α → ℕ) (k : ℕ) : Prop :=
  (∃ S : Finset α, S.card = k ∧ Resolves d S) ∧ ∀ S : Finset α, S.card < k → ¬ Resolves d S

omit [Fintype α] [DecidableEq α] in
/-- [proved-derived; formal-checked] A superset of a resolving set resolves. -/
theorem Resolves.mono {d : α → α → ℕ} {S T : Finset α} (hS : Resolves d S) (hST : S ⊆ T) :
    Resolves d T :=
  fun u v h => hS u v fun s hs => h s (hST hs)

omit [Fintype α] in
/-- [proved-derived; formal-checked] Every set of fewer than three vertices lies in a pair. -/
theorem subset_pair_of_card_lt_three [Nonempty α] (T : Finset α) (hT : T.card < 3) :
    ∃ a b, T ⊆ {a, b} := by
  obtain ⟨a₀⟩ := ‹Nonempty α›
  interval_cases h : T.card
  · rw [Finset.card_eq_zero] at h
    exact ⟨a₀, a₀, by simp [h]⟩
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h
    exact ⟨a, a, by simp⟩
  · obtain ⟨a, b, -, rfl⟩ := Finset.card_eq_two.mp h
    exact ⟨a, b, le_rfl⟩

omit [Fintype α] in
/-- [proved-derived; formal-checked] Metric dimension two from a resolving pair and the refusal
of every single vertex. -/
theorem isMetricDimension_two [Nonempty α] (d : α → α → ℕ) (S : Finset α) (hS : S.card = 2)
    (hres : Resolves d S) (hone : ∀ a, ¬ Resolves d {a}) : IsMetricDimension d 2 := by
  refine ⟨⟨S, hS, hres⟩, fun T hT hTres => ?_⟩
  obtain ⟨a, b, hab⟩ := subset_pair_of_card_lt_three T (by omega)
  interval_cases h : T.card
  · obtain ⟨a₀⟩ := ‹Nonempty α›
    rw [Finset.card_eq_zero] at h
    exact hone a₀ (hTres.mono (by simp [h]))
  · obtain ⟨c, rfl⟩ := Finset.card_eq_one.mp h
    exact hone c hTres

omit [Fintype α] in
/-- [proved-derived; formal-checked] Metric dimension three from a resolving triple and the
refusal of every pair. -/
theorem isMetricDimension_three [Nonempty α] (d : α → α → ℕ) (S : Finset α) (hS : S.card = 3)
    (hres : Resolves d S) (htwo : ∀ a b, ¬ Resolves d {a, b}) : IsMetricDimension d 3 := by
  refine ⟨⟨S, hS, hres⟩, fun T hT hTres => ?_⟩
  obtain ⟨a, b, hab⟩ := subset_pair_of_card_lt_three T hT
  exact htwo a b (hTres.mono hab)

omit [Fintype α] [DecidableEq α] in
/-- [proved-derived; formal-checked] Metric dimension one from a resolving vertex on two or more
vertices. -/
theorem isMetricDimension_one (d : α → α → ℕ) (a : α) (hres : Resolves d {a})
    (hzero : ¬ Resolves d ∅) : IsMetricDimension d 1 := by
  refine ⟨⟨{a}, rfl, hres⟩, fun T hT hTres => hzero ?_⟩
  have : T = ∅ := Finset.card_eq_zero.mp (by omega)
  rwa [this] at hTres

/-- [definition] A distance satisfies the **Bellman equation** of an adjacency: zero on the
diagonal, and off it one more than the least neighbour's distance. -/
def IsBellmanDistance (adj : α → α → Bool) (d : α → α → ℕ) : Prop :=
  ∀ u v, (u = v → d u v = 0) ∧
    (u ≠ v → (∃ w, adj u w = true ∧ d w v + 1 = d u v) ∧ ∀ w, adj u w = true → d u v ≤ d w v + 1)

instance (adj : α → α → Bool) (d : α → α → ℕ) : Decidable (IsBellmanDistance adj d) := by
  unfold IsBellmanDistance; infer_instance

omit [Fintype α] in
/-- [proved-derived; formal-checked] **A Bellman distance is unique**: two solutions of the same
adjacency's Bellman equation are equal, so a table that satisfies it is the graph distance. -/
theorem bellman_unique {adj : α → α → Bool} {d d' : α → α → ℕ}
    (h : IsBellmanDistance adj d) (h' : IsBellmanDistance adj d') : d = d' := by
  have key : ∀ {d d' : α → α → ℕ}, IsBellmanDistance adj d → IsBellmanDistance adj d' →
      ∀ k u v, d u v = k → d' u v ≤ d u v := by
    intro d d' h h' k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro u v hk
      by_cases huv : u = v
      · rw [(h' u v).1 huv]; exact Nat.zero_le _
      · obtain ⟨⟨w, hw, hdw⟩, -⟩ := (h u v).2 huv
        have hlt : d w v < k := by omega
        have := ih (d w v) hlt w v rfl
        have := ((h' u v).2 huv).2 w hw
        omega
  funext u v
  exact le_antisymm (key h' h _ u v rfl) (key h h' _ u v rfl)

/-- [definition] `|a − b|` on the naturals. -/
def absDiff (a b : ℕ) : ℕ := a - b + (b - a)

/-- [definition] A path's adjacency. -/
def pathAdj {k : ℕ} (i j : Fin k) : Bool := i.val + 1 = j.val || j.val + 1 = i.val

/-- [definition] A path's distance. -/
def pathDist {k : ℕ} (i j : Fin k) : ℕ := absDiff i.val j.val

/-- [definition] A ring's adjacency. -/
def cycleAdj {k : ℕ} (i j : Fin k) : Bool := (i.val + 1) % k = j.val || (j.val + 1) % k = i.val

/-- [definition] A ring's distance. -/
def cycleDist {k : ℕ} (i j : Fin k) : ℕ := min (absDiff i.val j.val) (k - absDiff i.val j.val)

/-- [definition] The box product's adjacency: a step in one factor with the other held. -/
def boxAdj {β γ : Type*} [DecidableEq β] [DecidableEq γ] (a : β → β → Bool) (b : γ → γ → Bool)
    (u v : β × γ) : Bool :=
  (decide (u.1 = v.1) && b u.2 v.2) || (decide (u.2 = v.2) && a u.1 v.1)

/-- [definition] The box product's distance: the sum of the factors'. -/
def boxDist {β γ : Type*} (a : β → β → ℕ) (b : γ → γ → ℕ) (u v : β × γ) : ℕ :=
  a u.1 v.1 + b u.2 v.2

/-- [definition] The star `K_(1,3)`, centre `0`. -/
def starAdj (i j : Fin 4) : Bool := (i = 0 && j ≠ 0) || (j = 0 && i ≠ 0)

/-- [definition] The star's distance. -/
def starDist (i j : Fin 4) : ℕ := if i = j then 0 else if i = 0 ∨ j = 0 then 1 else 2

/-- [proved-derived; formal-checked] **`P₃` needs one landmark**: an end resolves the path. -/
theorem path3_metricDimension :
    IsBellmanDistance (pathAdj (k := 3)) pathDist ∧ IsMetricDimension (pathDist (k := 3)) 1 :=
  ⟨by decide +kernel, isMetricDimension_one _ 0 (by decide +kernel) (by decide +kernel)⟩

/-- [proved-derived; formal-checked] **`K_(1,3)` needs two**, though it is a contractible tree as
`P₃` is: there is no topological law behind the count. -/
theorem star_metricDimension :
    IsBellmanDistance starAdj starDist ∧ IsMetricDimension starDist 2 :=
  ⟨by decide +kernel, isMetricDimension_two _ {1, 2} rfl (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 200000 in
/-- [proved-derived; formal-checked] **The grid `P₄ □ P₄` needs two**: two adjacent corners. -/
theorem grid44_metricDimension :
    IsBellmanDistance (boxAdj (pathAdj (k := 4)) (pathAdj (k := 4)))
        (boxDist pathDist pathDist) ∧
      IsMetricDimension (boxDist (pathDist (k := 4)) (pathDist (k := 4))) 2 :=
  ⟨by decide +kernel, isMetricDimension_two _ {(0, 0), (0, 3)} rfl (by decide +kernel)
    (by decide +kernel)⟩

set_option maxRecDepth 200000 in
/-- [proved-derived; formal-checked] **The prism `C₅ □ P₂` needs two.** -/
theorem prism5_metricDimension :
    IsBellmanDistance (boxAdj (cycleAdj (k := 5)) (pathAdj (k := 2)))
        (boxDist cycleDist pathDist) ∧
      IsMetricDimension (boxDist (cycleDist (k := 5)) (pathDist (k := 2))) 2 :=
  ⟨by decide +kernel, isMetricDimension_two _ {(0, 0), (2, 0)} rfl (by decide +kernel)
    (by decide +kernel)⟩

set_option maxRecDepth 200000 in
/-- [proved-derived; formal-checked] **The prism `C₆ □ P₂` needs three**: an even ring costs one
more landmark. -/
theorem prism6_metricDimension :
    IsBellmanDistance (boxAdj (cycleAdj (k := 6)) (pathAdj (k := 2)))
        (boxDist cycleDist pathDist) ∧
      IsMetricDimension (boxDist (cycleDist (k := 6)) (pathDist (k := 2))) 3 :=
  ⟨by decide +kernel, isMetricDimension_three _ {(0, 0), (1, 0), (0, 1)} rfl
    (by decide +kernel) (by decide +kernel)⟩

set_option maxRecDepth 200000 in
/-- [proved-derived; formal-checked] **The prism `C₇ □ P₂` needs two**, as an odd ring does. -/
theorem prism7_metricDimension :
    IsBellmanDistance (boxAdj (cycleAdj (k := 7)) (pathAdj (k := 2)))
        (boxDist cycleDist pathDist) ∧
      IsMetricDimension (boxDist (cycleDist (k := 7)) (pathDist (k := 2))) 2 :=
  ⟨by decide +kernel, isMetricDimension_two _ {(0, 0), (3, 0)} rfl (by decide +kernel)
    (by decide +kernel)⟩

set_option maxRecDepth 200000 in
/-- [proved-derived; formal-checked] **The torus `C₃ □ C₄` needs three**, a ring being odd. -/
theorem torus34_metricDimension :
    IsBellmanDistance (boxAdj (cycleAdj (k := 3)) (cycleAdj (k := 4)))
        (boxDist cycleDist cycleDist) ∧
      IsMetricDimension (boxDist (cycleDist (k := 3)) (cycleDist (k := 4))) 3 :=
  ⟨by decide +kernel, isMetricDimension_three _ {(0, 0), (0, 1), (1, 0)} rfl
    (by decide +kernel) (by decide +kernel)⟩

end MetricDimension

end Holonics.Holon.LoopCurvature
