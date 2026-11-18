import Mathlib
import HolonicsResearch.Hodge.HodgeEllipticProduct

/-!
# The integral Hodge statement in degree two on a product of `n` tori of dimension one

**[definition]** The chart.  Tori `Eᵢ = ℂ/(ℤ + ℤτᵢ)` indexed by a finite linearly ordered `ι`, and
their product `∏ Eᵢ`, whose first homology is the lattice `Λ = ⊕ᵢ (ℤ + ℤτᵢ)` with basis
`e_{i,0} ↦ 1`, `e_{i,1} ↦ τᵢ`.  A class of degree two is an alternating integer form on `Λ`
(`Form`, `IsAlt`).  Its pairing with `dzᵢ ∧ dzⱼ` is `periodForm τ c i j` up to conjugation, and the
class is of type `(1, 1)` when every such pairing vanishes (`IsHodge`); `evalC_holVec` and
`isHodge_iff_evalC` show this is the vanishing of the class on every pair of holomorphic vectors
`vᵢ = −conj(τᵢ)·e_{i,0} + e_{i,1}`.  The block `(i, j)` of a form is read as a lattice map
`Λᵢ → Λⱼ` (`blockMap`, the `LatticeMap` of `Hodge/HodgeEllipticProduct`); `fibreForm i` is the
class of `{pt} × ∏_{k ≠ i} E_k`, and `homForm i j M` the class of a lattice map in the block
`(i, j)`.

**[proved-derived; formal-checked]** What is proved.

1. **E1, type `(1, 1)` is read block by block** (`periodForm_eq_zero_iff`, `periodForm_self`,
   `periodForm_swap`, `isHodge_iff_blocks`): an alternating form is of type `(1, 1)` if and only if
   each block above the diagonal is a homomorphism `Eᵢ → Eⱼ` (multiplication by one complex number,
   `IsHolomorphic` of `Hodge/HodgeEllipticProduct`).  The diagonal blocks impose nothing.
2. **The cycle is written** (`assemble`, `assemble_blockMap`, `assemble_eq_sum`,
   `eq_sum_of_isAlt`, `sum_decomposition_unique`): every alternating integer form is, in exactly
   one way, `∑ᵢ c(e_{i,0}, e_{i,1})·[fibre i] + ∑_{i<j} [homForm i j (blockMap c i j)]`.
3. **E2, the integral Hodge statement in degree two** (`isHodge_homForm_iff`,
   `isHodge_fibreForm`, `isHodge_iff_combination`): an alternating integer form is of type `(1, 1)`
   if and only if it is an integer combination of the fibre classes and of the classes of
   homomorphisms `Eᵢ → Eⱼ`, `i < j`.  No rational coefficient enters, and nothing depends on `n`
   but the count of pairs.

**Reading.**  [interpretation] `agent-inferred`.  On a product of tori the classes of type `(1, 1)`
in degree two are made of what two factors share: a homomorphism between them, a pair contact
that carries one lattice into another as one complex multiplier.  The whole product adds no new
kind of class in this degree; each class is a sum over pairs, the two-torus statement of
`Hodge/HodgeEllipticProduct` applied block by block.  In higher degree (the classes of type
`(k, k)` on `Eⁿ`, whose count is the Narayana row of the record of November 18) products of these
divisors are needed, and this file does not reach them.

**What this does not state.**  The chart is the lattice's: that the second cohomology of the
product is the alternating forms on `Λ`, that type `(1, 1)` is the vanishing on pairs of
holomorphic vectors, and that `fibreForm` and `homForm` of a homomorphism are classes of divisors
(the fibre, and the pullback of a graph's class) are the standard identifications and are not
formalized.  Granted these, E2 is Lefschetz's theorem on `(1, 1)` classes for `∏ Eᵢ` with the
divisors written.  Classes of degree above two, the intersection form and the index theorem on the
product are not stated here.

**Computational object.**  The helical pair interaction: a block is a pair contact between two
factors, and type `(1, 1)` asks that the contact be one complex multiplier.  Of the winding
guide's six objects: the pair (the block), cell holonomy (the period that must vanish around the
two factors' cycles) and the tower thread (the product as a transverse gluing of its factors).

**Consumers.**  The atlas row `hodge.torus-power-divisors`, beside `hodge.torus-power-narayana`.

Source record: `research/records/2026-11-18_AN_ABELIAN_COVER_FACTORS_THROUGH_ITS_CHARACTERS_A_TEMPERED_COMPLEX_MIXES_AT_ITS_HALF_THE_FLUIDS_TRIADS_DO_NO_WORK_SO_EVERY_TRUNCATION_FLOWS_FOR_ALL_TIME_AND_HARD_LEFSCHETZ_IS_A_POSITIVE_COMMUTATOR.md` (§8).

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Hodge.EllipticProduct.LatticeMap

/-! ## Lattice maps add -/

instance : Add LatticeMap := ⟨fun M N => ⟨M.p + N.p, M.r + N.r, M.s + N.s, M.t + N.t⟩⟩

instance : Neg LatticeMap := ⟨fun M => ⟨-M.p, -M.r, -M.s, -M.t⟩⟩

@[simp] theorem add_p (M N : LatticeMap) : (M + N).p = M.p + N.p := rfl
@[simp] theorem add_r (M N : LatticeMap) : (M + N).r = M.r + N.r := rfl
@[simp] theorem add_s (M N : LatticeMap) : (M + N).s = M.s + N.s := rfl
@[simp] theorem add_t (M N : LatticeMap) : (M + N).t = M.t + N.t := rfl
@[simp] theorem neg_p (M : LatticeMap) : (-M).p = -M.p := rfl
@[simp] theorem neg_r (M : LatticeMap) : (-M).r = -M.r := rfl
@[simp] theorem neg_s (M : LatticeMap) : (-M).s = -M.s := rfl
@[simp] theorem neg_t (M : LatticeMap) : (-M).t = -M.t := rfl

/-- [definition] Lattice maps `ℤ + ℤτ → ℤ + ℤτ'` form an additive group, coordinate by
coordinate. -/
instance : AddCommGroup LatticeMap where
  add := (· + ·)
  zero := 0
  neg := Neg.neg
  add_assoc M N K := by ext <;> simp [add_assoc]
  zero_add M := by ext <;> simp
  add_zero M := by ext <;> simp
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel M := by ext <;> simp
  add_comm M N := by ext <;> simp [add_comm]

end Holonics.Hodge.EllipticProduct.LatticeMap

namespace Holonics.Hodge.EllipticPower

open Complex Holonics.Hodge.EllipticProduct

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-! ## The chart -/

/-- [definition] An integer bilinear form on the lattice `Λ = ⊕ᵢ (ℤ + ℤτᵢ)`, by its matrix in the
basis `e_{i,0} ↦ 1`, `e_{i,1} ↦ τᵢ` of the `i`-th factor. -/
abbrev Form (ι : Type*) : Type _ := Matrix (ι × Fin 2) (ι × Fin 2) ℤ

/-- [definition] The form is alternating: a class in the second cohomology of the product. -/
def IsAlt (c : Form ι) : Prop := ∀ x y, c x y = -c y x

omit [Fintype ι] [LinearOrder ι] in
theorem IsAlt.diag {c : Form ι} (hc : IsAlt c) (x : ι × Fin 2) : c x x = 0 := by
  have := hc x x
  omega

/-- [definition] The pairing of a class with the holomorphic two-form `dzᵢ ∧ dzⱼ`, up to
conjugation: the value of the form on the holomorphic vectors `vᵢ, vⱼ`, conjugated
(`evalC_holVec`). -/
def periodForm (τ : ι → ℂ) (c : Form ι) (i j : ι) : ℂ :=
  c (i, 1) (j, 1) - τ i * c (i, 0) (j, 1) - τ j * c (i, 1) (j, 0) + τ i * τ j * c (i, 0) (j, 0)

/-- [definition] A class of type `(1, 1)`: every holomorphic two-form `dzᵢ ∧ dzⱼ` pairs to zero
with it. -/
def IsHodge (τ : ι → ℂ) (c : Form ι) : Prop := ∀ i j, periodForm τ c i j = 0

/-- [definition] The lattice map `Λᵢ → Λⱼ` read off the block `(i, j)` of a form: the block is
`ω(M ·, ·)` for the standard form `ω` on `Λⱼ` (`blk_blockMap`). -/
def blockMap (c : Form ι) (i j : ι) : LatticeMap :=
  ⟨c (i, 0) (j, 1), c (i, 1) (j, 1), -c (i, 0) (j, 0), -c (i, 1) (j, 0)⟩

omit [Fintype ι] [LinearOrder ι] in
theorem periodForm_eq (τ : ι → ℂ) (c : Form ι) (i j : ι) :
    periodForm τ c i j =
      (((blockMap c i j).r : ℂ) + (blockMap c i j).t * τ j) -
        τ i * ((blockMap c i j).p + (blockMap c i j).s * τ j) := by
  simp only [periodForm, blockMap]
  push_cast
  ring

omit [Fintype ι] [LinearOrder ι] in
/-- [proved-derived; formal-checked] The block `(i, j)` pairs to zero with `dzᵢ ∧ dzⱼ` precisely
when its lattice map is a homomorphism `Eᵢ → Eⱼ`. -/
theorem periodForm_eq_zero_iff (τ : ι → ℂ) (c : Form ι) (i j : ι) :
    periodForm τ c i j = 0 ↔ IsHolomorphic (τ i) (τ j) (blockMap c i j) := by
  rw [periodForm_eq, sub_eq_zero]
  rfl

omit [Fintype ι] [LinearOrder ι] in
theorem periodForm_self (τ : ι → ℂ) {c : Form ι} (hc : IsAlt c) (i : ι) :
    periodForm τ c i i = 0 := by
  have h1 := hc.diag (i, 1)
  have h0 := hc.diag (i, 0)
  have h10 := hc (i, 1) (i, 0)
  simp only [periodForm, h1, h0, h10]
  push_cast
  ring

omit [Fintype ι] [LinearOrder ι] in
theorem periodForm_swap (τ : ι → ℂ) {c : Form ι} (hc : IsAlt c) (i j : ι) :
    periodForm τ c j i = -periodForm τ c i j := by
  simp only [periodForm, hc (j, 1) (i, 1), hc (j, 0) (i, 1), hc (j, 1) (i, 0), hc (j, 0) (i, 0)]
  push_cast
  ring

omit [Fintype ι] in
/-- [proved-derived; formal-checked] E1.  An alternating form is of type `(1, 1)` if and only if
each of its blocks above the diagonal is a homomorphism of the two tori it joins. -/
theorem isHodge_iff_blocks (τ : ι → ℂ) {c : Form ι} (hc : IsAlt c) :
    IsHodge τ c ↔ ∀ i j, i < j → IsHolomorphic (τ i) (τ j) (blockMap c i j) := by
  constructor
  · intro h i j _
    exact (periodForm_eq_zero_iff τ c i j).mp (h i j)
  · intro h i j
    rcases lt_trichotomy i j with hij | rfl | hij
    · exact (periodForm_eq_zero_iff τ c i j).mpr (h i j hij)
    · exact periodForm_self τ hc i
    · rw [periodForm_swap τ hc j i, (periodForm_eq_zero_iff τ c j i).mpr (h j i hij), neg_zero]

/-! ## The definition is the vanishing on pairs of holomorphic vectors -/

/-- [definition] The complex bilinear extension of a form. -/
def evalC (c : Form ι) (v w : ι × Fin 2 → ℂ) : ℂ := ∑ a, ∑ b, v a * (c a b : ℂ) * w b

/-- [definition] The holomorphic vector of the `i`-th factor, `vᵢ = −conj(τᵢ)·e_{i,0} + e_{i,1}`:
the vector of `Λᵢ ⊗ ℂ` on which the conjugate coordinate `x₀ + x₁·conj τᵢ` vanishes. -/
def holVec (τ : ι → ℂ) (i : ι) : ι × Fin 2 → ℂ := fun x =>
  if x.1 = i then ![-(starRingEnd ℂ) (τ i), 1] x.2 else 0

theorem sum_single_fst (i : ι) (g : Fin 2 → ℂ) (f : ι × Fin 2 → ℂ) :
    ∑ a : ι × Fin 2, (if a.1 = i then g a.2 else 0) * f a = ∑ e, g e * f (i, e) := by
  rw [Fintype.sum_prod_type, Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- [proved-derived; formal-checked] The value of a class on two holomorphic vectors is the
conjugate of `periodForm`: type `(1, 1)` is the vanishing of the class on every pair of
holomorphic vectors. -/
theorem evalC_holVec (τ : ι → ℂ) (c : Form ι) (i j : ι) :
    evalC c (holVec τ i) (holVec τ j) = (starRingEnd ℂ) (periodForm τ c i j) := by
  have h1 : ∀ a : ι × Fin 2, ∑ b, holVec τ i a * (c a b : ℂ) * holVec τ j b
      = holVec τ i a * ∑ f, ![-(starRingEnd ℂ) (τ j), 1] f * (c a (j, f) : ℂ) := by
    intro a
    have hb : ∀ b : ι × Fin 2, holVec τ i a * (c a b : ℂ) * holVec τ j b =
        (if b.1 = j then ![-(starRingEnd ℂ) (τ j), 1] b.2 else 0) *
          (holVec τ i a * (c a b : ℂ)) := by
      intro b
      simp only [holVec]
      ring
    rw [Finset.sum_congr rfl fun b _ => hb b,
      sum_single_fst j (![-(starRingEnd ℂ) (τ j), 1]) (fun b => holVec τ i a * (c a b : ℂ)),
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    ring
  simp only [evalC, h1]
  have h2 : ∀ a : ι × Fin 2, holVec τ i a *
      ∑ f, ![-(starRingEnd ℂ) (τ j), 1] f * (c a (j, f) : ℂ) =
      (if a.1 = i then ![-(starRingEnd ℂ) (τ i), 1] a.2 else 0) *
        ∑ f, ![-(starRingEnd ℂ) (τ j), 1] f * (c a (j, f) : ℂ) := fun a => rfl
  rw [Finset.sum_congr rfl fun a _ => h2 a, sum_single_fst i]
  simp only [Fin.sum_univ_two, periodForm, map_add, map_sub, map_mul, map_intCast]
  simp
  ring

theorem isHodge_iff_evalC (τ : ι → ℂ) (c : Form ι) :
    IsHodge τ c ↔ ∀ i j, evalC c (holVec τ i) (holVec τ j) = 0 := by
  unfold IsHodge
  refine forall_congr' fun i => forall_congr' fun j => ?_
  rw [evalC_holVec]
  simp

/-! ## The cycles: fibres and homomorphisms -/

/-- [definition] The standard alternating form of a rank-two lattice, `ω(e₀, e₁) = 1`: the class
of a point of the torus. -/
def omega : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; -1, 0]

/-- [definition] The matrix of `(x, y) ↦ ω(M x, y)`, the pullback of `ω` along a lattice map in
its first slot. -/
def blk (M : LatticeMap) : Matrix (Fin 2) (Fin 2) ℤ := !![-M.s, M.p; -M.t, M.r]

theorem omega_swap (e f : Fin 2) : omega e f = -omega f e := by
  fin_cases e <;> fin_cases f <;> simp [omega]

/-- [definition] The pullback of the point class of `Eᵢ` along the projection: the class of
`{pt} × ∏_{k ≠ i} E_k`. -/
def fibreForm (i : ι) : Form ι := fun x y => if x.1 = i ∧ y.1 = i then omega x.2 y.2 else 0

/-- [definition] The class of a lattice map `M : Λᵢ → Λⱼ`: the alternating form whose block
`(i, j)` is `ω(M ·, ·)`, its block `(j, i)` the negative transpose, zero elsewhere.  For a
homomorphism it is, in the standard identification of the lattice chart with the cohomology, the
class of the divisor that the graph of the homomorphism pulls back to `∏ E_k`, less its two fibre
parts (that identification is not formalized here). -/
def homForm (i j : ι) (M : LatticeMap) : Form ι := fun x y =>
  if x.1 = i ∧ y.1 = j then blk M x.2 y.2
  else if x.1 = j ∧ y.1 = i then -blk M y.2 x.2 else 0

/-- [definition] The pairs `i < j` of factors. -/
abbrev Pair (ι : Type*) [LinearOrder ι] : Type _ := {p : ι × ι // p.1 < p.2}

/-- [definition] The form with fibre coefficients `a` and the lattice maps `M i j` (`i < j`) in
its blocks. -/
def assemble (a : ι → ℤ) (M : ι → ι → LatticeMap) : Form ι := fun x y =>
  if x.1 = y.1 then a x.1 * omega x.2 y.2
  else if x.1 < y.1 then blk (M x.1 y.1) x.2 y.2
  else -blk (M y.1 x.1) y.2 x.2

/-- [definition] A family of lattice maps on the pairs `i < j`, extended by zero. -/
def extend (M : Pair ι → LatticeMap) : ι → ι → LatticeMap := fun i j =>
  if h : i < j then M ⟨(i, j), h⟩ else 0

omit [Fintype ι] in
theorem extend_of_lt (M : Pair ι → LatticeMap) {i j : ι} (h : i < j) :
    extend M i j = M ⟨(i, j), h⟩ := dif_pos h

omit [Fintype ι] [LinearOrder ι] in
theorem blk_blockMap (c : Form ι) (i j : ι) (e f : Fin 2) :
    blk (blockMap c i j) e f = c (i, e) (j, f) := by
  fin_cases e <;> fin_cases f <;> simp [blk, blockMap]

omit [Fintype ι] in
theorem isAlt_fibreForm (i : ι) : IsAlt (fibreForm i) := by
  intro x y
  simp only [fibreForm]
  by_cases h : x.1 = i ∧ y.1 = i
  · rw [if_pos h, if_pos ⟨h.2, h.1⟩, omega_swap]
  · rw [if_neg h, if_neg (fun h' => h ⟨h'.2, h'.1⟩), neg_zero]

omit [Fintype ι] in
theorem isAlt_homForm {i j : ι} (hij : i ≠ j) (M : LatticeMap) : IsAlt (homForm i j M) := by
  intro x y
  simp only [homForm]
  by_cases h1 : x.1 = i ∧ y.1 = j
  · have h2 : ¬(y.1 = i ∧ x.1 = j) := fun h => hij (h1.1.symm.trans h.2)
    rw [if_pos h1, if_neg h2, if_pos ⟨h1.2, h1.1⟩, neg_neg]
  · by_cases h2 : x.1 = j ∧ y.1 = i
    · rw [if_neg h1, if_pos h2, if_pos ⟨h2.2, h2.1⟩]
    · rw [if_neg h1, if_neg h2, if_neg (fun h => h2 ⟨h.2, h.1⟩), if_neg (fun h => h1 ⟨h.2, h.1⟩),
        neg_zero]

omit [Fintype ι] in
theorem isAlt_assemble (a : ι → ℤ) (M : ι → ι → LatticeMap) : IsAlt (assemble a M) := by
  intro x y
  simp only [assemble]
  rcases lt_trichotomy x.1 y.1 with h | h | h
  · rw [if_neg h.ne, if_pos h, if_neg h.ne', if_neg (not_lt.mpr h.le), neg_neg]
  · rw [if_pos h, if_pos h.symm, omega_swap, h]
    ring
  · rw [if_neg h.ne', if_neg (not_lt.mpr h.le), if_neg h.ne, if_pos h]

omit [Fintype ι] in
theorem assemble_congr (a : ι → ℤ) {M M' : ι → ι → LatticeMap}
    (h : ∀ i j, i < j → M i j = M' i j) : assemble a M = assemble a M' := by
  funext x y
  simp only [assemble]
  rcases lt_trichotomy x.1 y.1 with hxy | hxy | hxy
  · rw [if_neg hxy.ne, if_pos hxy, if_neg hxy.ne, if_pos hxy, h _ _ hxy]
  · rw [if_pos hxy, if_pos hxy]
  · rw [if_neg hxy.ne', if_neg (not_lt.mpr hxy.le), if_neg hxy.ne', if_neg (not_lt.mpr hxy.le),
      h _ _ hxy]

omit [Fintype ι] in
theorem diag_assemble (a : ι → ℤ) (M : ι → ι → LatticeMap) (i : ι) :
    assemble a M (i, 0) (i, 1) = a i := by
  simp [assemble, omega]

omit [Fintype ι] in
theorem blockMap_assemble (a : ι → ℤ) (M : ι → ι → LatticeMap) {i j : ι} (hij : i < j) :
    blockMap (assemble a M) i j = M i j := by
  ext <;> simp [blockMap, assemble, hij.ne, hij, blk]

omit [Fintype ι] in
/-- [proved-derived; formal-checked] Every alternating form is assembled from its fibre
coefficients `c(e_{i,0}, e_{i,1})` and its block maps. -/
theorem assemble_blockMap {c : Form ι} (hc : IsAlt c) :
    assemble (fun i => c (i, 0) (i, 1)) (blockMap c) = c := by
  funext x y
  obtain ⟨i, e⟩ := x
  obtain ⟨j, f⟩ := y
  simp only [assemble]
  rcases lt_trichotomy i j with h | h | h
  · rw [if_neg h.ne, if_pos h, blk_blockMap]
  · subst h
    rw [if_pos rfl]
    have h00 := hc.diag (i, 0)
    have h11 := hc.diag (i, 1)
    have h10 := hc (i, 1) (i, 0)
    fin_cases e <;> fin_cases f <;> simp [omega, h00, h11, h10]
  · rw [if_neg h.ne', if_neg (not_lt.mpr h.le), blk_blockMap, hc (i, e) (j, f)]

theorem isHolomorphic_zero (τ τ' : ℂ) : IsHolomorphic τ τ' 0 := by
  simp [IsHolomorphic]

omit [Fintype ι] in
theorem isHodge_fibreForm (τ : ι → ℂ) (k : ι) : IsHodge τ (fibreForm k) := by
  intro i j
  simp only [periodForm, fibreForm]
  by_cases h : i = k ∧ j = k
  · obtain ⟨rfl, rfl⟩ := h
    simp [omega]
  · simp [h]

omit [Fintype ι] in
theorem blockMap_homForm_self {i j : ι} (_hij : i ≠ j) (M : LatticeMap) :
    blockMap (homForm i j M) i j = M := by
  ext <;> simp [blockMap, homForm, blk]

omit [Fintype ι] in
theorem blockMap_homForm_of_ne {i j : ι} (hij : i < j) (M : LatticeMap) {k l : ι} (hkl : k < l)
    (hne : (k, l) ≠ (i, j)) : blockMap (homForm i j M) k l = 0 := by
  have h1 : ¬(k = i ∧ l = j) := fun h => hne (by rw [h.1, h.2])
  have h2 : ¬(k = j ∧ l = i) := fun h => by
    rw [h.1, h.2] at hkl
    exact absurd hkl (not_lt.mpr hij.le)
  ext <;> simp [blockMap, homForm, h1, h2]

omit [Fintype ι] in
/-- [proved-derived; formal-checked] The class of a lattice map `Λᵢ → Λⱼ` is of type `(1, 1)`
precisely when the map is a homomorphism of the tori. -/
theorem isHodge_homForm_iff (τ : ι → ℂ) {i j : ι} (hij : i < j) (M : LatticeMap) :
    IsHodge τ (homForm i j M) ↔ IsHolomorphic (τ i) (τ j) M := by
  rw [isHodge_iff_blocks τ (isAlt_homForm hij.ne M)]
  constructor
  · intro h
    have := h i j hij
    rwa [blockMap_homForm_self hij.ne] at this
  · intro h k l hkl
    by_cases hne : (k, l) = (i, j)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hne
      rwa [blockMap_homForm_self hij.ne]
    · rw [blockMap_homForm_of_ne hij M hkl hne]
      exact isHolomorphic_zero _ _

/-- [proved-derived; formal-checked] The assembled form is the integer combination of the fibre
classes and the classes of its lattice maps. -/
theorem assemble_eq_sum (a : ι → ℤ) (M : Pair ι → LatticeMap) :
    assemble a (extend M) =
      ∑ i, a i • fibreForm i + ∑ p : Pair ι, homForm p.1.1 p.1.2 (M p) := by
  funext x y
  obtain ⟨i, e⟩ := x
  obtain ⟨j, f⟩ := y
  rw [Matrix.add_apply, Matrix.sum_apply, Matrix.sum_apply]
  have h1 : ∑ k, (a k • fibreForm k) (i, e) (j, f) = if i = j then a i * omega e f else 0 := by
    rw [Finset.sum_eq_single i]
    · by_cases h : i = j
      · simp [fibreForm, h]
      · simp [fibreForm, h, Ne.symm h]
    · intro k _ hk
      simp [fibreForm, Ne.symm hk]
    · intro h
      exact absurd (Finset.mem_univ i) h
  rw [h1]
  simp only [assemble]
  rcases lt_trichotomy i j with h | h | h
  · rw [if_neg h.ne, if_pos h, if_neg h.ne, zero_add, extend_of_lt M h,
      Finset.sum_eq_single (⟨(i, j), h⟩ : Pair ι)]
    · simp [homForm]
    · rintro ⟨⟨k, l⟩, hkl⟩ _ hne
      have hkl' : k < l := hkl
      have h1 : ¬(i = k ∧ j = l) := fun h' => hne (by
        apply Subtype.ext
        simp [h'.1, h'.2])
      have h2 : ¬(i = l ∧ j = k) := fun h' => by
        rw [h'.1, h'.2] at h
        exact absurd h (not_lt.mpr hkl'.le)
      simp [homForm, h1, h2]
    · intro h'
      exact absurd (Finset.mem_univ _) h'
  · subst h
    rw [if_pos rfl, if_pos rfl, Finset.sum_eq_zero, add_zero]
    rintro ⟨⟨k, l⟩, hkl⟩ _
    have hkl' : k < l := hkl
    have h1 : ¬(i = k ∧ i = l) := fun h' => hkl'.ne (h'.1.symm.trans h'.2)
    have h2 : ¬(i = l ∧ i = k) := fun h' => hkl'.ne (h'.2.symm.trans h'.1)
    simp [homForm, h1, h2]
  · rw [if_neg h.ne', if_neg (not_lt.mpr h.le), if_neg h.ne', zero_add, extend_of_lt M h,
      Finset.sum_eq_single (⟨(j, i), h⟩ : Pair ι)]
    · simp [homForm, h.ne']
    · rintro ⟨⟨k, l⟩, hkl⟩ _ hne
      have hkl' : k < l := hkl
      have h1 : ¬(i = k ∧ j = l) := fun h' => by
        rw [h'.1, h'.2] at h
        exact absurd h (not_lt.mpr hkl'.le)
      have h2 : ¬(i = l ∧ j = k) := fun h' => hne (by
        apply Subtype.ext
        simp [h'.1, h'.2])
      simp [homForm, h1, h2]
    · intro h'
      exact absurd (Finset.mem_univ _) h'

/-- [proved-derived; formal-checked] E2, the cycle is written.  Every alternating integer form is
the integer combination of the fibre classes, with coefficients `c(e_{i,0}, e_{i,1})`, and of the
classes of its block maps. -/
theorem eq_sum_of_isAlt {c : Form ι} (hc : IsAlt c) :
    c = ∑ i, c (i, 0) (i, 1) • fibreForm i +
      ∑ p : Pair ι, homForm p.1.1 p.1.2 (blockMap c p.1.1 p.1.2) := by
  rw [← assemble_eq_sum]
  conv_lhs => rw [← assemble_blockMap hc]
  exact assemble_congr _ fun i j hij =>
    (extend_of_lt (fun p : Pair ι => blockMap c p.1.1 p.1.2) hij).symm

/-- [proved-derived; formal-checked] A decomposition along fibres and lattice maps determines its
coefficients and its maps. -/
theorem sum_decomposition_unique {c : Form ι} {a : ι → ℤ} {M : Pair ι → LatticeMap}
    (h : c = ∑ i, a i • fibreForm i + ∑ p : Pair ι, homForm p.1.1 p.1.2 (M p)) :
    (∀ i, a i = c (i, 0) (i, 1)) ∧ ∀ p : Pair ι, M p = blockMap c p.1.1 p.1.2 := by
  rw [← assemble_eq_sum] at h
  subst h
  refine ⟨fun i => (diag_assemble _ _ i).symm, ?_⟩
  rintro ⟨⟨i, j⟩, hij⟩
  have hij' : i < j := hij
  rw [blockMap_assemble _ _ hij', extend_of_lt M hij']

/-- [proved-derived; formal-checked] E2, the integral Hodge statement in degree two, in the lattice
chart: an alternating integer form on the lattice of `∏ Eᵢ` is of type `(1, 1)` if and only if it
is an integer combination of the fibre classes and of the classes of homomorphisms `Eᵢ → Eⱼ`,
`i < j`.  No rational coefficient enters. -/
theorem isHodge_iff_combination (τ : ι → ℂ) {c : Form ι} (hc : IsAlt c) :
    IsHodge τ c ↔ ∃ (a : ι → ℤ) (M : Pair ι → LatticeMap),
      (∀ p : Pair ι, IsHolomorphic (τ p.1.1) (τ p.1.2) (M p)) ∧
        c = ∑ i, a i • fibreForm i + ∑ p : Pair ι, homForm p.1.1 p.1.2 (M p) := by
  rw [isHodge_iff_blocks τ hc]
  constructor
  · intro h
    exact ⟨fun i => c (i, 0) (i, 1), fun p => blockMap c p.1.1 p.1.2, fun p => h _ _ p.2,
      eq_sum_of_isAlt hc⟩
  · rintro ⟨a, M, hM, hsum⟩ i j hij
    have := (sum_decomposition_unique hsum).2 ⟨(i, j), hij⟩
    rw [← this]
    exact hM ⟨(i, j), hij⟩

section Audit

#print axioms periodForm_eq_zero_iff
#print axioms isHodge_iff_blocks
#print axioms evalC_holVec
#print axioms isHodge_iff_evalC
#print axioms assemble_blockMap
#print axioms eq_sum_of_isAlt
#print axioms sum_decomposition_unique
#print axioms isHodge_homForm_iff
#print axioms isHodge_fibreForm
#print axioms isHodge_iff_combination

end Audit

end Holonics.Hodge.EllipticPower
