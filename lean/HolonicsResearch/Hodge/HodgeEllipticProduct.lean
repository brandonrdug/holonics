import Mathlib

/-!
# The integral Hodge statement on a product of two tori of dimension one, in the lattice chart

**[definition]** The chart.  `E = ℂ/(ℤ + ℤτ)` and `E' = ℂ/(ℤ + ℤτ')`.  The first homology of
`E × E'` is `ℤ⁴`, with basis `e₁, e₂` (the periods `1, τ` of `dz`) and `e₃, e₄` (the periods
`1, τ'` of `dz'`).  The second homology is `Λ²ℤ⁴`, held here as `Class2 = Fin 6 → ℤ` in the
coordinates `(c12, c13, c14, c23, c24, c34)` at the indices `0, …, 5`; `wedge x y` is the class of
the parallelogram on `x, y`, its six `2 × 2` minors.

* `period τ τ' c = c13 + c14·τ' + c23·τ + c24·τ·τ'` is the pairing of `c` with `dz ∧ dz'`, the one
  holomorphic two-form of the product (`period_wedge`: on `wedge x y` it is
  `dz x · dz' y − dz y · dz' x`).  A class is of type `(1, 1)` when that pairing vanishes:
  `IsHodge τ τ' c := period τ τ' c = 0`.
* A lattice map `M = (p, r, s, t)` sends `1 ↦ p + sτ'` and `τ ↦ r + tτ'`.  It is a homomorphism of
  the tori when it is multiplication by one complex number: `IsHolomorphic τ τ' M` says
  `r + tτ' = τ·(p + sτ')`, the multiplier being `μ = p + sτ'` (`isHolomorphic_iff_multiplier`).
* `graphClass M = wedge (e₁ + M e₁) (e₂ + M e₂) = (1, r, t, −p, −s, pt − rs)` is the class of the
  graph of `M` (`graphClass_eq_wedge`); `fibreE` and `fibreE'` are the classes of `E × 0` and
  `0 × E'`; `inter` is the wedge `Λ² × Λ² → Λ⁴ ≅ ℤ`, the intersection number
  (`inter_wedge_wedge`: on two parallelograms it is the `4 × 4` determinant of their four sides).

**[proved-derived; formal-checked]** What is proved.

1. **A graph's class is of type `(1, 1)` precisely when its map is holomorphic**
   (`isHodge_graphClass_iff`).
2. **The integral Hodge statement** (`isHodge_iff_graph`, `existsUnique_graph_of_isHodge`): an
   integral class is of type `(1, 1)` if and only if it is
   `graphClass M + (c12 − 1)·[E × 0] + (c34 − det M)·[0 × E']` for a holomorphic `M`, and that `M`
   is unique: it is read off the four mixed coordinates (`mapOf`).  Every integral class of type
   `(1, 1)` is an integer combination of the classes of `E × 0`, `0 × E'` and the graph of a
   homomorphism.  No rational coefficient enters.
3. **Intersections** (`inter_wedge_self`, `inter_graphClass_self`, `inter_graphClass_fibreE'`,
   `inter_graphClass_fibreE`, `inter_mixed_self`): a graph meets itself in `0`, meets `0 × E'`
   once and `E × 0` in `det M` points, and its mixed part `graphClass M − [E × 0] − det M·[0 × E']`
   has self-intersection `−2·det M`.
4. **The index theorem is the positivity of the norm** (`det_mul_im`, `det_eq_normSq`,
   `det_nonneg`, `det_eq_zero_iff`, `inter_negDef_on_mixed_hodge`, `hodge_index`): for a holomorphic
   `M` with multiplier `μ`, `det M · Im τ' = |μ|² · Im τ`, and for `τ' = τ`, `det M = |μ|²`.  So the
   degree `det M` is a norm, it is positive unless `M = 0`, and the intersection form is negative
   definite on the mixed classes of type `(1, 1)` and on every class of type `(1, 1)` orthogonal
   to `[E × 0] + [0 × E']`: the signature `(1, ρ − 1)` of the Hodge index theorem, here with the
   norm of the multiplier as its cause.
5. **The places of complex multiplication** (`τ' = τ`; `isHolomorphic_iff_of_generic`,
   `isHolomorphic_iff_of_cm`, `isHodge_iff_of_generic`, `isHodge_iff_of_cm`): when `τ` satisfies no
   integer quadratic relation the holomorphic maps are the integers `p·1` and the classes of type
   `(1, 1)` are the three-parameter family `(c12, 0, c14, −c14, 0, c34)`; when
   `Aτ² + Bτ + C = 0` with `gcd(A, B, C) = 1` they are `t·1 + k·(B + Aτ)`, one more integer `k`,
   and the classes of type `(1, 1)` are a four-parameter family.  The rank goes from three to four
   at the places a quadratic relation names, and the fourth class is the graph of the
   multiplication by `Aτ`.
6. **When a nonzero homomorphism exists** (`exists_nonzero_holomorphic_iff`): precisely when
   `τ·(p + sτ') = r + tτ'` for integers with `(p, s) ≠ (0, 0)`.

**What this does not state.**  The chart is the lattice's.  Three standard facts carry the chart to
the geometry and are not formalized here: that the second homology of the product is `Λ²` of the
lattice with `inter` its intersection form; that an integral class is of type `(1, 1)` precisely when
the one holomorphic two-form `dz ∧ dz'` pairs to zero with it; and that the graph of a holomorphic
homomorphism is an algebraic curve in the product (Chow's theorem; the product is an abelian
surface).  Granted these, item 2 is the integral Hodge statement for `E × E'`, in codimension one,
which is all of it for a surface; it is Lefschetz's theorem on `(1, 1)` classes in this chart, with
the cycle written.  Nothing here bears on classes of codimension two and up on any variety.

Every `theorem` is discharged and none depends on `sorryAx`.
-/

namespace Holonics.Hodge.EllipticProduct

open Complex

/-! ## The chart -/

/-- [definition] `H₂(E × E', ℤ) = Λ²ℤ⁴` in the coordinates `(c12, c13, c14, c23, c24, c34)`, held
at the indices `0, …, 5`. -/
abbrev Class2 : Type := Fin 6 → ℤ

/-- [definition] The class of the parallelogram on `x, y ∈ ℤ⁴`: its six `2 × 2` minors. -/
def wedge (x y : Fin 4 → ℤ) : Class2 :=
  ![x 0 * y 1 - x 1 * y 0, x 0 * y 2 - x 2 * y 0, x 0 * y 3 - x 3 * y 0,
    x 1 * y 2 - x 2 * y 1, x 1 * y 3 - x 3 * y 1, x 2 * y 3 - x 3 * y 2]

/-- [definition] The period of `dz` on a lattice vector: `e₁ ↦ 1`, `e₂ ↦ τ`, `e₃, e₄ ↦ 0`. -/
def dz (τ : ℂ) (x : Fin 4 → ℤ) : ℂ := x 0 + x 1 * τ

/-- [definition] The period of `dz'` on a lattice vector: `e₃ ↦ 1`, `e₄ ↦ τ'`, `e₁, e₂ ↦ 0`. -/
def dz' (τ' : ℂ) (x : Fin 4 → ℤ) : ℂ := x 2 + x 3 * τ'

/-- [definition] The pairing of a class with the holomorphic two-form `dz ∧ dz'`. -/
def period (τ τ' : ℂ) (c : Class2) : ℂ := c 1 + c 2 * τ' + c 3 * τ + c 4 * τ * τ'

/-- [proved-derived; formal-checked] On a parallelogram the period is the pairing with
`dz ∧ dz'`. -/
theorem period_wedge (τ τ' : ℂ) (x y : Fin 4 → ℤ) :
    period τ τ' (wedge x y) = dz τ x * dz' τ' y - dz τ y * dz' τ' x := by
  simp only [period, wedge, dz, dz']
  simp
  ring

theorem period_add (τ τ' : ℂ) (c c' : Class2) :
    period τ τ' (c + c') = period τ τ' c + period τ τ' c' := by
  simp only [period, Pi.add_apply]
  push_cast
  ring

theorem period_zsmul (τ τ' : ℂ) (n : ℤ) (c : Class2) :
    period τ τ' (n • c) = n * period τ τ' c := by
  simp only [period, Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

/-- [definition] The period as an additive map `Λ²ℤ⁴ → ℂ`. -/
def periodHom (τ τ' : ℂ) : Class2 →+ ℂ where
  toFun := period τ τ'
  map_zero' := by simp [period]
  map_add' := period_add τ τ'

/-- [definition] An integral class of type `(1, 1)`: the holomorphic two-form pairs to zero with
it. -/
def IsHodge (τ τ' : ℂ) (c : Class2) : Prop := period τ τ' c = 0

/-- [definition] The integral classes of type `(1, 1)` are the kernel of the period, a
subgroup. -/
def hodgeClasses (τ τ' : ℂ) : AddSubgroup Class2 := (periodHom τ τ').ker

theorem mem_hodgeClasses (τ τ' : ℂ) (c : Class2) : c ∈ hodgeClasses τ τ' ↔ IsHodge τ τ' c :=
  Iff.rfl

/-- [definition] A map of lattices `ℤ + ℤτ → ℤ + ℤτ'`: `1 ↦ p + sτ'`, `τ ↦ r + tτ'`. -/
@[ext] structure LatticeMap where
  p : ℤ
  r : ℤ
  s : ℤ
  t : ℤ

namespace LatticeMap

/-- [definition] The determinant of a lattice map: its degree when it is holomorphic. -/
def det (M : LatticeMap) : ℤ := M.p * M.t - M.r * M.s

instance : Zero LatticeMap := ⟨⟨0, 0, 0, 0⟩⟩

@[simp] theorem zero_p : (0 : LatticeMap).p = 0 := rfl
@[simp] theorem zero_r : (0 : LatticeMap).r = 0 := rfl
@[simp] theorem zero_s : (0 : LatticeMap).s = 0 := rfl
@[simp] theorem zero_t : (0 : LatticeMap).t = 0 := rfl

end LatticeMap

/-- [definition] The image of `1` under a lattice map, read in `ℂ`: the multiplier of the map
when it is holomorphic. -/
def multiplier (τ' : ℂ) (M : LatticeMap) : ℂ := M.p + M.s * τ'

/-- [definition] The lattice map is a homomorphism of the tori: it is multiplication by its
multiplier, `M(τ) = τ·M(1)`. -/
def IsHolomorphic (τ τ' : ℂ) (M : LatticeMap) : Prop :=
  (M.r : ℂ) + M.t * τ' = τ * (M.p + M.s * τ')

/-- [proved-derived; formal-checked] Holomorphic means multiplication by one complex number on
both generators of the lattice. -/
theorem isHolomorphic_iff_multiplier (τ τ' : ℂ) (M : LatticeMap) :
    IsHolomorphic τ τ' M ↔
      ∃ μ : ℂ, (M.p : ℂ) + M.s * τ' = μ ∧ (M.r : ℂ) + M.t * τ' = μ * τ := by
  constructor
  · intro h
    exact ⟨(M.p : ℂ) + M.s * τ', rfl, by rw [h, mul_comm]⟩
  · rintro ⟨μ, h1, h2⟩
    unfold IsHolomorphic
    rw [h2, h1, mul_comm]

/-- [definition] `e₁ + M e₁`, the lattice vector the graph of `M` carries over `1`. -/
def graphOne (M : LatticeMap) : Fin 4 → ℤ := ![1, 0, M.p, M.s]

/-- [definition] `e₂ + M e₂`, the lattice vector the graph of `M` carries over `τ`. -/
def graphTau (M : LatticeMap) : Fin 4 → ℤ := ![0, 1, M.r, M.t]

theorem dz'_graphOne (τ' : ℂ) (M : LatticeMap) : dz' τ' (graphOne M) = multiplier τ' M := by
  simp [dz', graphOne, multiplier]

theorem dz'_graphTau (τ' : ℂ) (M : LatticeMap) :
    dz' τ' (graphTau M) = (M.r : ℂ) + M.t * τ' := by
  simp [dz', graphTau]

/-- [definition] The class of the graph of `M` in `E × E'`. -/
def graphClass (M : LatticeMap) : Class2 := ![1, M.r, M.t, -M.p, -M.s, M.det]

/-- [proved-derived; formal-checked] The graph's class is the parallelogram on
`e₁ + M e₁, e₂ + M e₂`. -/
theorem graphClass_eq_wedge (M : LatticeMap) :
    graphClass M = wedge (graphOne M) (graphTau M) := by
  funext i
  fin_cases i <;> simp [graphClass, wedge, graphOne, graphTau, LatticeMap.det]
  ring

/-- [definition] The class of `E × 0`. -/
def fibreE : Class2 := ![1, 0, 0, 0, 0, 0]

/-- [definition] The class of `0 × E'`. -/
def fibreE' : Class2 := ![0, 0, 0, 0, 0, 1]

theorem fibreE_eq_wedge : fibreE = wedge ![1, 0, 0, 0] ![0, 1, 0, 0] := by
  funext i
  fin_cases i <;> simp [fibreE, wedge]

theorem fibreE'_eq_wedge : fibreE' = wedge ![0, 0, 1, 0] ![0, 0, 0, 1] := by
  funext i
  fin_cases i <;> simp [fibreE', wedge]

theorem isHodge_fibreE (τ τ' : ℂ) : IsHodge τ τ' fibreE := by
  simp [IsHodge, period, fibreE]

theorem isHodge_fibreE' (τ τ' : ℂ) : IsHodge τ τ' fibreE' := by
  simp [IsHodge, period, fibreE']

/-- [definition] The intersection number, the wedge `Λ² × Λ² → Λ⁴ ≅ ℤ`. -/
def inter (c c' : Class2) : ℤ :=
  c 0 * c' 5 + c 5 * c' 0 - c 1 * c' 4 - c 4 * c' 1 + c 2 * c' 3 + c 3 * c' 2

theorem inter_comm (c c' : Class2) : inter c c' = inter c' c := by
  simp only [inter]
  ring

/-- [proved-derived; formal-checked] The sign convention of `inter`: two parallelograms meet in
the `4 × 4` determinant of their four sides. -/
theorem inter_wedge_wedge (x y z w : Fin 4 → ℤ) :
    inter (wedge x y) (wedge z w) = Matrix.det (Matrix.of ![x, y, z, w]) := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, Fin.succAbove, inter, wedge]
  ring

/-! ## A graph's class is of type `(1, 1)` precisely when its map is holomorphic -/

theorem period_graphClass (τ τ' : ℂ) (M : LatticeMap) :
    period τ τ' (graphClass M) = ((M.r : ℂ) + M.t * τ') - τ * (M.p + M.s * τ') := by
  simp only [period, graphClass]
  simp
  ring

/-- [proved-derived; formal-checked] H1.  The class of a graph is of type `(1, 1)` if and only if
the lattice map is a homomorphism of the tori. -/
theorem isHodge_graphClass_iff (τ τ' : ℂ) (M : LatticeMap) :
    IsHodge τ τ' (graphClass M) ↔ IsHolomorphic τ τ' M := by
  unfold IsHodge IsHolomorphic
  rw [period_graphClass, sub_eq_zero]

/-! ## The integral Hodge statement -/

/-- [definition] The lattice map read off the four mixed coordinates of a class. -/
def mapOf (c : Class2) : LatticeMap := ⟨-c 3, c 1, -c 4, c 2⟩

theorem mapOf_graphClass (M : LatticeMap) : mapOf (graphClass M) = M := by
  ext <;> simp [mapOf, graphClass]

/-- [proved-derived; formal-checked] Every class is the graph class of its map, adjusted along
the two fibres. -/
theorem eq_graphClass_mapOf (c : Class2) :
    c = graphClass (mapOf c) + (c 0 - 1) • fibreE + (c 5 - (mapOf c).det) • fibreE' := by
  funext i
  fin_cases i <;> simp [graphClass, mapOf, fibreE, fibreE']

/-- [proved-derived; formal-checked] A decomposition along a graph and the two fibres determines
its map and its two coefficients. -/
theorem graph_decomposition_unique {c : Class2} {M : LatticeMap} {x y : ℤ}
    (h : c = graphClass M + x • fibreE + y • fibreE') :
    M = mapOf c ∧ x = c 0 - 1 ∧ y = c 5 - M.det := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  have h4 := congrFun h 4
  have h5 := congrFun h 5
  simp [graphClass, fibreE, fibreE'] at h0 h1 h2 h3 h4 h5
  refine ⟨?_, by omega, by omega⟩
  ext <;> simp only [mapOf] <;> omega

theorem period_eq_period_graphClass_mapOf (τ τ' : ℂ) (c : Class2) :
    period τ τ' c = period τ τ' (graphClass (mapOf c)) := by
  simp only [period, graphClass, mapOf]
  simp

/-- [proved-derived; formal-checked] A class is of type `(1, 1)` precisely when the map read off
its mixed coordinates is holomorphic. -/
theorem isHodge_iff_isHolomorphic_mapOf (τ τ' : ℂ) (c : Class2) :
    IsHodge τ τ' c ↔ IsHolomorphic τ τ' (mapOf c) := by
  rw [← isHodge_graphClass_iff]
  unfold IsHodge
  rw [period_eq_period_graphClass_mapOf]

/-- [proved-derived; formal-checked] H2, the integral Hodge statement in the lattice chart: an
integral class is of type `(1, 1)` if and only if it is an integer combination of the classes of
`E × 0`, `0 × E'` and the graph of a homomorphism `E → E'`, the graph entering once. -/
theorem isHodge_iff_graph (τ τ' : ℂ) (c : Class2) :
    IsHodge τ τ' c ↔ ∃ M : LatticeMap, IsHolomorphic τ τ' M ∧
      c = graphClass M + (c 0 - 1) • fibreE + (c 5 - M.det) • fibreE' := by
  constructor
  · intro h
    exact ⟨mapOf c, (isHodge_iff_isHolomorphic_mapOf τ τ' c).mp h, eq_graphClass_mapOf c⟩
  · rintro ⟨M, hM, hc⟩
    obtain ⟨hMc, -, -⟩ := graph_decomposition_unique hc
    rw [isHodge_iff_isHolomorphic_mapOf, ← hMc]
    exact hM

/-- [proved-derived; formal-checked] H2 with uniqueness: a class of type `(1, 1)` is carried by
one homomorphism and no other. -/
theorem existsUnique_graph_of_isHodge (τ τ' : ℂ) (c : Class2) (h : IsHodge τ τ' c) :
    ∃! M : LatticeMap, IsHolomorphic τ τ' M ∧
      c = graphClass M + (c 0 - 1) • fibreE + (c 5 - M.det) • fibreE' := by
  refine ⟨mapOf c, ⟨(isHodge_iff_isHolomorphic_mapOf τ τ' c).mp h, eq_graphClass_mapOf c⟩, ?_⟩
  rintro M ⟨-, hc⟩
  exact (graph_decomposition_unique hc).1

/-- [proved-derived; formal-checked] Every integral combination of the two fibres and the graph
of a homomorphism is of type `(1, 1)`: the three kinds of cycle span inside the kernel of the
period. -/
theorem isHodge_of_combination (τ τ' : ℂ) {M : LatticeMap} (hM : IsHolomorphic τ τ' M)
    (n x y : ℤ) : IsHodge τ τ' (n • graphClass M + x • fibreE + y • fibreE') := by
  have hg : period τ τ' (graphClass M) = 0 := (isHodge_graphClass_iff τ τ' M).mpr hM
  have hE : period τ τ' fibreE = 0 := isHodge_fibreE τ τ'
  have hE' : period τ τ' fibreE' = 0 := isHodge_fibreE' τ τ'
  unfold IsHodge
  rw [period_add, period_add, period_zsmul, period_zsmul, period_zsmul, hg, hE, hE']
  ring

/-! ## Intersections -/

/-- [proved-derived; formal-checked] A parallelogram meets itself in zero. -/
theorem inter_wedge_self (x y : Fin 4 → ℤ) : inter (wedge x y) (wedge x y) = 0 := by
  simp [inter, wedge]
  ring

/-- [proved-derived; formal-checked] A graph meets itself in zero: a curve of genus one in the
product. -/
theorem inter_graphClass_self (M : LatticeMap) : inter (graphClass M) (graphClass M) = 0 := by
  rw [graphClass_eq_wedge, inter_wedge_self]

/-- [proved-derived; formal-checked] A graph meets `0 × E'` once. -/
theorem inter_graphClass_fibreE' (M : LatticeMap) : inter (graphClass M) fibreE' = 1 := by
  simp [inter, graphClass, fibreE']

/-- [proved-derived; formal-checked] A graph meets `E × 0` in `det M` points: the degree. -/
theorem inter_graphClass_fibreE (M : LatticeMap) : inter (graphClass M) fibreE = M.det := by
  simp [inter, graphClass, fibreE]

theorem inter_fibreE_fibreE' : inter fibreE fibreE' = 1 := by
  simp [inter, fibreE, fibreE']

theorem inter_fibreE_self : inter fibreE fibreE = 0 := by
  simp [inter, fibreE]

theorem inter_fibreE'_self : inter fibreE' fibreE' = 0 := by
  simp [inter, fibreE']

/-- [definition] The mixed part of a graph's class: the graph less its two fibre components. -/
def mixed (M : LatticeMap) : Class2 := graphClass M - fibreE - M.det • fibreE'

theorem mixed_eq (M : LatticeMap) : mixed M = ![0, M.r, M.t, -M.p, -M.s, 0] := by
  funext i
  fin_cases i <;> simp [mixed, graphClass, fibreE, fibreE']

/-- [proved-derived; formal-checked] The mixed part of a graph has self-intersection
`−2·det M`. -/
theorem inter_mixed_self (M : LatticeMap) : inter (mixed M) (mixed M) = -2 * M.det := by
  rw [mixed_eq]
  simp [inter, LatticeMap.det]
  ring

/-- [proved-derived; formal-checked] A class with no fibre component has self-intersection
`−2·det` of its map. -/
theorem inter_self_of_mixed (c : Class2) (h0 : c 0 = 0) :
    inter c c = -2 * (mapOf c).det := by
  simp only [inter, mapOf, LatticeMap.det, h0]
  ring

/-! ## The index theorem is the positivity of the norm -/

/-- An integer combination `a + bτ` vanishes only when both integers do, once `τ` is not real. -/
theorem int_add_mul_eq_zero {τ : ℂ} (hτ : τ.im ≠ 0) {a b : ℤ}
    (h : (a : ℂ) + b * τ = 0) : a = 0 ∧ b = 0 := by
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp at him hre
  have hb : b = 0 := by
    rcases him with hb | hτ0
    · exact hb
    · exact absurd hτ0 hτ
  subst hb
  simp at hre
  exact ⟨hre, rfl⟩

/-- [proved-derived; formal-checked] H5.  For a homomorphism with multiplier `μ`,
`det M · Im τ' = |μ|² · Im τ`: the degree is the multiplier's norm times the ratio of the two
lattices' areas. -/
theorem det_mul_im (τ τ' : ℂ) (M : LatticeMap) (h : IsHolomorphic τ τ' M) :
    (M.det : ℝ) * τ'.im = Complex.normSq (multiplier τ' M) * τ.im := by
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp at hre him
  simp only [multiplier, Complex.normSq_apply, LatticeMap.det]
  simp
  linear_combination ((M.p : ℝ) + M.s * τ'.re) * him - (M.s : ℝ) * τ'.im * hre

/-- [proved-derived; formal-checked] H5 at `τ' = τ`: the degree of an endomorphism is the norm of
its multiplier. -/
theorem det_eq_normSq (τ : ℂ) (hτ : τ.im ≠ 0) (M : LatticeMap) (h : IsHolomorphic τ τ M) :
    (M.det : ℝ) = Complex.normSq (multiplier τ M) := by
  have h1 := det_mul_im τ τ M h
  exact mul_right_cancel₀ hτ h1

/-- [proved-derived; formal-checked] The same identity read in `ℂ`. -/
theorem det_eq_normSq_complex (τ : ℂ) (hτ : τ.im ≠ 0) (M : LatticeMap)
    (h : IsHolomorphic τ τ M) :
    ((M.det : ℤ) : ℂ) = ((Complex.normSq (multiplier τ M) : ℝ) : ℂ) := by
  have h1 := det_eq_normSq τ hτ M h
  exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) h1

/-- [proved-derived; formal-checked] The degree of a homomorphism is not negative. -/
theorem det_nonneg (τ τ' : ℂ) (hτ : 0 < τ.im) (hτ' : 0 < τ'.im) (M : LatticeMap)
    (h : IsHolomorphic τ τ' M) : 0 ≤ M.det := by
  have h1 := det_mul_im τ τ' M h
  have h2 : 0 ≤ Complex.normSq (multiplier τ' M) * τ.im :=
    mul_nonneg (Complex.normSq_nonneg _) hτ.le
  rw [← h1] at h2
  have h3 : (0 : ℝ) ≤ (M.det : ℝ) := nonneg_of_mul_nonneg_left h2 hτ'
  exact_mod_cast h3

/-- [proved-derived; formal-checked] At `τ' = τ` the degree is not negative whichever side of the
real axis `τ` stands on. -/
theorem det_nonneg_self (τ : ℂ) (hτ : τ.im ≠ 0) (M : LatticeMap) (h : IsHolomorphic τ τ M) :
    0 ≤ M.det := by
  have h1 := det_eq_normSq τ hτ M h
  have h2 : (0 : ℝ) ≤ (M.det : ℝ) := h1 ▸ Complex.normSq_nonneg _
  exact_mod_cast h2

/-- [proved-derived; formal-checked] The degree vanishes only for the zero map: the norm form is
definite. -/
theorem det_eq_zero_iff (τ τ' : ℂ) (hτ : τ.im ≠ 0) (hτ' : τ'.im ≠ 0) (M : LatticeMap)
    (h : IsHolomorphic τ τ' M) : M.det = 0 ↔ M = 0 := by
  constructor
  · intro hdet
    have h1 := det_mul_im τ τ' M h
    rw [hdet] at h1
    simp only [Int.cast_zero, zero_mul] at h1
    have h2 : Complex.normSq (multiplier τ' M) = 0 := by
      rcases mul_eq_zero.mp h1.symm with h2 | h2
      · exact h2
      · exact absurd h2 hτ
    have h3 : (M.p : ℂ) + M.s * τ' = 0 := Complex.normSq_eq_zero.mp h2
    obtain ⟨hp, hs⟩ := int_add_mul_eq_zero hτ' h3
    have h4 : (M.r : ℂ) + M.t * τ' = 0 := by
      have := h
      unfold IsHolomorphic at this
      rw [this, h3, mul_zero]
    obtain ⟨hr, ht⟩ := int_add_mul_eq_zero hτ' h4
    ext <;> simp [hp, hr, hs, ht]
  · rintro rfl
    simp [LatticeMap.det]

/-- [proved-derived; formal-checked] The intersection form is negative definite on the mixed
classes of type `(1, 1)`: those with no component along either fibre. -/
theorem inter_negDef_on_mixed_hodge (τ τ' : ℂ) (hτ : 0 < τ.im) (hτ' : 0 < τ'.im) (c : Class2)
    (hc : IsHodge τ τ' c) (h0 : c 0 = 0) (h5 : c 5 = 0) :
    inter c c ≤ 0 ∧ (inter c c = 0 → c = 0) := by
  have hM := (isHodge_iff_isHolomorphic_mapOf τ τ' c).mp hc
  have hdet := det_nonneg τ τ' hτ hτ' (mapOf c) hM
  rw [inter_self_of_mixed c h0]
  refine ⟨by omega, fun hz => ?_⟩
  have hz' : (mapOf c).det = 0 := by omega
  have hM0 := (det_eq_zero_iff τ τ' hτ.ne' hτ'.ne' (mapOf c) hM).mp hz'
  have hp := congrArg LatticeMap.p hM0
  have hr := congrArg LatticeMap.r hM0
  have hs := congrArg LatticeMap.s hM0
  have ht := congrArg LatticeMap.t hM0
  simp [mapOf] at hp hr hs ht
  funext i
  fin_cases i <;> simp [h0, h5, hp, hr, hs, ht]

/-- [proved-derived; formal-checked] The Hodge index theorem of `E × E'` in the lattice chart.
The class `[E × 0] + [0 × E']` has self-intersection `2`, and on every class of type `(1, 1)`
orthogonal to it the intersection form is negative, vanishing only at zero: signature
`(1, ρ − 1)`, with the norm of the multiplier as the cause of the minus signs. -/
theorem hodge_index (τ τ' : ℂ) (hτ : 0 < τ.im) (hτ' : 0 < τ'.im) (c : Class2)
    (hc : IsHodge τ τ' c) (horth : inter c (fibreE + fibreE') = 0) :
    inter c c ≤ 0 ∧ (inter c c = 0 → c = 0) := by
  have hM := (isHodge_iff_isHolomorphic_mapOf τ τ' c).mp hc
  have hdet := det_nonneg τ τ' hτ hτ' (mapOf c) hM
  have h05 : c 5 = -c 0 := by
    simp [inter, fibreE, fibreE'] at horth
    omega
  have hself : inter c c = -2 * (c 0 * c 0) - 2 * (mapOf c).det := by
    simp only [inter, mapOf, LatticeMap.det, h05]
    ring
  rw [hself]
  have hsq : 0 ≤ c 0 * c 0 := mul_self_nonneg _
  refine ⟨by omega, fun hz => ?_⟩
  have hz0 : c 0 * c 0 = 0 := by omega
  have hz' : (mapOf c).det = 0 := by omega
  have hc0 : c 0 = 0 := mul_self_eq_zero.mp hz0
  have hc5 : c 5 = 0 := by rw [h05, hc0, neg_zero]
  have hM0 := (det_eq_zero_iff τ τ' hτ.ne' hτ'.ne' (mapOf c) hM).mp hz'
  have hp := congrArg LatticeMap.p hM0
  have hr := congrArg LatticeMap.r hM0
  have hs := congrArg LatticeMap.s hM0
  have ht := congrArg LatticeMap.t hM0
  simp [mapOf] at hp hr hs ht
  funext i
  fin_cases i <;> simp [hc0, hc5, hp, hr, hs, ht]

theorem inter_ample_self : inter (fibreE + fibreE') (fibreE + fibreE') = 2 := by
  simp [inter, fibreE, fibreE']

/-! ## The places of complex multiplication (`τ' = τ`) -/

/-- [proved-derived; formal-checked] An endomorphism's condition is one integer quadratic relation
on `τ`. -/
theorem isHolomorphic_iff_quadratic (τ : ℂ) (M : LatticeMap) :
    IsHolomorphic τ τ M ↔
      (M.s : ℂ) * τ ^ 2 + ((M.p - M.t : ℤ) : ℂ) * τ + ((-M.r : ℤ) : ℂ) = 0 := by
  unfold IsHolomorphic
  push_cast
  constructor <;> intro h <;> linear_combination (-1 : ℂ) * h

/-- [proved-derived; formal-checked] H3 (i).  When `τ` satisfies no integer quadratic relation
the only homomorphisms `E → E` are the integers. -/
theorem isHolomorphic_iff_of_generic (τ : ℂ)
    (hgen : ∀ A B C : ℤ, (A : ℂ) * τ ^ 2 + B * τ + C = 0 → A = 0 ∧ B = 0 ∧ C = 0)
    (M : LatticeMap) : IsHolomorphic τ τ M ↔ M.s = 0 ∧ M.r = 0 ∧ M.p = M.t := by
  rw [isHolomorphic_iff_quadratic]
  constructor
  · intro h
    obtain ⟨hs, hpt, hr⟩ := hgen _ _ _ h
    exact ⟨hs, by omega, by omega⟩
  · rintro ⟨hs, hr, hpt⟩
    simp [hs, hr, hpt]

/-- A primitive integer quadratic relation on a non-real `τ` has a nonzero leading
coefficient. -/
theorem leading_ne_zero_of_cm {τ : ℂ} (hτ : τ.im ≠ 0) {A B C : ℤ}
    (hrel : (A : ℂ) * τ ^ 2 + B * τ + C = 0) (hprim : Int.gcd A (Int.gcd B C) = 1) :
    A ≠ 0 := by
  rintro rfl
  have h1 : (C : ℂ) + B * τ = 0 := by
    have := hrel
    simp only [Int.cast_zero, zero_mul, zero_add] at this
    linear_combination this
  obtain ⟨hC, hB⟩ := int_add_mul_eq_zero hτ h1
  subst hC hB
  simp at hprim

/-- [proved-derived; formal-checked] H3 (ii).  At a place of complex multiplication,
`Aτ² + Bτ + C = 0` with `gcd(A, B, C) = 1`, the homomorphisms `E → E` are the maps
`t·1 + k·(B + Aτ)`: one integer more than the integers. -/
theorem isHolomorphic_iff_of_cm (τ : ℂ) (hτ : τ.im ≠ 0) {A B C : ℤ}
    (hrel : (A : ℂ) * τ ^ 2 + B * τ + C = 0) (hprim : Int.gcd A (Int.gcd B C) = 1)
    (M : LatticeMap) :
    IsHolomorphic τ τ M ↔ ∃ k : ℤ, M.s = k * A ∧ M.p - M.t = k * B ∧ M.r = -(k * C) := by
  have hA : A ≠ 0 := leading_ne_zero_of_cm hτ hrel hprim
  rw [isHolomorphic_iff_quadratic]
  constructor
  · intro h
    -- eliminate `τ²` between the two relations
    have hlin : (((-(A * M.r) - M.s * C : ℤ)) : ℂ) + ((A * (M.p - M.t) - M.s * B : ℤ) : ℂ) * τ
        = 0 := by
      push_cast
      push_cast at h
      linear_combination (A : ℂ) * h - (M.s : ℂ) * hrel
    obtain ⟨h0, h1⟩ := int_add_mul_eq_zero hτ hlin
    -- Bézout for the primitive triple
    obtain ⟨u, v, huv⟩ : ∃ u v : ℤ, A * u + (Int.gcd B C : ℤ) * v = 1 := by
      refine ⟨Int.gcdA A (Int.gcd B C), Int.gcdB A (Int.gcd B C), ?_⟩
      have hbez := Int.gcd_eq_gcd_ab A (Int.gcd B C)
      rw [hprim, Nat.cast_one] at hbez
      exact hbez.symm
    obtain ⟨x, y, hxy⟩ : ∃ x y : ℤ, (Int.gcd B C : ℤ) = B * x + C * y :=
      ⟨_, _, Int.gcd_eq_gcd_ab B C⟩
    have hone : A * u + (B * x + C * y) * v = 1 := by
      rw [← hxy]
      exact huv
    refine ⟨M.s * u + (M.p - M.t) * x * v - M.r * y * v, ?_, ?_, ?_⟩
    · -- `s = k A`
      linear_combination (-M.s) * hone - (x * v) * h1 - (y * v) * h0
    · -- `p − t = k B`
      have hk : M.s = (M.s * u + (M.p - M.t) * x * v - M.r * y * v) * A := by
        linear_combination (-M.s) * hone - (x * v) * h1 - (y * v) * h0
      have h2 : A * (M.p - M.t - (M.s * u + (M.p - M.t) * x * v - M.r * y * v) * B) = 0 := by
        linear_combination h1 + B * hk
      rcases mul_eq_zero.mp h2 with h3 | h3
      · exact absurd h3 hA
      · linarith
    · -- `r = −k C`
      have hk : M.s = (M.s * u + (M.p - M.t) * x * v - M.r * y * v) * A := by
        linear_combination (-M.s) * hone - (x * v) * h1 - (y * v) * h0
      have h2 : A * (M.r + (M.s * u + (M.p - M.t) * x * v - M.r * y * v) * C) = 0 := by
        linear_combination (-1 : ℤ) * h0 - C * hk
      rcases mul_eq_zero.mp h2 with h3 | h3
      · exact absurd h3 hA
      · linarith
  · rintro ⟨k, hs, hpt, hr⟩
    rw [hs, hpt, hr]
    push_cast
    linear_combination (k : ℂ) * hrel

/-- [proved-derived; formal-checked] The generator of the extra homomorphisms at a place of
complex multiplication: multiplication by `Aτ`, the lattice map `(0, −C, A, −B)`. -/
theorem isHolomorphic_cm_generator (τ : ℂ) {A B C : ℤ}
    (hrel : (A : ℂ) * τ ^ 2 + B * τ + C = 0) : IsHolomorphic τ τ ⟨0, -C, A, -B⟩ := by
  unfold IsHolomorphic
  push_cast
  linear_combination (-1 : ℂ) * hrel

/-- [proved-derived; formal-checked] Rank three away from complex multiplication: the classes of
type `(1, 1)` on `E × E` are `(c12, 0, c14, −c14, 0, c34)`, spanned by `E × 0`, `0 × E` and the
diagonal. -/
theorem isHodge_iff_of_generic (τ : ℂ)
    (hgen : ∀ A B C : ℤ, (A : ℂ) * τ ^ 2 + B * τ + C = 0 → A = 0 ∧ B = 0 ∧ C = 0)
    (c : Class2) : IsHodge τ τ c ↔ c 1 = 0 ∧ c 4 = 0 ∧ c 2 + c 3 = 0 := by
  rw [isHodge_iff_isHolomorphic_mapOf, isHolomorphic_iff_of_generic τ hgen]
  simp only [mapOf]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h2, by omega, by omega⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by omega, h1, by omega⟩

/-- [proved-derived; formal-checked] Rank four at a place of complex multiplication: one more
integer `k` enters the classes of type `(1, 1)` on `E × E`. -/
theorem isHodge_iff_of_cm (τ : ℂ) (hτ : τ.im ≠ 0) {A B C : ℤ}
    (hrel : (A : ℂ) * τ ^ 2 + B * τ + C = 0) (hprim : Int.gcd A (Int.gcd B C) = 1)
    (c : Class2) :
    IsHodge τ τ c ↔ ∃ k : ℤ, c 4 = -(k * A) ∧ c 2 + c 3 = -(k * B) ∧ c 1 = -(k * C) := by
  rw [isHodge_iff_isHolomorphic_mapOf, isHolomorphic_iff_of_cm τ hτ hrel hprim]
  simp only [mapOf]
  constructor
  · rintro ⟨k, h1, h2, h3⟩
    exact ⟨k, by omega, by omega, h3⟩
  · rintro ⟨k, h1, h2, h3⟩
    exact ⟨k, by omega, by omega, h3⟩

/-- [proved-derived; formal-checked] The diagonal of `E × E` is the graph of the identity and is
of type `(1, 1)` for every `τ`. -/
theorem isHodge_diagonal (τ : ℂ) : IsHodge τ τ (graphClass ⟨1, 0, 0, 1⟩) := by
  rw [isHodge_graphClass_iff]
  simp [IsHolomorphic]

/-! ## When a nonzero homomorphism exists -/

/-- [proved-derived; formal-checked] H4.  A nonzero homomorphism `E → E'` exists precisely when
`τ·(p + sτ') = r + tτ'` for integers with `(p, s) ≠ (0, 0)`: when `τ` is a rational fractional
linear image of `τ'`. -/
theorem exists_nonzero_holomorphic_iff (τ τ' : ℂ) (hτ' : τ'.im ≠ 0) :
    (∃ M : LatticeMap, M ≠ 0 ∧ IsHolomorphic τ τ' M) ↔
      ∃ p r s t : ℤ, (p ≠ 0 ∨ s ≠ 0) ∧ τ * ((p : ℂ) + s * τ') = (r : ℂ) + t * τ' := by
  constructor
  · rintro ⟨M, hM0, hM⟩
    refine ⟨M.p, M.r, M.s, M.t, ?_, hM.symm⟩
    by_contra hps
    have hp : M.p = 0 := by
      by_contra hp
      exact hps (Or.inl hp)
    have hs : M.s = 0 := by
      by_contra hs
      exact hps (Or.inr hs)
    have h4 : (M.r : ℂ) + M.t * τ' = 0 := by
      have := hM
      unfold IsHolomorphic at this
      rw [this, hp, hs]
      simp
    obtain ⟨hr, ht⟩ := int_add_mul_eq_zero hτ' h4
    exact hM0 (by ext <;> simp [hp, hr, hs, ht])
  · rintro ⟨p, r, s, t, hps, h⟩
    refine ⟨⟨p, r, s, t⟩, ?_, h.symm⟩
    intro h0
    have hp := congrArg LatticeMap.p h0
    have hs := congrArg LatticeMap.s h0
    simp at hp hs
    rcases hps with hps | hps
    · exact hps hp
    · exact hps hs

/-- [proved-derived; formal-checked] The multiplier of a nonzero lattice map is not zero, so a
nonzero homomorphism gives `τ = (r + tτ')/(p + sτ')`. -/
theorem eq_div_of_isHolomorphic (τ τ' : ℂ) (hτ' : τ'.im ≠ 0) (M : LatticeMap)
    (hps : M.p ≠ 0 ∨ M.s ≠ 0) (hM : IsHolomorphic τ τ' M) :
    τ = ((M.r : ℂ) + M.t * τ') / ((M.p : ℂ) + M.s * τ') := by
  have hne : (M.p : ℂ) + M.s * τ' ≠ 0 := by
    intro h0
    obtain ⟨hp, hs⟩ := int_add_mul_eq_zero hτ' h0
    rcases hps with hps | hps
    · exact hps hp
    · exact hps hs
  rw [eq_div_iff hne]
  exact hM.symm

section Audit

#print axioms period_wedge
#print axioms inter_wedge_wedge
#print axioms graphClass_eq_wedge
#print axioms isHodge_graphClass_iff
#print axioms isHodge_iff_graph
#print axioms existsUnique_graph_of_isHodge
#print axioms isHodge_of_combination
#print axioms inter_graphClass_self
#print axioms inter_mixed_self
#print axioms det_mul_im
#print axioms det_eq_normSq
#print axioms det_eq_zero_iff
#print axioms inter_negDef_on_mixed_hodge
#print axioms hodge_index
#print axioms isHolomorphic_iff_of_generic
#print axioms isHolomorphic_iff_of_cm
#print axioms isHodge_iff_of_generic
#print axioms isHodge_iff_of_cm
#print axioms exists_nonzero_holomorphic_iff

end Audit

end Holonics.Hodge.EllipticProduct
