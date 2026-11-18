import Mathlib

/-!
# Hard Lefschetz from positivity: a move, its reversal and their commutator

**[definition]** The setting (`Triple`).  A real inner product space `V` with a move `U`, its
reversal `D` (the adjoint, `⟪U x, y⟫ = ⟪x, D y⟫`), and their commutator `H = D U − U D`, with
`H U − U H = −2 U`: `U` lowers the weight `H` reads by two, and `D` raises it by two (`raise`).  This
is the `sl₂` of a Lefschetz operator `L = U`, its dual `Λ = D` and the degree operator `H`, given
abstractly; `dual` is the same triple read the other way (`D` moves, `U` reverses, weight `−H`).
`weightSpace m` is the eigenspace of `H` at `m`, and `P(m) = ker (D : W(m) → W(m + 2))` is the
primitive part (`primitiveMap`).

**[proved-derived; formal-checked]** What is proved.

1. **B1, strings** (`weight_iterate`, `D_iterate_succ`): `U^j x` has weight `m − 2j`, and
   `D U^(j+1) x = U^(j+1) D x + (j + 1)(m − j) U^j x` on a weight `m`.
2. **B2, the reversal's own form** (`norm_sq_U_sub_norm_sq_D`, `norm_gap`,
   `mul_norm_sq_le_norm_sq_U`, `eq_zero_of_U_eq_zero`, `eq_zero_of_D_eq_zero`):
   `‖U x‖² − ‖D x‖² = ⟪x, H x⟫` for every `x`, so on a positive weight `m ‖x‖² ≤ ‖U x‖²` and `U` is
   injective, and on a negative weight `D` is injective.
3. **B3, hard Lefschetz with its constant** (`inner_iterate_nonneg`, `prod_le_norm_sq_iterate`,
   `prod_eq_factorial_sq`, `hard_lefschetz`, `hard_lefschetz_D`, `eq_zero_of_iterate_eq_zero`): on a
   weight `m ∈ ℕ`, `m! ‖x‖ ≤ ‖U^m x‖`, in any dimension, and the mirror `m! ‖y‖ ≤ ‖D^m y‖` on the
   weight `−m`.
4. **B4, the Hodge–Riemann identity on primitives** (`inner_iterate_primitive`,
   `norm_sq_iterate_primitive`, `inner_iterate_primitive_nat`, `iterate_succ_eq_zero_of_primitive`):
   for `x` primitive of weight `m`, `⟪U^j x, U^j y⟫ = (∏_(i<j) (i + 1)(m − i)) ⟪x, y⟫`, which is
   `j! · m!/(m − j)! · ⟪x, y⟫` for `j ≤ m`; so each power of the move is a similitude on primitives
   with a positive factor up to `j = m`, and the string ends at `U^(m+1) x = 0`.
5. **B5, B6** (`exists_iterate_eq_zero`, `natural_of_primitive`, `primitive_iff`): in finite
   dimension every string ends, a nonzero primitive vector has a natural weight, and on a weight
   `m ∈ ℕ`, `D x = 0 ↔ U^(m+1) x = 0`.
6. **B7, the two halves match** (`finrank_weightSpace_neg`, `finrank_weightSpace_add_two_le`,
   `finrank_weightSpace_sub_two_le`): `dim W(m) = dim W(−m)` for `m ∈ ℕ`, and the dimensions grow
   toward weight zero from both sides.
7. **B8, hard Lefschetz as an isomorphism** (`lefschetzMap`, `lefschetzMap_injective`,
   `lefschetzMap_bijective`, `lefschetzEquiv`): in finite dimension `U^m : W(m) → W(−m)` is a
   linear equivalence for every `m ∈ ℕ`.
8. **B9, the count of primitives** (`primitiveMap_comp_moveMap_injective`,
   `primitiveMap_surjective`, `finrank_primitive_add`, `inner_primitive_move`): for `m + 2 > 0`,
   `D : W(m) → W(m + 2)` is onto, `dim P(m) + dim W(m + 2) = dim W(m)`, and `P(m)` is orthogonal
   to `U W(m + 2)` inside `W(m)`: the count of the Lefschetz decomposition.

**Reading.**  [interpretation] `agent-inferred`.  The record of November 18 on the half says that a
move with a reversal carries a form built from the two, and that where that form is positive every
mode sits at the half.  Here the form is `⟪x, H x⟫ = ‖U x‖² − ‖D x‖²`, the commutator of the move
with its reversal, and positivity is the inner product's own.  On a weight `m > 0` the move cannot
kill a vector, and along the string each step multiplies the squared norm by at least
`(j + 1)(m − j) > 0`, so `U^m` loses nothing: hard Lefschetz is the positivity of this form read
`m` times.  On primitives the same identity is an equality, the Hodge–Riemann form
`⟪U^j x, U^j y⟫` with its positive constant.  Nothing else is used: no complex structure, no
manifold, no harmonic theory.

**What this does not state.**  The triple is given: no Kähler manifold, no Kähler identities and
no harmonic representatives are constructed, so this is not hard Lefschetz for any variety until
such a triple is built on its cohomology with `⟪·,·⟫` positive.  The signs of the Hodge–Riemann
bilinear relations on a variety (`(−1)^(k(k−1)/2) i^(p−q)` on the primitive `(p, q)` part, against
the intersection pairing, which is not positive) are not stated: here the pairing is an inner
product from the start.  The Lefschetz decomposition is given as its count and its orthogonality,
not as a direct sum of submodules.

**Computational object.**  The helical pair interaction: the move and its reversal are a pair
contact read in two senses, and the commutator is what the contact leaves on a state.  Of the
winding guide's six objects: the tower thread (the weights are a transverse restriction, a string
is a thread of it) and faces and placement (the weight spaces are faces, and the Lefschetz map
places one face onto its mirror).

**Consumers.**  The atlas row `hodge.hard-lefschetz-positivity`.

Source record: `research/records/2026-11-18_AN_ABELIAN_COVER_FACTORS_THROUGH_ITS_CHARACTERS_A_TEMPERED_COMPLEX_MIXES_AT_ITS_HALF_THE_FLUIDS_TRIADS_DO_NO_WORK_SO_EVERY_TRUNCATION_FLOWS_FOR_ALL_TIME_AND_HARD_LEFSCHETZ_IS_A_POSITIVE_COMMUTATOR.md` (§8).

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Hodge.LefschetzFromPositivity

open RealInnerProductSpace Finset

/-- [definition] A raising move `U`, its reversal `D` (the adjoint of `U` under the inner product)
and their commutator `H = D U − U D`, with `U` lowering the weight read by `H` by two. -/
structure Triple (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V] where
  /-- The move. -/
  U : V →ₗ[ℝ] V
  /-- Its reversal. -/
  D : V →ₗ[ℝ] V
  /-- The weight. -/
  H : V →ₗ[ℝ] V
  adj : ∀ x y, ⟪U x, y⟫ = ⟪x, D y⟫
  comm : ∀ x, D (U x) - U (D x) = H x
  lower : ∀ x, H (U x) - U (H x) = (-2 : ℝ) • U x

namespace Triple

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (T : Triple V)

/-- [proved-derived; formal-checked] The reversal read from the other side. -/
theorem adj' (x y : V) : ⟪x, T.U y⟫ = ⟪T.D x, y⟫ := by
  rw [real_inner_comm, T.adj, real_inner_comm]

/-- [proved-derived; formal-checked] The weight is self-adjoint. -/
theorem H_adj (x y : V) : ⟪T.H x, y⟫ = ⟪x, T.H y⟫ := by
  rw [← T.comm, ← T.comm, inner_sub_left, inner_sub_right, ← T.adj' (T.U x) y, T.adj (T.D x) y,
    ← T.adj x (T.U y), T.adj' x (T.D y)]

/-- [proved-derived; formal-checked] The reversal raises the weight by two: `H D − D H = 2 D`. -/
theorem raise (x : V) : T.H (T.D x) - T.D (T.H x) = (2 : ℝ) • T.D x := by
  apply ext_inner_right ℝ
  intro v
  have hl : T.U (T.H v) - T.H (T.U v) = (2 : ℝ) • T.U v := by
    rw [← neg_sub, T.lower v, neg_smul, neg_neg]
  calc ⟪T.H (T.D x) - T.D (T.H x), v⟫ = ⟪x, T.U (T.H v)⟫ - ⟪x, T.H (T.U v)⟫ := by
        rw [inner_sub_left, T.H_adj, ← T.adj', ← T.adj', T.H_adj]
    _ = ⟪x, (2 : ℝ) • T.U v⟫ := by rw [← inner_sub_right, hl]
    _ = ⟪(2 : ℝ) • T.D x, v⟫ := by rw [real_inner_smul_right, real_inner_smul_left, T.adj']

/-- [definition] The reversed triple: `D` raises, `U` reverses it, and the weight is `−H`. -/
def dual : Triple V where
  U := T.D
  D := T.U
  H := -T.H
  adj x y := (T.adj' x y).symm
  comm x := by rw [LinearMap.neg_apply, ← T.comm, neg_sub]
  lower x := by
    simp only [LinearMap.neg_apply, map_neg]
    rw [neg_sub_neg, ← neg_sub, T.raise, neg_smul]

@[simp] theorem dual_U : T.dual.U = T.D := rfl
@[simp] theorem dual_D : T.dual.D = T.U := rfl
@[simp] theorem dual_H : T.dual.H = -T.H := rfl

variable {T}

/-- [proved-derived; formal-checked] **B1, the weights along a string**: `U^j x` has weight
`m − 2j`. -/
theorem weight_iterate {m : ℝ} {x : V} (hx : T.H x = m • x) (j : ℕ) :
    T.H (T.U^[j] x) = (m - 2 * j) • T.U^[j] x := by
  induction j with
  | zero => simpa using hx
  | succ j ih =>
    have h := T.lower (T.U^[j] x)
    rw [sub_eq_iff_eq_add] at h
    rw [Function.iterate_succ_apply', h, ih, map_smul, ← add_smul]
    congr 1
    push_cast
    ring

/-- [proved-derived; formal-checked] **B1, the commutation along a string**:
`D U^(j+1) x = U^(j+1) D x + (j + 1)(m − j) U^j x` for `x` of weight `m`. -/
theorem D_iterate_succ {m : ℝ} {x : V} (hx : T.H x = m • x) (j : ℕ) :
    T.D (T.U^[j + 1] x) = T.U^[j + 1] (T.D x) + (((j : ℝ) + 1) * (m - j)) • T.U^[j] x := by
  induction j with
  | zero =>
    have h := T.comm x
    rw [sub_eq_iff_eq_add'] at h
    simp only [zero_add, Function.iterate_one, Function.iterate_zero, id_eq, CharP.cast_eq_zero,
      sub_zero, one_mul]
    rw [h, hx]
  | succ j ih =>
    have hc := T.comm (T.U^[j + 1] x)
    rw [sub_eq_iff_eq_add'] at hc
    rw [Function.iterate_succ_apply' (⇑T.U) (j + 1) x, hc, ih, map_add, map_smul,
      T.weight_iterate hx (j + 1), ← Function.iterate_succ_apply' (⇑T.U) (j + 1) (T.D x),
      ← Function.iterate_succ_apply' (⇑T.U) j x, add_assoc, ← add_smul]
    congr 2
    push_cast
    ring

/-- [proved-derived; formal-checked] **B2, the norm gap**: `‖U x‖² − ‖D x‖² = ⟪x, H x⟫` for every
vector. -/
theorem norm_sq_U_sub_norm_sq_D (x : V) : ‖T.U x‖ ^ 2 - ‖T.D x‖ ^ 2 = ⟪x, T.H x⟫ := by
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, T.adj, ← T.adj',
    ← inner_sub_right, T.comm]

/-- [proved-derived; formal-checked] **B2 on a weight vector**: `‖U x‖² − ‖D x‖² = m ‖x‖²`. -/
theorem norm_gap {m : ℝ} {x : V} (hx : T.H x = m • x) :
    ‖T.U x‖ ^ 2 - ‖T.D x‖ ^ 2 = m * ‖x‖ ^ 2 := by
  rw [T.norm_sq_U_sub_norm_sq_D, hx, real_inner_smul_right, real_inner_self_eq_norm_sq]

/-- [proved-derived; formal-checked] On a positive weight the move loses nothing:
`m ‖x‖² ≤ ‖U x‖²`. -/
theorem mul_norm_sq_le_norm_sq_U {m : ℝ} {x : V} (hx : T.H x = m • x) :
    m * ‖x‖ ^ 2 ≤ ‖T.U x‖ ^ 2 := by
  have := T.norm_gap hx
  nlinarith [sq_nonneg ‖T.D x‖]

/-- [proved-derived; formal-checked] `U` is injective on a positive weight. -/
theorem eq_zero_of_U_eq_zero {m : ℝ} (hm : 0 < m) {x : V} (hx : T.H x = m • x)
    (hU : T.U x = 0) : x = 0 := by
  have h := T.mul_norm_sq_le_norm_sq_U hx
  rw [hU, norm_zero] at h
  have : ‖x‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖x‖]
  exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this)

/-- [proved-derived; formal-checked] `D` is injective on a negative weight. -/
theorem eq_zero_of_D_eq_zero {m : ℝ} (hm : m < 0) {x : V} (hx : T.H x = m • x)
    (hD : T.D x = 0) : x = 0 :=
  T.dual.eq_zero_of_U_eq_zero (m := -m) (by linarith)
    (by rw [dual_H, LinearMap.neg_apply, hx, neg_smul]) hD

/-- [proved-derived; formal-checked] One step of the norm along a string:
`‖U^(j+1) x‖² = ⟪U^(j+1) D x, U^j x⟫ + (j + 1)(m − j) ‖U^j x‖²`. -/
theorem norm_sq_iterate_succ {m : ℝ} {x : V} (hx : T.H x = m • x) (j : ℕ) :
    ‖T.U^[j + 1] x‖ ^ 2 =
      ⟪T.U^[j + 1] (T.D x), T.U^[j] x⟫ + (((j : ℝ) + 1) * (m - j)) * ‖T.U^[j] x‖ ^ 2 := by
  calc ‖T.U^[j + 1] x‖ ^ 2 = ⟪T.U^[j + 1] x, T.U (T.U^[j] x)⟫ := by
        rw [← Function.iterate_succ_apply' (⇑T.U) j x, real_inner_self_eq_norm_sq]
    _ = ⟪T.D (T.U^[j + 1] x), T.U^[j] x⟫ := T.adj' _ _
    _ = _ := by
      rw [T.D_iterate_succ hx j, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]

/-- [proved-derived; formal-checked] The cross terms `a_j = ⟪U^(j+1) D x, U^j x⟫` are nonnegative
while `j ≤ m + 1`: `a_0 = ‖D x‖²` and `a_(j+1) = ‖U^(j+1) D x‖² + (j + 1)(m − j) a_j`. -/
theorem inner_iterate_nonneg {m : ℝ} {x : V} (hx : T.H x = m • x) :
    ∀ j : ℕ, (j : ℝ) ≤ m + 1 → 0 ≤ ⟪T.U^[j + 1] (T.D x), T.U^[j] x⟫ := by
  intro j
  induction j with
  | zero =>
    intro _
    simp only [zero_add, Function.iterate_one, Function.iterate_zero, id_eq]
    rw [T.adj]
    exact real_inner_self_nonneg
  | succ j ih =>
    intro hj
    push_cast at hj
    rw [Function.iterate_succ_apply' (⇑T.U) (j + 1), T.adj, T.D_iterate_succ hx j,
      inner_add_right, real_inner_smul_right]
    have hc : 0 ≤ ((j : ℝ) + 1) * (m - j) := mul_nonneg (by positivity) (by linarith)
    exact add_nonneg real_inner_self_nonneg (mul_nonneg hc (ih (by linarith)))

/-- [proved-derived; formal-checked] The chain of the norm: for `j ≤ m + 1`,
`(∏_(i<j) (i + 1)(m − i)) ‖x‖² ≤ ‖U^j x‖²`. -/
theorem prod_le_norm_sq_iterate {m : ℝ} {x : V} (hx : T.H x = m • x) :
    ∀ j : ℕ, (j : ℝ) ≤ m + 1 →
      (∏ i ∈ range j, (((i : ℝ) + 1) * (m - i))) * ‖x‖ ^ 2 ≤ ‖T.U^[j] x‖ ^ 2 := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    push_cast at hj
    rw [prod_range_succ, T.norm_sq_iterate_succ hx j]
    have ha := T.inner_iterate_nonneg hx j (by linarith)
    have hc : 0 ≤ ((j : ℝ) + 1) * (m - j) := mul_nonneg (by positivity) (by linarith)
    have key := mul_le_mul_of_nonneg_left (ih (by linarith)) hc
    nlinarith

/-- [proved-standard; formal-checked] `∏_(i<m) (i + 1)(m − i) = (m!)²`. -/
theorem prod_eq_factorial_sq (m : ℕ) :
    ∏ i ∈ range m, (((i : ℝ) + 1) * ((m : ℝ) - i)) = ((m.factorial : ℕ) : ℝ) ^ 2 := by
  have h1 : ∏ i ∈ range m, ((i : ℝ) + 1) = (m.factorial : ℝ) := by
    rw [← Finset.prod_range_add_one_eq_factorial]
    push_cast
    rfl
  have h2 : ∏ i ∈ range m, ((m : ℝ) - i) = (m.factorial : ℝ) := by
    rw [← h1, ← Finset.prod_range_reflect (fun i : ℕ => (i : ℝ) + 1) m]
    apply prod_congr rfl
    intro i hi
    rw [mem_range] at hi
    rw [Nat.cast_sub (show i ≤ m - 1 by omega), Nat.cast_sub (show 1 ≤ m by omega)]
    push_cast
    ring
  rw [prod_mul_distrib, h1, h2, sq]

/-- [proved-derived; formal-checked] **B3, hard Lefschetz with its constant**: on a weight
`m ∈ ℕ`, `m! ‖x‖ ≤ ‖U^m x‖`. -/
theorem hard_lefschetz (m : ℕ) {x : V} (hx : T.H x = (m : ℝ) • x) :
    (m.factorial : ℝ) * ‖x‖ ≤ ‖T.U^[m] x‖ := by
  have h := T.prod_le_norm_sq_iterate hx m (by linarith)
  rw [prod_eq_factorial_sq] at h
  have h' : ((m.factorial : ℝ) * ‖x‖) ^ 2 ≤ ‖T.U^[m] x‖ ^ 2 := by rw [mul_pow]; exact h
  exact (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp h'

/-- [proved-derived; formal-checked] **B3, the mirror**: on a weight `−m`, `m! ‖y‖ ≤ ‖D^m y‖`. -/
theorem hard_lefschetz_D (m : ℕ) {y : V} (hy : T.H y = (-(m : ℝ)) • y) :
    (m.factorial : ℝ) * ‖y‖ ≤ ‖T.D^[m] y‖ :=
  T.dual.hard_lefschetz m (by rw [dual_H, LinearMap.neg_apply, hy, neg_smul, neg_neg])

/-- [proved-derived; formal-checked] `U^m` is injective on the weight `m ∈ ℕ`. -/
theorem eq_zero_of_iterate_eq_zero (m : ℕ) {x : V} (hx : T.H x = (m : ℝ) • x)
    (h : T.U^[m] x = 0) : x = 0 := by
  have := T.hard_lefschetz m hx
  rw [h, norm_zero] at this
  have hf : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  have : ‖x‖ ≤ 0 := by nlinarith [norm_nonneg x]
  exact norm_eq_zero.mp (le_antisymm this (norm_nonneg x))

/-- [proved-derived; formal-checked] **B4, the Hodge–Riemann identity**: for `x` primitive
(`D x = 0`) of weight `m` and any `y`,
`⟪U^j x, U^j y⟫ = (∏_(i<j) (i + 1)(m − i)) ⟪x, y⟫`. -/
theorem inner_iterate_primitive {m : ℝ} {x : V} (hx : T.H x = m • x) (hD : T.D x = 0)
    (y : V) (j : ℕ) :
    ⟪T.U^[j] x, T.U^[j] y⟫ = (∏ i ∈ range j, (((i : ℝ) + 1) * (m - i))) * ⟪x, y⟫ := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply' (⇑T.U) j y, T.adj', T.D_iterate_succ hx j, hD,
      Function.iterate_fixed (map_zero T.U), zero_add, real_inner_smul_left, ih, prod_range_succ]
    ring

/-- [proved-derived; formal-checked] **B4, the norm on a primitive string**:
`‖U^j x‖² = (∏_(i<j) (i + 1)(m − i)) ‖x‖²`. -/
theorem norm_sq_iterate_primitive {m : ℝ} {x : V} (hx : T.H x = m • x) (hD : T.D x = 0)
    (j : ℕ) :
    ‖T.U^[j] x‖ ^ 2 = (∏ i ∈ range j, (((i : ℝ) + 1) * (m - i))) * ‖x‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
    T.inner_iterate_primitive hx hD x j]

/-- [proved-derived; formal-checked] **B4, a primitive string ends**: for `x` primitive of weight
`m ∈ ℕ`, `U^(m+1) x = 0`. -/
theorem iterate_succ_eq_zero_of_primitive (m : ℕ) {x : V} (hx : T.H x = (m : ℝ) • x)
    (hD : T.D x = 0) : T.U^[m + 1] x = 0 := by
  have h := T.norm_sq_iterate_primitive hx hD (m + 1)
  rw [prod_range_succ, sub_self, mul_zero, mul_zero, zero_mul] at h
  exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h)

/-- [proved-derived; formal-checked] **B6, primitive is the kernel of the next power**: for `x` of
weight `m ∈ ℕ`, `D x = 0 ↔ U^(m+1) x = 0`. -/
theorem primitive_iff (m : ℕ) {x : V} (hx : T.H x = (m : ℝ) • x) :
    T.D x = 0 ↔ T.U^[m + 1] x = 0 := by
  constructor
  · exact T.iterate_succ_eq_zero_of_primitive m hx
  · intro hU
    have hDx : T.H (T.D x) = ((m + 2 : ℕ) : ℝ) • T.D x := by
      have h := T.raise x
      rw [sub_eq_iff_eq_add] at h
      rw [h, hx, map_smul, ← add_smul]
      congr 1
      push_cast
      ring
    have h2 : T.U^[m + 2] x = 0 := by
      rw [Function.iterate_succ_apply' (⇑T.U) (m + 1) x, hU, map_zero]
    have h3 := T.D_iterate_succ hx (m + 1)
    rw [h2, map_zero, hU, smul_zero, add_zero] at h3
    exact T.eq_zero_of_iterate_eq_zero (m + 2) hDx h3.symm

/-- [proved-standard; formal-checked] For `j ≤ m`, `∏_(i<j) (i + 1)(m − i) = j! · m!/(m − j)!`,
written as `j! · m.descFactorial j`. -/
theorem prod_eq_factorial_mul_descFactorial {m j : ℕ} (hj : j ≤ m) :
    ∏ i ∈ range j, (((i : ℝ) + 1) * ((m : ℝ) - i)) =
      (j.factorial : ℝ) * (m.descFactorial j : ℝ) := by
  rw [prod_mul_distrib, ← Finset.prod_range_add_one_eq_factorial, Nat.descFactorial_eq_prod_range]
  push_cast
  congr 1
  apply prod_congr rfl
  intro i hi
  rw [mem_range] at hi
  rw [Nat.cast_sub (by omega)]

/-- [proved-derived; formal-checked] **B4, every power of the move is a similitude on
primitives**: for `x` primitive of weight `m ∈ ℕ` and `j ≤ m`,
`⟪U^j x, U^j y⟫ = j! · m!/(m − j)! · ⟪x, y⟫`. -/
theorem inner_iterate_primitive_nat (m : ℕ) {x : V} (hx : T.H x = (m : ℝ) • x)
    (hD : T.D x = 0) (y : V) {j : ℕ} (hj : j ≤ m) :
    ⟪T.U^[j] x, T.U^[j] y⟫ = ((j.factorial : ℝ) * (m.descFactorial j : ℝ)) * ⟪x, y⟫ := by
  rw [T.inner_iterate_primitive hx hD y j, prod_eq_factorial_mul_descFactorial hj]

/-! ## Finite dimension: the weights of primitives, and the two halves -/

/-- [proved-derived; formal-checked] In finite dimension every string ends: some power of the move
kills a weight vector. -/
theorem exists_iterate_eq_zero [FiniteDimensional ℝ V] {m : ℝ} {x : V} (hx : T.H x = m • x) :
    ∃ j : ℕ, T.U^[j] x = 0 := by
  by_contra hall
  simp only [not_exists] at hall
  have hfin := Module.End.finite_hasEigenvalue T.H
  refine (Set.infinite_of_injective_forall_mem (f := fun j : ℕ => m - 2 * (j : ℝ)) ?_ ?_) hfin
  · intro a b h
    have : (a : ℝ) = b := by simp only at h; linarith
    exact_mod_cast this
  · intro j
    exact Module.End.hasEigenvalue_of_hasEigenvector
      (Module.End.hasEigenvector_iff.mpr
        ⟨Module.End.mem_eigenspace_iff.mpr (T.weight_iterate hx j), hall j⟩)

/-- [proved-derived; formal-checked] **B5, a primitive weight is a natural number**: in finite
dimension a nonzero primitive vector of weight `m ∈ ℝ` has `m = N` for some `N ∈ ℕ`. -/
theorem natural_of_primitive [FiniteDimensional ℝ V] {m : ℝ} {x : V} (hx : T.H x = m • x)
    (hD : T.D x = 0) (hx0 : x ≠ 0) : ∃ N : ℕ, m = N := by
  obtain ⟨j, hj⟩ := T.exists_iterate_eq_zero hx
  have h := T.norm_sq_iterate_primitive hx hD j
  rw [hj, norm_zero, zero_pow two_ne_zero] at h
  have hn : ‖x‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hx0)
  have hP := (mul_eq_zero.mp h.symm).resolve_right hn
  rw [prod_eq_zero_iff] at hP
  obtain ⟨i, _, hi⟩ := hP
  rcases mul_eq_zero.mp hi with h1 | h1
  · have : (0 : ℝ) < (i : ℝ) + 1 := by positivity
    linarith
  · exact ⟨i, by linarith⟩

variable (T) in
/-- [definition] The weight space of `m`: the eigenspace of `H` at `m`. -/
abbrev weightSpace (m : ℝ) : Submodule ℝ V := Module.End.eigenspace T.H m

theorem mem_weightSpace {m : ℝ} {x : V} : x ∈ T.weightSpace m ↔ T.H x = m • x :=
  Module.End.mem_eigenspace_iff

/-- [proved-derived; formal-checked] `U^m` carries the weight `m` into the weight `−m`. -/
theorem pow_mem_weightSpace_neg (m : ℕ) {x : V} (hx : x ∈ T.weightSpace m) :
    (T.U ^ m) x ∈ T.weightSpace (-(m : ℝ)) := by
  rw [mem_weightSpace] at hx ⊢
  rw [Module.End.pow_apply, T.weight_iterate hx m]
  congr 1
  ring

/-- [proved-derived; formal-checked] `D^m` carries the weight `−m` into the weight `m`. -/
theorem pow_D_mem_weightSpace (m : ℕ) {y : V} (hy : y ∈ T.weightSpace (-(m : ℝ))) :
    (T.D ^ m) y ∈ T.weightSpace (m : ℝ) := by
  rw [mem_weightSpace] at hy ⊢
  have hy' : T.dual.H y = (m : ℝ) • y := by rw [dual_H, LinearMap.neg_apply, hy, neg_smul, neg_neg]
  have h := T.dual.weight_iterate hy' m
  rw [dual_H, LinearMap.neg_apply, dual_U, neg_eq_iff_eq_neg] at h
  rw [Module.End.pow_apply, h, ← neg_smul]
  congr 1
  ring

/-- [proved-derived; formal-checked] **B7, the two halves match**: in finite dimension, for
`m ∈ ℕ`, the weight spaces of `m` and `−m` have one dimension; `U^m` is an isomorphism between
them, injective by B3, and `D^m` is injective back by the mirror. -/
theorem finrank_weightSpace_neg [FiniteDimensional ℝ V] (m : ℕ) :
    Module.finrank ℝ (T.weightSpace (m : ℝ)) = Module.finrank ℝ (T.weightSpace (-(m : ℝ))) := by
  apply le_antisymm
  · apply LinearMap.finrank_le_finrank_of_injective
      (f := (T.U ^ m).restrict (fun x hx => T.pow_mem_weightSpace_neg m hx))
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨a, ha⟩ h
    have h' : (T.U ^ m) a = 0 := congrArg Subtype.val h
    rw [Module.End.pow_apply] at h'
    exact Subtype.ext (T.eq_zero_of_iterate_eq_zero m (mem_weightSpace.mp ha) h')
  · apply LinearMap.finrank_le_finrank_of_injective
      (f := (T.D ^ m).restrict (fun y hy => T.pow_D_mem_weightSpace m hy))
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨a, ha⟩ h
    have h' : (T.D ^ m) a = 0 := congrArg Subtype.val h
    rw [Module.End.pow_apply] at h'
    have := T.hard_lefschetz_D m (mem_weightSpace.mp ha)
    rw [h', norm_zero] at this
    have hf : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
    have h0 : ‖a‖ ≤ 0 := by nlinarith [norm_nonneg a]
    exact Subtype.ext (norm_eq_zero.mp (le_antisymm h0 (norm_nonneg a)))

variable (T) in
/-- [definition] The Lefschetz map of the weight `m ∈ ℕ`: `U^m` restricted to `W(m) → W(−m)`. -/
def lefschetzMap (m : ℕ) : T.weightSpace (m : ℝ) →ₗ[ℝ] T.weightSpace (-(m : ℝ)) :=
  (T.U ^ m).restrict (fun _ hx => T.pow_mem_weightSpace_neg m hx)

/-- [proved-derived; formal-checked] The Lefschetz map is injective, in any dimension (B3). -/
theorem lefschetzMap_injective (m : ℕ) : Function.Injective (T.lefschetzMap m) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  rintro ⟨a, ha⟩ h
  have h' : (T.U ^ m) a = 0 := congrArg Subtype.val h
  rw [Module.End.pow_apply] at h'
  exact Subtype.ext (T.eq_zero_of_iterate_eq_zero m (mem_weightSpace.mp ha) h')

/-- [proved-derived; formal-checked] **B8, hard Lefschetz as an isomorphism**: in finite dimension,
for every `m ∈ ℕ`, `U^m : W(m) → W(−m)` is bijective. -/
theorem lefschetzMap_bijective [FiniteDimensional ℝ V] (m : ℕ) :
    Function.Bijective (T.lefschetzMap m) := by
  refine ⟨T.lefschetzMap_injective m, ?_⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (T.finrank_weightSpace_neg m)).mp (T.lefschetzMap_injective m)

variable (T) in
/-- [definition] Hard Lefschetz as a linear equivalence `W(m) ≃ W(−m)`. -/
noncomputable def lefschetzEquiv [FiniteDimensional ℝ V] (m : ℕ) :
    T.weightSpace (m : ℝ) ≃ₗ[ℝ] T.weightSpace (-(m : ℝ)) :=
  LinearEquiv.ofBijective (T.lefschetzMap m) (T.lefschetzMap_bijective m)

@[simp] theorem lefschetzEquiv_apply [FiniteDimensional ℝ V] (m : ℕ) (x : T.weightSpace (m : ℝ)) :
    (T.lefschetzEquiv m x : V) = (T.U ^ m) x := rfl

/-- [proved-derived; formal-checked] `U` carries the weight `m + 2` into the weight `m`. -/
theorem U_mem_weightSpace {m : ℝ} {x : V} (hx : x ∈ T.weightSpace (m + 2)) :
    T.U x ∈ T.weightSpace m := by
  rw [mem_weightSpace] at hx ⊢
  have h := T.weight_iterate hx 1
  simp only [Function.iterate_one, Nat.cast_one] at h
  rw [h]
  congr 1
  ring

/-- [proved-derived; formal-checked] `D` carries the weight `m − 2` into the weight `m`. -/
theorem D_mem_weightSpace {m : ℝ} {x : V} (hx : x ∈ T.weightSpace (m - 2)) :
    T.D x ∈ T.weightSpace m := by
  rw [mem_weightSpace] at hx ⊢
  have h := T.raise x
  rw [sub_eq_iff_eq_add] at h
  rw [h, hx, map_smul, ← add_smul]
  congr 1
  ring

/-- [proved-derived; formal-checked] **B7, the dimensions grow toward weight zero** (upper side):
for `m + 2 > 0`, `dim W(m + 2) ≤ dim W(m)`, by `U`, injective there by B2. -/
theorem finrank_weightSpace_add_two_le [FiniteDimensional ℝ V] {m : ℝ} (hm : 0 < m + 2) :
    Module.finrank ℝ (T.weightSpace (m + 2)) ≤ Module.finrank ℝ (T.weightSpace m) := by
  apply LinearMap.finrank_le_finrank_of_injective
    (f := T.U.restrict (fun x hx => T.U_mem_weightSpace hx))
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  rintro ⟨a, ha⟩ h
  have h' : T.U a = 0 := congrArg Subtype.val h
  exact Subtype.ext (T.eq_zero_of_U_eq_zero hm (mem_weightSpace.mp ha) h')

/-- [proved-derived; formal-checked] **B7, the lower side**: for `m − 2 < 0`,
`dim W(m − 2) ≤ dim W(m)`, by `D`, injective there by B2. -/
theorem finrank_weightSpace_sub_two_le [FiniteDimensional ℝ V] {m : ℝ} (hm : m - 2 < 0) :
    Module.finrank ℝ (T.weightSpace (m - 2)) ≤ Module.finrank ℝ (T.weightSpace m) := by
  apply LinearMap.finrank_le_finrank_of_injective
    (f := T.D.restrict (fun x hx => T.D_mem_weightSpace hx))
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  rintro ⟨a, ha⟩ h
  have h' : T.D a = 0 := congrArg Subtype.val h
  exact Subtype.ext (T.eq_zero_of_D_eq_zero hm (mem_weightSpace.mp ha) h')

variable (T) in
/-- [definition] The reversal restricted to a weight, `D : W(m) → W(m + 2)`; its kernel is the
primitive part `P(m)`. -/
def primitiveMap (m : ℝ) : T.weightSpace m →ₗ[ℝ] T.weightSpace (m + 2) :=
  T.D.restrict (fun x hx => T.D_mem_weightSpace (m := m + 2) (by rwa [add_sub_cancel_right]))

variable (T) in
/-- [definition] The move restricted to a weight, `U : W(m + 2) → W(m)`. -/
def moveMap (m : ℝ) : T.weightSpace (m + 2) →ₗ[ℝ] T.weightSpace m :=
  T.U.restrict (fun _ hx => T.U_mem_weightSpace hx)

/-- [proved-derived; formal-checked] For `m + 2 > 0`, `D ∘ U` is injective on `W(m + 2)`:
`⟪D U y, y⟫ = ‖U y‖²` and `U` is injective there (B2). -/
theorem primitiveMap_comp_moveMap_injective {m : ℝ} (hm : 0 < m + 2) :
    Function.Injective (T.primitiveMap m ∘ₗ T.moveMap m) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  rintro ⟨y, hy⟩ h
  have h' : T.D (T.U y) = 0 := congrArg Subtype.val h
  have hU : T.U y = 0 := by
    have : ⟪T.U y, T.U y⟫ = 0 := by rw [T.adj, h', inner_zero_right]
    exact inner_self_eq_zero.mp this
  exact Subtype.ext (T.eq_zero_of_U_eq_zero hm (mem_weightSpace.mp hy) hU)

/-- [proved-derived; formal-checked] For `m + 2 > 0`, in finite dimension, `D : W(m) → W(m + 2)`
is onto. -/
theorem primitiveMap_surjective [FiniteDimensional ℝ V] {m : ℝ} (hm : 0 < m + 2) :
    Function.Surjective (T.primitiveMap m) := by
  have hbij := LinearMap.injective_iff_surjective.mp (T.primitiveMap_comp_moveMap_injective hm)
  intro z
  obtain ⟨y, hy⟩ := hbij z
  exact ⟨T.moveMap m y, hy⟩

/-- [proved-derived; formal-checked] **B9, the count of primitives**: for `m + 2 > 0`, in finite
dimension, `dim P(m) + dim W(m + 2) = dim W(m)`, where `P(m) = ker (D : W(m) → W(m + 2))`.  With
`m ∈ ℕ` this is `dim P(m) = dim W(m) − dim W(m + 2)`, the Lefschetz decomposition's count. -/
theorem finrank_primitive_add [FiniteDimensional ℝ V] {m : ℝ} (hm : 0 < m + 2) :
    Module.finrank ℝ (LinearMap.ker (T.primitiveMap m)) +
        Module.finrank ℝ (T.weightSpace (m + 2)) =
      Module.finrank ℝ (T.weightSpace m) := by
  have h := LinearMap.finrank_range_add_finrank_ker (T.primitiveMap m)
  rw [LinearMap.range_eq_top.mpr (T.primitiveMap_surjective hm), finrank_top] at h
  omega

/-- [proved-derived; formal-checked] The primitive part and the image of the move are orthogonal
inside `W(m)`: `⟪x, U y⟫ = ⟪D x, y⟫ = 0` for `x ∈ P(m)`. -/
theorem inner_primitive_move {m : ℝ} {x : T.weightSpace m}
    (hx : x ∈ LinearMap.ker (T.primitiveMap m)) (y : T.weightSpace (m + 2)) :
    ⟪(x : V), (T.moveMap m y : V)⟫ = 0 := by
  have hD : T.D x = 0 := congrArg Subtype.val (LinearMap.mem_ker.mp hx)
  change ⟪(x : V), T.U y⟫ = 0
  rw [T.adj', hD, inner_zero_left]

end Triple

section Audit

open Triple

#print axioms Triple.raise
#print axioms Triple.norm_sq_U_sub_norm_sq_D
#print axioms Triple.eq_zero_of_U_eq_zero
#print axioms Triple.hard_lefschetz
#print axioms Triple.hard_lefschetz_D
#print axioms Triple.inner_iterate_primitive
#print axioms Triple.inner_iterate_primitive_nat
#print axioms Triple.iterate_succ_eq_zero_of_primitive
#print axioms Triple.primitive_iff
#print axioms Triple.natural_of_primitive
#print axioms Triple.finrank_weightSpace_neg
#print axioms Triple.lefschetzMap_bijective
#print axioms Triple.finrank_primitive_add
#print axioms Triple.inner_primitive_move

end Audit

end Holonics.Hodge.LefschetzFromPositivity
