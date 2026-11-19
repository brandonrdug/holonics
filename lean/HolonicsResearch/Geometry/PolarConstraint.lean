import Holonics.Geometry.Motion
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Rat.Lemmas
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Tactic

/-!
# Polar factors on two coordinates, the roots carried as their constraints

Sources: #410's box for the polar factors over square-root extensions, the roots carried as their constraints;
the closing paragraph of `Geometry/Motion`, which cites the polar decomposition over a field with square roots
and does not prove it, beside its split of a rate into a skew turn and a self-adjoint boost (item 1,
`turn_add_boost`) and its turn · boost · shear factorization of `SL(2)` (item 11, `iwasawa`); §9 of the motion
record of September 28 (`THE_SWING_IS_A_MOVE_ABOUT_A_GRIP_…`), whose owed list names the box; the polar factors
over `ℂ` at determinant one in `HolonicsResearch/Physics/Spacetime/LorentzOnto` (`lorentz_polar`, and
`exists_herm_sqrt`, whose root `(X + 1)/√(tr X + 2)` is this file's root at `s = 1`); the two boosts that
compose into a boost and a turn in `Physics/Spacetime/WignerGeneral` (`disk_composition`); the gate read as a
move's polar factorization in `HNN/CarryGate` (a turn times a boost toward rest, the one-coordinate complex
chart of `turnChart_polar` below); and the winding guide's sentence that the site kinds by trace and
determinant are "not a universal Euclidean polar decomposition". Atlas rows served: `motion.turn-boost-split`,
`motion.iwasawa-sl2`, `trace.site-kind`, `lorentz.pair-move-double-cover`, `lorentz.wigner-general`.

On two coordinates a positive definite form `M` has a square root that is a polynomial of degree one in `M`:
by Cayley–Hamilton, `P = (M + s·1)/t` with `s² = det M` and `t² = tr M + 2s`. The two roots `s` and `t` are
carried as these constraints, never evaluated, so every statement holds in any ordered field that contains
them; `Real.sqrt` supplies them over `ℝ` in §5. For the polar factors of a move `A`, `M = AᵀA` has
`det M = (det A)²`, so `s = |det A|` is already in the field and `t` is the only new root.

[definition] `IsPosDef2` (a symmetric form on two coordinates with positive leading minors), `constraintRoot`,
`polarBoost`, `polarTurn`, `polarBoostLeft`.

[proved-standard; formal-checked] What is proved, over a field `K` with a strict linear order unless a
statement names another (each theorem carries its own grade; the constraint readings and the witnesses are
`proved-derived`).

1. **Two minors** (§1). `IsPosDef2 M` is a symmetric form with positive quadratic form
   (`isPosDef2_iff_quadratic`); a symmetric form with positive trace and determinant is one
   (`isPosDef2_of_trace_det`); one has positive trace (`IsPosDef2.trace_pos`) and a positive definite square
   (`IsPosDef2.mul_self`); `symm_entry` reads the symmetry on entries.
2. **The root by its constraints** (§2). Over any field, `X² = (tr X) X − (det X) 1` (`mul_self_fin_two`) and
   `tr X² = (tr X)² − 2 det X` (`trace_mul_self_fin_two`); for `t ≠ 0`, `s² = det M` and `t² = tr M + 2s`, the
   root squares to `M` (`constraintRoot_mul_self`), its determinant is `s` and its trace is `t`
   (`constraintRoot_det`, `constraintRoot_trace`): the two constraint roots are the root's own determinant
   and trace. Over the ordered field, a symmetric `M` with `s, t > 0` has a positive definite root
   (`constraintRoot_transpose`, `constraintRoot_isPosDef2`) and is itself positive definite
   (`isPosDef2_of_constraints`); a positive definite root reads `det Q = s` and `(tr Q)² = tr Q² + 2s`
   (`det_trace_of_mul_self`), so it is `(M + s·1)/t` (`constraintRoot_unique`, `existsUnique_root`); and `M`
   has a positive definite root over `K` if and only if `K` holds the two positive constraint roots
   (`exists_root_iff`).
3. **The polar factors** (§3). For `det A ≠ 0` the Gram form `AᵀA` is positive definite with determinant
   `(det A)²` (`gram_isPosDef2`, `gram_det`, `abs_det_sq`). With `t > 0`, `t² = tr AᵀA + 2|det A|`: the boost
   `P = (AᵀA + |det A|·1)/t` is positive definite with `P² = AᵀA`, `det P = |det A|`, `tr P = t`
   (`polarBoost_isPosDef2`, `polarBoost_mul_self`, `polarBoost_det_trace`, `polarBoost_isUnit_det`); the turn
   `U = A P⁻¹` gives `A = U P` (`polarTurn_mul_polarBoost`), `UᵀU = 1` (`polarTurn_orthogonal`) and
   `det U · |det A| = det A`, so `det U = 1` for `det A > 0` and `det U = −1` for `det A < 0`
   (`polarTurn_det_mul`, `polarTurn_det_of_pos`, `polarTurn_det_of_neg`). The pair is unique: an orthogonal
   `U'` and a positive definite `P'` with `A = U' P'` are `U` and `P` (`eq_polarTurn_of_mul`, `polar_unique`).
   Every such factorization reads the root, `(tr P)² = tr AᵀA + 2|det A|` (`trace_sq_of_polar`), so the polar
   factors exist over `K` if and only if `K` holds `t` (`exists_polar_iff`). The left form takes the same `t`
   (`gram_left_trace`, `gram_left_det`): `P̃ = (AAᵀ + |det A|·1)/t` is `U P Uᵀ` (`polarBoostLeft_eq`), positive
   definite with `P̃² = AAᵀ` (`polarBoostLeft_isPosDef2`), `A = P̃ U` (`polarBoostLeft_mul_polarTurn`), and the
   left pair is unique (`polar_left_unique`).
4. **The swing's turn and boost** (§4), in Motion's charts. For `det A > 0`, `U` is the turn chart
   `[[x, −y], [y, x]]` with `x = (a + d)/t`, `y = (c − b)/t` on the circle `x² + y² = 1`
   (`polarTurn_eq_turnChart`, `turnChart_coeff_sq`); for `det A < 0`, `U` is a turn after the reflection
   `diag(1, −1)`, with `x = (a − d)/t`, `y = (b + c)/t` (`polarTurn_eq_turnChart_reflect`). A turn has no boost:
   an orthogonal `A` has `t = 2`, `P = 1`, `U = A` (`polar_of_orthogonal`, `turnChart_orthogonal`). A boost has
   no turn: a positive definite `A` has `t = tr A`, `P = A`, `U = 1` (`polar_of_isPosDef2`), and the pure boost
   `diag(a, 1/a)` with `a > 0` has `t = a + 1/a` (`boostChart_polar`). A complex multiplier `k = x + iy` read
   as `[[x, −y], [y, x]]` has `t = 2ρ`, `P = ρ·1`, `U` the turn of `(x/ρ, y/ρ)`, with the modulus carried as
   `ρ² = x² + y²` (`turnChart_polar`).
5. **The witnesses** (§4). The shear `[[1, 1], [0, 1]]` has `det = 1` and `tr AᵀA + 2|det A| = 5`
   (`shear_root_constraint`); for `t > 0` with `t² = 5`, `P = [[2, 1], [1, 3]]/t` and `U` is the turn of
   `(2/t, −1/t)` (`shear_polar`); every polar factorization of the shear has `(tr P)² = 5`
   (`shear_polar_trace_sq`); five is not a rational square (`five_not_isSquare`), so the shear has no polar
   factors over `ℚ` (`shear_no_rational_polar`): they live over `ℚ(√5)`. Its Iwasawa factors through Motion's
   `iwasawa` stay rational, `r = 1` with a trivial turn and boost (`shear_iwasawa`); and a move of `SL(2)`
   carries both factorizations at once, the polar root `t² = a² + b² + c² + d² + 2` beside the Iwasawa root
   `r² = a² + c²` (`sl2_polar_and_iwasawa`): two factorizations of one move, with different roots.
6. **Over `ℝ`** (§5). On a field with the trivial star, `IsPosDef2` is Mathlib's `Matrix.PosDef`
   (`isPosDef2_iff_posDef`); `s = √(det M)`, `t = √(tr M + 2s)` give the real root (`real_constraintRoot`), the
   unique positive definite root (`real_existsUnique_root`) and the unique polar pair of an invertible real move
   (`real_existsUnique_polar`).
7. **Over `ℂ`** (§6). For invertible complex `A`, real `s > 0` with `s² = |det A|²` (the real root of
   `|det A|²`, again a constraint) and real `t > 0` with `t² = tr AᴴA + 2s`, the boost `(AᴴA + s·1)/t` is
   positive definite in Mathlib's sense with square `AᴴA`, determinant `s` and trace `t`, and `U = A P⁻¹` is
   unitary with `A = U P` (`complex_polar`).

What is not claimed. The polar decomposition on `n` coordinates: for `n ≥ 3` the root of `AᵀA` is not of
degree one in `AᵀA` with two constraint roots, and it needs the eigenvalues, which this file does not use.
The uniqueness of the complex factors and the complex left form (`complex_polar` gives existence and the two
invariants only). The singular case `det A = 0`, where `P` is only semidefinite and `U` is not fixed. Which
fields hold `t` for a given move beyond `exists_polar_iff`: only the shear over `ℚ` is shown to need its root.
The factors here are read against the unit receiver (`UᵀU = 1`, `Pᵀ = P`); against another receiver metric
`G` the turn is `G`-orthogonal and the boost `G`-symmetric, and that reading, like the site kinds of the
winding guide (similarity classes by trace and determinant), is not treated. The turn's angle is never
evaluated: the turn is carried as its point `(x, y)` of the circle. How the finite factors meet Motion's
infinitesimal split of a rate is not proved.

The computational object is the helical pair interaction: a contact's move on its two coordinates is a turn
that the unit receiver reads without work (`UᵀU = 1`) after a boost that carries all of the stretch (`P`
symmetric positive definite), and the roots that split needs are carried as the constraints `s² = det M`,
`t² = tr M + 2s` of the pair's Gram form, never evaluated. Of the winding guide's six general objects this
touches the pair (the move, its Gram form and its two factors) and the helix (the turn as a point of the
circle `x² + y² = 1`, and the reflected sheet when `det A < 0`); faces and placement, cell holonomy, the tube
and the tower thread stay attached.

Consumers: #410's box; the sentence of `Geometry/Motion` that cites the polar decomposition, which this file
discharges on two coordinates; the atlas rows above.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.Geometry.PolarConstraint

open Matrix

/-! ## 1. A positive definite form on two coordinates, read by its two minors -/

section Definite

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- [definition] A symmetric positive definite form on two coordinates, by its two leading minors. -/
def IsPosDef2 (M : Matrix (Fin 2) (Fin 2) K) : Prop :=
  Mᵀ = M ∧ 0 < M 0 0 ∧ 0 < M.det

omit [Field K] [LinearOrder K] [IsStrictOrderedRing K] in
/-- [proved-standard; formal-checked] A symmetric form on two coordinates has equal off-diagonal entries. -/
theorem symm_entry {M : Matrix (Fin 2) (Fin 2) K} (h : Mᵀ = M) : M 1 0 = M 0 1 := by
  have := congrFun (congrFun h 0) 1
  simpa using this

theorem isPosDef2_iff_quadratic {M : Matrix (Fin 2) (Fin 2) K} :
    IsPosDef2 M ↔ Mᵀ = M ∧ ∀ v : Fin 2 → K, v ≠ 0 → 0 < v ⬝ᵥ (M *ᵥ v) := by
  constructor
  · rintro ⟨hs, h0, hd⟩
    refine ⟨hs, fun v hv => ?_⟩
    have h10 := symm_entry hs
    rw [det_fin_two, h10] at hd
    simp only [dotProduct, mulVec, Fin.sum_univ_two, h10]
    have key : M 0 0 * (v 0 * (M 0 0 * v 0 + M 0 1 * v 1) + v 1 * (M 0 1 * v 0 + M 1 1 * v 1)) =
        (M 0 0 * v 0 + M 0 1 * v 1) ^ 2 + (M 0 0 * M 1 1 - M 0 1 * M 0 1) * v 1 ^ 2 := by ring
    by_cases hv1 : v 1 = 0
    · have hv0 : v 0 ≠ 0 := by
        intro hv0
        apply hv
        ext i
        fin_cases i <;> simp [hv0, hv1]
      rw [hv1]
      have : 0 < v 0 ^ 2 := by positivity
      nlinarith
    · have : 0 < v 1 ^ 2 := by positivity
      have hpos : 0 < M 0 0 * (v 0 * (M 0 0 * v 0 + M 0 1 * v 1) +
          v 1 * (M 0 1 * v 0 + M 1 1 * v 1)) := by
        rw [key]; positivity
      exact pos_of_mul_pos_right hpos h0.le
  · rintro ⟨hs, hq⟩
    have h10 := symm_entry hs
    have h0 : 0 < M 0 0 := by
      have := hq ![1, 0] (fun h => by simpa using congrFun h 0)
      simpa [dotProduct, mulVec, Fin.sum_univ_two] using this
    refine ⟨hs, h0, ?_⟩
    have hne : (![-M 0 1, M 0 0] : Fin 2 → K) ≠ 0 := fun h => by
      have := congrFun h 1
      simp at this
      exact h0.ne' this
    have := hq _ hne
    simp only [dotProduct, mulVec, Fin.sum_univ_two, h10] at this
    simp at this
    rw [det_fin_two, h10]
    have hp : 0 < M 0 0 * (M 0 0 * M 1 1 - M 0 1 * M 0 1) := by nlinarith [this]
    exact pos_of_mul_pos_right hp h0.le

/-- [proved-standard; formal-checked] A symmetric form with positive trace and determinant is positive definite. -/
theorem isPosDef2_of_trace_det {M : Matrix (Fin 2) (Fin 2) K} (hs : Mᵀ = M) (ht : 0 < M.trace)
    (hd : 0 < M.det) : IsPosDef2 M := by
  refine ⟨hs, ?_, hd⟩
  have h10 := symm_entry hs
  rw [trace_fin_two] at ht
  rw [det_fin_two, h10] at hd
  by_contra h
  push Not at h
  nlinarith [sq_nonneg (M 0 1)]

/-- [proved-standard; formal-checked] A positive definite form has positive trace. -/
theorem IsPosDef2.trace_pos {M : Matrix (Fin 2) (Fin 2) K} (hM : IsPosDef2 M) : 0 < M.trace := by
  obtain ⟨hs, h0, hd⟩ := hM
  have h10 := symm_entry hs
  rw [trace_fin_two]
  rw [det_fin_two, h10] at hd
  nlinarith [sq_nonneg (M 0 1)]

/-- [proved-standard; formal-checked] The square of a positive definite form is positive definite. -/
theorem IsPosDef2.mul_self {P : Matrix (Fin 2) (Fin 2) K} (hP : IsPosDef2 P) : IsPosDef2 (P * P) := by
  obtain ⟨hs, h0, hd⟩ := hP
  have h10 := symm_entry hs
  refine ⟨by rw [transpose_mul, hs], ?_, by rw [det_mul]; positivity⟩
  simp only [mul_apply, Fin.sum_univ_two, h10]
  nlinarith [sq_nonneg (P 0 1)]

end Definite

/-! ## 2. The square root of a form on two coordinates, carried by its two constraints -/

section Root

variable {K : Type*} [Field K]

/-- [proved-standard; formal-checked] **Cayley–Hamilton on two coordinates**: `X² = (tr X) X − (det X) 1`. -/
theorem mul_self_fin_two (X : Matrix (Fin 2) (Fin 2) K) : X * X = X.trace • X - X.det • 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, trace_fin_two, det_fin_two] <;> ring

/-- [proved-standard; formal-checked] The trace of a square on two coordinates: `tr X² = (tr X)² − 2 det X`. -/
theorem trace_mul_self_fin_two (X : Matrix (Fin 2) (Fin 2) K) :
    (X * X).trace = X.trace ^ 2 - 2 * X.det := by
  simp [Matrix.mul_apply, Fin.sum_univ_two, trace_fin_two, det_fin_two]
  ring

/-- [definition] **The root by its constraints**: `P = (M + s·1)/t`, where `s` and `t` stand for the roots
`s² = det M` and `t² = tr M + 2s`. -/
def constraintRoot (M : Matrix (Fin 2) (Fin 2) K) (s t : K) : Matrix (Fin 2) (Fin 2) K :=
  t⁻¹ • (M + s • 1)

/-- [proved-standard; formal-checked] **The root squares to the form**: `s² = det M`, `t² = tr M + 2s` and
`t ≠ 0` give `P² = M`, for any form on two coordinates over any field. -/
theorem constraintRoot_mul_self {M : Matrix (Fin 2) (Fin 2) K} {s t : K} (ht : t ≠ 0)
    (hs : s ^ 2 = M.det) (htt : t ^ 2 = M.trace + 2 * s) :
    constraintRoot M s t * constraintRoot M s t = M := by
  rw [trace_fin_two] at htt
  rw [det_fin_two] at hs
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [constraintRoot, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
  all_goals field_simp
  · linear_combination hs - M 0 0 * htt
  · linear_combination (-M 0 1) * htt
  · linear_combination (-M 1 0) * htt
  · linear_combination hs - M 1 1 * htt

/-- [proved-derived; formal-checked] **The root's determinant is the first constraint root**: `det P = s`. -/
theorem constraintRoot_det {M : Matrix (Fin 2) (Fin 2) K} {s t : K} (ht : t ≠ 0)
    (hs : s ^ 2 = M.det) (htt : t ^ 2 = M.trace + 2 * s) : (constraintRoot M s t).det = s := by
  rw [trace_fin_two] at htt
  rw [det_fin_two] at hs
  simp [constraintRoot, det_fin_two]
  field_simp
  linear_combination (-1 : K) * hs - s * htt

/-- [proved-derived; formal-checked] **The root's trace is the second constraint root**: `tr P = t`. -/
theorem constraintRoot_trace {M : Matrix (Fin 2) (Fin 2) K} {s t : K} (ht : t ≠ 0)
    (htt : t ^ 2 = M.trace + 2 * s) : (constraintRoot M s t).trace = t := by
  rw [trace_fin_two] at htt
  simp [constraintRoot, trace_fin_two]
  field_simp
  linear_combination (-1 : K) * htt

/-- [proved-standard; formal-checked] The root of a symmetric form is symmetric. -/
theorem constraintRoot_transpose {M : Matrix (Fin 2) (Fin 2) K} (hM : Mᵀ = M) (s t : K) :
    (constraintRoot M s t)ᵀ = constraintRoot M s t := by
  simp [constraintRoot, transpose_smul, transpose_add, hM]

variable [LinearOrder K] [IsStrictOrderedRing K]

/-- [proved-standard; formal-checked] **The root is positive definite**: for symmetric `M`, positive constraint
roots `s` and `t` give a positive definite `P`. -/
theorem constraintRoot_isPosDef2 {M : Matrix (Fin 2) (Fin 2) K} {s t : K} (hM : Mᵀ = M) (hs0 : 0 < s)
    (hs : s ^ 2 = M.det) (ht0 : 0 < t) (htt : t ^ 2 = M.trace + 2 * s) :
    IsPosDef2 (constraintRoot M s t) :=
  isPosDef2_of_trace_det (constraintRoot_transpose hM s t)
    (by rw [constraintRoot_trace ht0.ne' htt]; exact ht0)
    (by rw [constraintRoot_det ht0.ne' hs htt]; exact hs0)

/-- [proved-derived; formal-checked] **The constraints make the form positive definite**: a symmetric `M`
with positive constraint roots `s` and `t` is positive definite, the square of its root. -/
theorem isPosDef2_of_constraints {M : Matrix (Fin 2) (Fin 2) K} {s t : K} (hM : Mᵀ = M) (hs0 : 0 < s)
    (hs : s ^ 2 = M.det) (ht0 : 0 < t) (htt : t ^ 2 = M.trace + 2 * s) : IsPosDef2 M := by
  rw [← constraintRoot_mul_self ht0.ne' hs htt]
  exact (constraintRoot_isPosDef2 hM hs0 hs ht0 htt).mul_self

/-- [proved-standard; formal-checked] **A positive definite root reads its constraint roots**: if `Q` is
positive definite and `s > 0` with `s² = det (Q Q)`, then `det Q = s` and `(tr Q)² = tr (Q Q) + 2s`. -/
theorem det_trace_of_mul_self {Q : Matrix (Fin 2) (Fin 2) K} (hQ : IsPosDef2 Q) {s : K} (hs0 : 0 < s)
    (hs : s ^ 2 = (Q * Q).det) : Q.det = s ∧ Q.trace ^ 2 = (Q * Q).trace + 2 * s := by
  have hd : Q.det = s := by
    rw [det_mul, ← sq] at hs
    exact (sq_eq_sq₀ hQ.2.2.le hs0.le).mp hs.symm
  refine ⟨hd, ?_⟩
  rw [trace_mul_self_fin_two, hd]
  ring

/-- [proved-standard; formal-checked] **The root is the only positive definite root**: any positive definite
`Q` with `Q² = M` is `(M + s·1)/t`, for the positive constraint roots `s` and `t`. -/
theorem constraintRoot_unique {M Q : Matrix (Fin 2) (Fin 2) K} {s t : K} (hs0 : 0 < s)
    (hs : s ^ 2 = M.det) (ht0 : 0 < t) (htt : t ^ 2 = M.trace + 2 * s) (hQ : IsPosDef2 Q)
    (hQM : Q * Q = M) : Q = constraintRoot M s t := by
  subst hQM
  obtain ⟨hd, htr⟩ := det_trace_of_mul_self hQ hs0 hs
  have htq : Q.trace = t := (sq_eq_sq₀ hQ.trace_pos.le ht0.le).mp (by rw [htr, htt])
  rw [constraintRoot, mul_self_fin_two Q, htq, hd, sub_add_cancel, smul_smul, inv_mul_cancel₀ ht0.ne',
    one_smul]

/-- [proved-standard; formal-checked] **One positive definite root**: under the constraints, `(M + s·1)/t` is
the unique positive definite `P` with `P² = M`. -/
theorem existsUnique_root {M : Matrix (Fin 2) (Fin 2) K} {s t : K} (hM : Mᵀ = M) (hs0 : 0 < s)
    (hs : s ^ 2 = M.det) (ht0 : 0 < t) (htt : t ^ 2 = M.trace + 2 * s) :
    ∃! P : Matrix (Fin 2) (Fin 2) K, IsPosDef2 P ∧ P * P = M :=
  ⟨constraintRoot M s t, ⟨constraintRoot_isPosDef2 hM hs0 hs ht0 htt, constraintRoot_mul_self ht0.ne' hs htt⟩,
    fun _ ⟨hQ, hQM⟩ => constraintRoot_unique hs0 hs ht0 htt hQ hQM⟩

/-- [proved-derived; formal-checked] **The root lives where its constraint roots live**: a positive definite
`M` has a positive definite root over `K` if and only if `K` holds positive `s`, `t` with `s² = det M` and
`t² = tr M + 2s`. -/
theorem exists_root_iff {M : Matrix (Fin 2) (Fin 2) K} (hM : IsPosDef2 M) :
    (∃ P : Matrix (Fin 2) (Fin 2) K, IsPosDef2 P ∧ P * P = M) ↔
      ∃ s t : K, 0 < s ∧ s ^ 2 = M.det ∧ 0 < t ∧ t ^ 2 = M.trace + 2 * s := by
  constructor
  · rintro ⟨P, hP, rfl⟩
    refine ⟨P.det, P.trace, hP.2.2, by rw [det_mul, sq], hP.trace_pos, ?_⟩
    rw [trace_mul_self_fin_two]
    ring
  · rintro ⟨s, t, hs0, hs, ht0, htt⟩
    exact ⟨constraintRoot M s t, constraintRoot_isPosDef2 hM.1 hs0 hs ht0 htt,
      constraintRoot_mul_self ht0.ne' hs htt⟩

end Root

/-! ## 3. The polar factors of a move on two coordinates -/

section Polar

variable {K : Type*} [Field K]

/-- [proved-standard; formal-checked] The Gram form `AᵀA` has determinant `(det A)²`. -/
theorem gram_det (A : Matrix (Fin 2) (Fin 2) K) : (Aᵀ * A).det = A.det ^ 2 := by
  rw [det_mul, det_transpose, sq]

/-- [proved-standard; formal-checked] The Gram form `AAᵀ` has determinant `(det A)²`. -/
theorem gram_left_det (A : Matrix (Fin 2) (Fin 2) K) : (A * Aᵀ).det = A.det ^ 2 := by
  rw [det_mul, det_transpose, sq]

/-- [proved-standard; formal-checked] The two Gram forms share their trace: `tr AAᵀ = tr AᵀA`. -/
theorem gram_left_trace (A : Matrix (Fin 2) (Fin 2) K) : (A * Aᵀ).trace = (Aᵀ * A).trace :=
  trace_mul_comm A Aᵀ

variable [LinearOrder K] [IsStrictOrderedRing K]

/-- [proved-standard; formal-checked] The Gram form of an invertible move is positive definite. -/
theorem gram_isPosDef2 {A : Matrix (Fin 2) (Fin 2) K} (hA : A.det ≠ 0) : IsPosDef2 (Aᵀ * A) := by
  refine ⟨by rw [transpose_mul, transpose_transpose], ?_, by rw [gram_det]; positivity⟩
  simp only [mul_apply, Fin.sum_univ_two, transpose_apply]
  rw [det_fin_two] at hA
  by_contra h
  push Not at h
  have h0 : A 0 0 = 0 := by nlinarith [sq_nonneg (A 0 0), sq_nonneg (A 1 0)]
  have h1 : A 1 0 = 0 := by nlinarith [sq_nonneg (A 0 0), sq_nonneg (A 1 0)]
  exact hA (by rw [h0, h1]; ring)

/-- [definition] **The polar boost** `P = (AᵀA + |det A|·1)/t`, where `t` stands for the root
`t² = tr AᵀA + 2|det A|`; `|det A|` is already in `K`, so `t` is the only new root. -/
def polarBoost (A : Matrix (Fin 2) (Fin 2) K) (t : K) : Matrix (Fin 2) (Fin 2) K :=
  constraintRoot (Aᵀ * A) |A.det| t

/-- [definition] **The polar turn** `U = A P⁻¹`. -/
def polarTurn (A : Matrix (Fin 2) (Fin 2) K) (t : K) : Matrix (Fin 2) (Fin 2) K :=
  A * (polarBoost A t)⁻¹

/-- [definition] **The left polar boost** `P̃ = (AAᵀ + |det A|·1)/t`, with the same `t`. -/
def polarBoostLeft (A : Matrix (Fin 2) (Fin 2) K) (t : K) : Matrix (Fin 2) (Fin 2) K :=
  constraintRoot (A * Aᵀ) |A.det| t

variable {A : Matrix (Fin 2) (Fin 2) K} {t : K}

omit [IsStrictOrderedRing K] in
/-- [proved-standard; formal-checked] `|det A|² = det AᵀA`. -/
theorem abs_det_sq (A : Matrix (Fin 2) (Fin 2) K) : |A.det| ^ 2 = (Aᵀ * A).det := by
  rw [sq_abs, gram_det]

omit [IsStrictOrderedRing K] in
/-- [proved-standard; formal-checked] **The polar boost squares to the Gram form**: `P² = AᵀA`. -/
theorem polarBoost_mul_self (ht0 : 0 < t) (htt : t ^ 2 = (Aᵀ * A).trace + 2 * |A.det|) :
    polarBoost A t * polarBoost A t = Aᵀ * A :=
  constraintRoot_mul_self ht0.ne' (abs_det_sq A) htt

/-- [proved-standard; formal-checked] **The polar boost is positive definite.** -/
theorem polarBoost_isPosDef2 (hA : A.det ≠ 0) (ht0 : 0 < t)
    (htt : t ^ 2 = (Aᵀ * A).trace + 2 * |A.det|) : IsPosDef2 (polarBoost A t) :=
  constraintRoot_isPosDef2 (by rw [transpose_mul, transpose_transpose]) (abs_pos.mpr hA) (abs_det_sq A)
    ht0 htt

omit [IsStrictOrderedRing K] in
/-- [proved-derived; formal-checked] The polar boost has determinant `|det A|` and trace `t`. -/
theorem polarBoost_det_trace (ht0 : 0 < t) (htt : t ^ 2 = (Aᵀ * A).trace + 2 * |A.det|) :
    (polarBoost A t).det = |A.det| ∧ (polarBoost A t).trace = t :=
  ⟨constraintRoot_det ht0.ne' (abs_det_sq A) htt, constraintRoot_trace ht0.ne' htt⟩

/-- [proved-standard; formal-checked] The polar boost is invertible. -/
theorem polarBoost_isUnit_det (hA : A.det ≠ 0) (ht0 : 0 < t)
    (htt : t ^ 2 = (Aᵀ * A).trace + 2 * |A.det|) : IsUnit (polarBoost A t).det := by
  rw [(polarBoost_det_trace ht0 htt).1]
  exact isUnit_iff_ne_zero.mpr (abs_ne_zero.mpr hA)

/-- [proved-standard; formal-checked] **The move is its turn after its boost**: `A = U P`. -/
theorem polarTurn_mul_polarBoost (hA : A.det ≠ 0) (ht0 : 0 < t)
    (htt : t ^ 2 = (Aᵀ * A).trace + 2 * |A.det|) : polarTurn A t * polarBoost A t = A :=
  nonsing_inv_mul_cancel_right _ A (polarBoost_isUnit_det hA ht0 htt)

/-- [proved-standard; formal-checked] **The polar turn is orthogonal**: `UᵀU = 1`. -/
theorem polarTurn_orthogonal (hA : A.det ≠ 0) (ht0 : 0 < t)
    (htt : t ^ 2 = (Aᵀ * A).trace + 2 * |A.det|) : (polarTurn A t)ᵀ * polarTurn A t = 1 := by
  have hu := polarBoost_isUnit_det hA ht0 htt
  have hPt : (polarBoost A t)ᵀ = polarBoost A t :=
    constraintRoot_transpose (by rw [transpose_mul, transpose_transpose]) _ _
  set P := polarBoost A t with hP
  have hPP : P * P = Aᵀ * A := polarBoost_mul_self ht0 htt
  calc (polarTurn A t)ᵀ * polarTurn A t = P⁻¹ * (Aᵀ * A) * P⁻¹ := by
        rw [polarTurn, ← hP, transpose_mul, transpose_nonsing_inv, hPt, Matrix.mul_assoc,
          Matrix.mul_assoc, Matrix.mul_assoc]
    _ = P⁻¹ * (P * P) * P⁻¹ := by rw [hPP]
    _ = 1 := by
        rw [← Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.one_mul, mul_nonsing_inv _ hu]

/-- [proved-derived; formal-checked] **The turn carries the sign of the move**: `det U · |det A| = det A`. -/
theorem polarTurn_det_mul (hA : A.det ≠ 0) (ht0 : 0 < t)
    (htt : t ^ 2 = (Aᵀ * A).trace + 2 * |A.det|) : (polarTurn A t).det * |A.det| = A.det := by
  rw [← (polarBoost_det_trace ht0 htt).1, ← det_mul, polarTurn_mul_polarBoost hA ht0 htt]

/-- [proved-standard; formal-checked] A move of positive determinant has a proper turn: `det U = 1`. -/
theorem polarTurn_det_of_pos (hA : 0 < A.det) (ht0 : 0 < t)
    (htt : t ^ 2 = (Aᵀ * A).trace + 2 * |A.det|) : (polarTurn A t).det = 1 := by
  have h := polarTurn_det_mul hA.ne' ht0 htt
  rw [abs_of_pos hA] at h
  exact (mul_eq_right₀ hA.ne').mp h

/-- [proved-standard; formal-checked] A move of negative determinant has a reflected turn: `det U = −1`. -/
theorem polarTurn_det_of_neg (hA : A.det < 0) (ht0 : 0 < t)
    (htt : t ^ 2 = (Aᵀ * A).trace + 2 * |A.det|) : (polarTurn A t).det = -1 := by
  have h := polarTurn_det_mul hA.ne ht0 htt
  rw [abs_of_neg hA] at h
  have hA' : A.det ≠ 0 := hA.ne
  field_simp at h
  linear_combination -h

/-- [proved-standard; formal-checked] A turn with `U' P = A` is the polar turn. -/
theorem eq_polarTurn_of_mul {U' : Matrix (Fin 2) (Fin 2) K} (hA : A.det ≠ 0) (ht0 : 0 < t)
    (htt : t ^ 2 = (Aᵀ * A).trace + 2 * |A.det|) (h : U' * polarBoost A t = A) : U' = polarTurn A t := by
  calc U' = U' * polarBoost A t * (polarBoost A t)⁻¹ :=
        (mul_nonsing_inv_cancel_right _ U' (polarBoost_isUnit_det hA ht0 htt)).symm
    _ = polarTurn A t := by rw [h, polarTurn]

/-- [proved-standard; formal-checked] **The polar factors are unique**: an orthogonal `U'` and a positive
definite `P'` with `A = U' P'` are the polar turn and the polar boost. -/
theorem polar_unique {U' P' : Matrix (Fin 2) (Fin 2) K} (hA : A.det ≠ 0) (ht0 : 0 < t)
    (htt : t ^ 2 = (Aᵀ * A).trace + 2 * |A.det|) (hU : U'ᵀ * U' = 1) (hP : IsPosDef2 P')
    (hAUP : A = U' * P') : U' = polarTurn A t ∧ P' = polarBoost A t := by
  have hPP : P' * P' = Aᵀ * A := by
    rw [hAUP, transpose_mul, hP.1, Matrix.mul_assoc, ← Matrix.mul_assoc U'ᵀ, hU, Matrix.one_mul]
  have hP' : P' = polarBoost A t :=
    constraintRoot_unique (abs_pos.mpr hA) (abs_det_sq A) ht0 htt hP hPP
  exact ⟨eq_polarTurn_of_mul hA ht0 htt (by rw [← hP', ← hAUP]), hP'⟩

/-- [proved-derived; formal-checked] **Every polar factorization reads the root**: an orthogonal `U` and a
positive definite `P` with `A = U P` give `(tr P)² = tr AᵀA + 2|det A|`. -/
theorem trace_sq_of_polar {U P : Matrix (Fin 2) (Fin 2) K} (hA : A.det ≠ 0) (hU : Uᵀ * U = 1)
    (hP : IsPosDef2 P) (hAUP : A = U * P) : P.trace ^ 2 = (Aᵀ * A).trace + 2 * |A.det| := by
  have hPP : P * P = Aᵀ * A := by
    rw [hAUP, transpose_mul, hP.1, Matrix.mul_assoc, ← Matrix.mul_assoc Uᵀ, hU, Matrix.one_mul]
  obtain ⟨-, htr⟩ := det_trace_of_mul_self hP (abs_pos.mpr hA) (by rw [hPP, abs_det_sq])
  rw [htr, hPP]

/-- [proved-derived; formal-checked] **The polar factors live where `t` lives**: an invertible move has an
orthogonal and positive definite factorization over `K` if and only if `K` holds a positive `t` with
`t² = tr AᵀA + 2|det A|`. -/
theorem exists_polar_iff (hA : A.det ≠ 0) :
    (∃ U P : Matrix (Fin 2) (Fin 2) K, Uᵀ * U = 1 ∧ IsPosDef2 P ∧ A = U * P) ↔
      ∃ t : K, 0 < t ∧ t ^ 2 = (Aᵀ * A).trace + 2 * |A.det| := by
  constructor
  · rintro ⟨U, P, hU, hP, hAUP⟩
    exact ⟨P.trace, hP.trace_pos, trace_sq_of_polar hA hU hP hAUP⟩
  · rintro ⟨t, ht0, htt⟩
    exact ⟨polarTurn A t, polarBoost A t, polarTurn_orthogonal hA ht0 htt,
      polarBoost_isPosDef2 hA ht0 htt, (polarTurn_mul_polarBoost hA ht0 htt).symm⟩

/-- [proved-standard; formal-checked] **The left polar boost is the polar boost carried by the turn**:
`P̃ = U P Uᵀ`, with the same `t`. -/
theorem polarBoostLeft_eq (hA : A.det ≠ 0) (ht0 : 0 < t)
    (htt : t ^ 2 = (Aᵀ * A).trace + 2 * |A.det|) :
    polarBoostLeft A t = polarTurn A t * polarBoost A t * (polarTurn A t)ᵀ := by
  have hU := polarTurn_orthogonal hA ht0 htt
  have hUP := polarTurn_mul_polarBoost hA ht0 htt
  have hPd := polarBoost_isPosDef2 hA ht0 htt
  obtain ⟨hdet, htr⟩ := polarBoost_det_trace ht0 htt
  set U := polarTurn A t
  set P := polarBoost A t
  have hQs : (U * P * Uᵀ)ᵀ = U * P * Uᵀ := by
    rw [transpose_mul, transpose_mul, transpose_transpose, hPd.1, Matrix.mul_assoc]
  have hQt : 0 < (U * P * Uᵀ).trace := by
    rw [trace_mul_comm, ← Matrix.mul_assoc, hU, Matrix.one_mul, htr]
    exact ht0
  have hdU : U.det ^ 2 = 1 := by
    have := congrArg det hU
    rwa [det_mul, det_transpose, det_one, ← sq] at this
  have hQd : 0 < (U * P * Uᵀ).det := by
    rw [det_mul, det_mul, det_transpose, mul_comm (U.det) P.det, mul_assoc, ← sq, hdU, mul_one]
    exact hPd.2.2
  have hQQ : U * P * Uᵀ * (U * P * Uᵀ) = A * Aᵀ := by
    rw [← hUP, transpose_mul, hPd.1]
    calc U * P * Uᵀ * (U * P * Uᵀ) = U * P * (Uᵀ * U) * P * Uᵀ := by
          simp only [Matrix.mul_assoc]
      _ = U * P * (P * Uᵀ) := by rw [hU, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  symm
  refine constraintRoot_unique (abs_pos.mpr hA) (by rw [sq_abs, gram_left_det]) ht0
    (by rw [gram_left_trace]; exact htt) (isPosDef2_of_trace_det hQs hQt hQd) hQQ

/-- [proved-standard; formal-checked] **The left form**: `A = P̃ U`, the same turn after the left boost. -/
theorem polarBoostLeft_mul_polarTurn (hA : A.det ≠ 0) (ht0 : 0 < t)
    (htt : t ^ 2 = (Aᵀ * A).trace + 2 * |A.det|) : polarBoostLeft A t * polarTurn A t = A := by
  rw [polarBoostLeft_eq hA ht0 htt, Matrix.mul_assoc, polarTurn_orthogonal hA ht0 htt, Matrix.mul_one,
    polarTurn_mul_polarBoost hA ht0 htt]

/-- [proved-standard; formal-checked] **The left polar boost is positive definite** with `P̃² = AAᵀ`. -/
theorem polarBoostLeft_isPosDef2 (hA : A.det ≠ 0) (ht0 : 0 < t)
    (htt : t ^ 2 = (Aᵀ * A).trace + 2 * |A.det|) :
    IsPosDef2 (polarBoostLeft A t) ∧ polarBoostLeft A t * polarBoostLeft A t = A * Aᵀ := by
  have hs : |A.det| ^ 2 = (A * Aᵀ).det := by rw [sq_abs, gram_left_det]
  have htt' : t ^ 2 = (A * Aᵀ).trace + 2 * |A.det| := by rw [gram_left_trace]; exact htt
  exact ⟨constraintRoot_isPosDef2 (by rw [transpose_mul, transpose_transpose]) (abs_pos.mpr hA) hs ht0 htt',
    constraintRoot_mul_self ht0.ne' hs htt'⟩

/-- [proved-standard; formal-checked] **The left factors are unique**: a positive definite `P'` and an
orthogonal `U'` with `A = P' U'` are the left polar boost and the polar turn. -/
theorem polar_left_unique {U' P' : Matrix (Fin 2) (Fin 2) K} (hA : A.det ≠ 0) (ht0 : 0 < t)
    (htt : t ^ 2 = (Aᵀ * A).trace + 2 * |A.det|) (hU : U'ᵀ * U' = 1) (hP : IsPosDef2 P')
    (hAPU : A = P' * U') : P' = polarBoostLeft A t ∧ U' = polarTurn A t := by
  have hU' : U' * U'ᵀ = 1 := mul_eq_one_comm.mp hU
  have hPP : P' * P' = A * Aᵀ := by
    rw [hAPU, transpose_mul, hP.1, Matrix.mul_assoc, ← Matrix.mul_assoc U', hU', Matrix.one_mul]
  have hP' : P' = polarBoostLeft A t :=
    constraintRoot_unique (abs_pos.mpr hA) (by rw [sq_abs, gram_left_det]) ht0
      (by rw [gram_left_trace]; exact htt) hP hPP
  refine ⟨hP', ?_⟩
  have hu : IsUnit P'.det := isUnit_iff_ne_zero.mpr hP.2.2.ne'
  have h1 : P'⁻¹ * A = U' := by rw [hAPU, nonsing_inv_mul_cancel_left _ U' hu]
  have h2 : P'⁻¹ * A = polarTurn A t := by
    nth_rewrite 1 [← polarBoostLeft_mul_polarTurn hA ht0 htt]
    rw [← hP', nonsing_inv_mul_cancel_left _ _ hu]
  rw [← h1, h2]

end Polar

/-! ## 4. The factors read as the swing's turn and boost, and the witnesses -/

section Witness

open Holonics.Geometry.Motion

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {A : Matrix (Fin 2) (Fin 2) K} {t : K}

/-- [proved-standard; formal-checked] **A proper move's polar factor is a turn**: for `det A > 0`,
`U = [[x, −y], [y, x]]` with `x = (a + d)/t`, `y = (c − b)/t`. -/
theorem polarTurn_eq_turnChart (hA : 0 < A.det) (ht0 : 0 < t)
    (htt : t ^ 2 = (Aᵀ * A).trace + 2 * |A.det|) :
    polarTurn A t = turnChart ((A 0 0 + A 1 1) / t) ((A 1 0 - A 0 1) / t) := by
  refine (eq_polarTurn_of_mul hA.ne' ht0 htt ?_).symm
  rw [polarBoost, constraintRoot]
  rw [abs_of_pos hA] at htt ⊢
  rw [det_fin_two] at htt ⊢
  simp [trace_fin_two, mul_apply, Fin.sum_univ_two] at htt
  ext i j
  fin_cases i <;> fin_cases j <;> simp [turnChart, mul_apply, Fin.sum_univ_two, one_apply]
  all_goals field_simp
  · linear_combination (-A 0 0) * htt
  · linear_combination (-A 0 1) * htt
  · linear_combination (-A 1 0) * htt
  · linear_combination (-A 1 1) * htt

/-- [proved-standard; formal-checked] The turn's chart lies on the circle: `x² + y² = 1` for `det A > 0`. -/
theorem turnChart_coeff_sq (hA : 0 < A.det) (ht0 : 0 < t)
    (htt : t ^ 2 = (Aᵀ * A).trace + 2 * |A.det|) :
    ((A 0 0 + A 1 1) / t) ^ 2 + ((A 1 0 - A 0 1) / t) ^ 2 = 1 := by
  rw [abs_of_pos hA, det_fin_two] at htt
  simp [trace_fin_two, mul_apply, Fin.sum_univ_two] at htt
  field_simp
  linear_combination (-1 : K) * htt

/-- [proved-standard; formal-checked] **A reversing move's polar factor is a turn after a reflection**: for
`det A < 0`, `U = [[x, −y], [y, x]] · diag(1, −1)` with `x = (a − d)/t`, `y = (b + c)/t`. -/
theorem polarTurn_eq_turnChart_reflect (hA : A.det < 0) (ht0 : 0 < t)
    (htt : t ^ 2 = (Aᵀ * A).trace + 2 * |A.det|) :
    polarTurn A t = turnChart ((A 0 0 - A 1 1) / t) ((A 0 1 + A 1 0) / t) * !![1, 0; 0, -1] := by
  refine (eq_polarTurn_of_mul hA.ne ht0 htt ?_).symm
  rw [polarBoost, constraintRoot]
  rw [abs_of_neg hA] at htt ⊢
  rw [det_fin_two] at htt ⊢
  simp [trace_fin_two, mul_apply, Fin.sum_univ_two] at htt
  ext i j
  fin_cases i <;> fin_cases j <;> simp [turnChart, mul_apply, Fin.sum_univ_two, one_apply]
  all_goals field_simp
  · linear_combination (-A 0 0) * htt
  · linear_combination (-A 0 1) * htt
  · linear_combination (-A 1 0) * htt
  · linear_combination (-A 1 1) * htt

/-- [proved-standard; formal-checked] **A turn has no boost**: an orthogonal `A` has `t = 2`, `P = 1`, `U = A`. -/
theorem polar_of_orthogonal (hA : Aᵀ * A = 1) :
    (2 : K) ^ 2 = (Aᵀ * A).trace + 2 * |A.det| ∧ polarBoost A 2 = 1 ∧ polarTurn A 2 = A := by
  have hd : |A.det| = 1 := by
    have h := abs_det_sq A
    rw [hA, det_one] at h
    exact (sq_eq_sq₀ (abs_nonneg _) zero_le_one).mp (by rw [h, one_pow])
  have hb : polarBoost A 2 = 1 := by
    rw [polarBoost, constraintRoot, hA, hd, one_smul, ← two_smul K (1 : Matrix (Fin 2) (Fin 2) K),
      smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]
  refine ⟨?_, hb, ?_⟩
  · rw [hA, hd, trace_one, Fintype.card_fin]
    norm_num
  · rw [polarTurn, hb, inv_one, Matrix.mul_one]

/-- [proved-standard; formal-checked] The turn chart `[[x, −y], [y, x]]` with `x² + y² = 1` is orthogonal. -/
theorem turnChart_orthogonal {x y : K} (h : x ^ 2 + y ^ 2 = 1) : (turnChart x y)ᵀ * turnChart x y = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [turnChart, mul_apply, Fin.sum_univ_two, one_apply]
  · linear_combination h
  · ring
  · ring
  · linear_combination h

/-- [proved-derived; formal-checked] **A complex multiplier's polar factors**: `k = x + iy` read as
`[[x, −y], [y, x]]`, with `ρ > 0` and `ρ² = x² + y²`, has `t = 2ρ`, `P = ρ·1` and `U` the turn of
`(x/ρ, y/ρ)`: `k = (k/|k|)·|k|`, the root `|k|` carried as `ρ`. -/
theorem turnChart_polar {x y ρ : K} (hρ : 0 < ρ) (h : ρ ^ 2 = x ^ 2 + y ^ 2) :
    (2 * ρ) ^ 2 = ((turnChart x y)ᵀ * turnChart x y).trace + 2 * |(turnChart x y).det| ∧
      polarBoost (turnChart x y) (2 * ρ) = ρ • 1 ∧
      polarTurn (turnChart x y) (2 * ρ) = turnChart (x / ρ) (y / ρ) := by
  have hg : (turnChart x y)ᵀ * turnChart x y = ρ ^ 2 • (1 : Matrix (Fin 2) (Fin 2) K) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [turnChart, mul_apply, Fin.sum_univ_two, one_apply, h] <;> ring
  have hd : (turnChart x y).det = ρ ^ 2 := by
    simp [turnChart, det_fin_two, h]
    ring
  have hdp : 0 < (turnChart x y).det := by rw [hd]; positivity
  have habs : |(turnChart x y).det| = ρ ^ 2 := by rw [abs_of_pos hdp, hd]
  have htt : (2 * ρ) ^ 2 = ((turnChart x y)ᵀ * turnChart x y).trace + 2 * |(turnChart x y).det| := by
    rw [hg, habs]
    simp
    ring
  refine ⟨htt, ?_, ?_⟩
  · rw [polarBoost, constraintRoot, hg, habs, ← add_smul, smul_smul]
    congr 1
    field_simp
    ring
  · have e1 : (turnChart x y 0 0 + turnChart x y 1 1) / (2 * ρ) = x / ρ := by
      simp [turnChart]
      field_simp
      ring
    have e2 : (turnChart x y 1 0 - turnChart x y 0 1) / (2 * ρ) = y / ρ := by
      simp [turnChart]
      field_simp
      ring
    rw [polarTurn_eq_turnChart hdp (by positivity) htt, e1, e2]

/-- [proved-standard; formal-checked] **A boost has no turn**: a positive definite `A` has `t = tr A`,
`P = A`, `U = 1`. -/
theorem polar_of_isPosDef2 (hA : IsPosDef2 A) :
    A.trace ^ 2 = (Aᵀ * A).trace + 2 * |A.det| ∧ polarBoost A A.trace = A ∧ polarTurn A A.trace = 1 := by
  have hd : |A.det| = A.det := abs_of_pos hA.2.2
  have htt : A.trace ^ 2 = (Aᵀ * A).trace + 2 * |A.det| := by
    rw [hA.1, hd, trace_mul_self_fin_two]
    ring
  have hb : polarBoost A A.trace = A :=
    (constraintRoot_unique (abs_pos.mpr hA.2.2.ne') (abs_det_sq A) hA.trace_pos htt hA
      (by rw [hA.1])).symm
  refine ⟨htt, hb, ?_⟩
  rw [polarTurn, hb, mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hA.2.2.ne')]

/-- [proved-standard; formal-checked] **The pure boost `diag(a, 1/a)` has no turn**: for `a > 0`,
`t = a + 1/a`, `P = diag(a, 1/a)` and `U = 1`. -/
theorem boostChart_polar {a : K} (ha : 0 < a) :
    polarBoost (boostChart a) (a + a⁻¹) = boostChart a ∧ polarTurn (boostChart a) (a + a⁻¹) = 1 := by
  have hA : IsPosDef2 (boostChart a) := by
    refine ⟨?_, by simpa [boostChart] using ha, ?_⟩
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [boostChart]
    · simp [boostChart, det_fin_two, ha.ne']
  have htr : (boostChart a).trace = a + a⁻¹ := by simp [boostChart, trace_fin_two]
  obtain ⟨-, hb, hu⟩ := polar_of_isPosDef2 hA
  rw [htr] at hb hu
  exact ⟨hb, hu⟩

/-- [proved-standard; formal-checked] The shear `[[1, 1], [0, 1]]` has determinant one and
`tr AᵀA + 2|det A| = 5`. -/
theorem shear_root_constraint :
    (shearChart (1 : K)).det = 1 ∧
      ((shearChart (1 : K))ᵀ * shearChart 1).trace + 2 * |(shearChart (1 : K)).det| = 5 := by
  have hd : (shearChart (1 : K)).det = 1 := by simp [shearChart, det_fin_two]
  refine ⟨hd, ?_⟩
  rw [hd]
  simp [shearChart, trace_fin_two, mul_apply, Fin.sum_univ_two]
  norm_num

/-- [proved-derived; formal-checked] **The shear's polar factors over `t² = 5`**: for `t > 0` with `t² = 5`,
`P = [[2, 1], [1, 3]]/t` and `U = [[2, 1], [−1, 2]]/t`, the turn chart of `x = 2/t`, `y = −1/t`. -/
theorem shear_polar (ht0 : 0 < t) (htt : t ^ 2 = 5) :
    polarBoost (shearChart (1 : K)) t = t⁻¹ • !![2, 1; 1, 3] ∧
      polarTurn (shearChart (1 : K)) t = turnChart (2 / t) (-1 / t) := by
  obtain ⟨hd, hc⟩ := shear_root_constraint (K := K)
  have htt' : t ^ 2 = ((shearChart (1 : K))ᵀ * shearChart 1).trace +
      2 * |(shearChart (1 : K)).det| := by rw [hc, htt]
  constructor
  · rw [polarBoost, constraintRoot, hd, abs_one]
    congr 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [shearChart, mul_apply, Fin.sum_univ_two, one_apply]
    all_goals norm_num
  · rw [polarTurn_eq_turnChart (by rw [hd]; exact one_pos) ht0 htt']
    simp [shearChart]
    ring_nf

/-- [proved-derived; formal-checked] **Every polar factorization of the shear holds the root of five**:
an orthogonal `U` and positive definite `P` with `[[1, 1], [0, 1]] = U P` have `(tr P)² = 5`. -/
theorem shear_polar_trace_sq {U P : Matrix (Fin 2) (Fin 2) K} (hU : Uᵀ * U = 1) (hP : IsPosDef2 P)
    (h : shearChart (1 : K) = U * P) : P.trace ^ 2 = 5 := by
  obtain ⟨hd, hc⟩ := shear_root_constraint (K := K)
  rw [trace_sq_of_polar (by rw [hd]; exact one_ne_zero) hU hP h, hc]

/-- [proved-standard; formal-checked] Five is not the square of a rational. -/
theorem five_not_isSquare : ¬ IsSquare (5 : ℚ) := by
  rw [Rat.isSquare_ofNat_iff]
  rintro ⟨r, hr⟩
  have : r ≤ 2 := by nlinarith
  interval_cases r <;> omega

/-- [proved-derived; formal-checked] **The shear has no polar factors over `ℚ`**: no orthogonal `U` and
positive definite `P` over the rationals give `[[1, 1], [0, 1]] = U P`. -/
theorem shear_no_rational_polar :
    ¬ ∃ U P : Matrix (Fin 2) (Fin 2) ℚ, Uᵀ * U = 1 ∧ IsPosDef2 P ∧ shearChart 1 = U * P := by
  rintro ⟨U, P, hU, hP, h⟩
  exact five_not_isSquare ⟨P.trace, by rw [← shear_polar_trace_sq hU hP h]; ring⟩

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- [proved-derived; formal-checked] **The shear's Iwasawa factors stay rational**: Motion's `iwasawa` at
`r = 1` reads `[[1, 1], [0, 1]] = 1 · diag(1, 1) · [[1, 1], [0, 1]]`, the turn and the boost trivial. -/
theorem shear_iwasawa : shearChart (1 : K) = turnChart 1 0 * boostChart 1 * shearChart 1 := by
  have h := (iwasawa (K := K) (a := 1) (b := 1) (c := 0) (d := 1) (r := 1) (by ring) (by ring)
    one_ne_zero).1
  show !![(1 : K), 1; 0, 1] = _
  simpa using h

/-- [proved-derived; formal-checked] **One move, two factorizations**: for `ad − bc = 1`, the polar root
`t² = a² + b² + c² + d² + 2` gives `A = U P` with `U` the turn of `x = (a + d)/t`, `y = (c − b)/t`, and
the Iwasawa root `r² = a² + c²` gives Motion's `A = K · diag(r, 1/r) · N`. -/
theorem sl2_polar_and_iwasawa {a b c d r : K} (hdet : a * d - b * c = 1) (hr : r ^ 2 = a ^ 2 + c ^ 2)
    (hr0 : r ≠ 0) (ht0 : 0 < t) (htt : t ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + 2) :
    !![a, b; c, d] = turnChart ((a + d) / t) ((c - b) / t) * polarBoost !![a, b; c, d] t ∧
      !![a, b; c, d] =
        turnChart (a / r) (c / r) * boostChart r * shearChart ((a * b + c * d) / r ^ 2) := by
  have hd : (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    rw [det_fin_two_of]; exact hdet
  have htt' : t ^ 2 = ((!![a, b; c, d])ᵀ * !![a, b; c, d]).trace +
      2 * |(!![a, b; c, d] : Matrix (Fin 2) (Fin 2) K).det| := by
    rw [hd, abs_one, htt]
    simp [trace_fin_two, mul_apply, Fin.sum_univ_two]
    ring
  refine ⟨?_, (iwasawa hdet hr hr0).1⟩
  have h := polarTurn_mul_polarBoost (by rw [hd]; exact one_ne_zero) ht0 htt'
  rw [polarTurn_eq_turnChart (by rw [hd]; exact one_pos) ht0 htt'] at h
  simpa using h.symm

end Witness

/-! ## 5. Over `ℝ`: the roots given by `Real.sqrt`, and Mathlib's positive definite forms -/

section Real

/-- [proved-standard; formal-checked] **Two minors are Mathlib's positive definite form** on a field with the
trivial star: `IsPosDef2 M ↔ M.PosDef`. -/
theorem isPosDef2_iff_posDef {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [StarRing K]
    [TrivialStar K] {M : Matrix (Fin 2) (Fin 2) K} : IsPosDef2 M ↔ M.PosDef := by
  rw [isPosDef2_iff_quadratic, posDef_iff_dotProduct_mulVec, IsHermitian,
    conjTranspose_eq_transpose_of_trivial]
  simp only [star_trivial]

/-- [proved-standard; formal-checked] **The real root**: for positive definite `M` over `ℝ`,
`s = √(det M)` and `t = √(tr M + 2s)` meet the constraints, and `(M + s·1)/t` is positive definite with
square `M`. -/
theorem real_constraintRoot {M : Matrix (Fin 2) (Fin 2) ℝ} (hM : IsPosDef2 M) :
    IsPosDef2 (constraintRoot M √M.det √(M.trace + 2 * √M.det)) ∧
      constraintRoot M √M.det √(M.trace + 2 * √M.det) *
        constraintRoot M √M.det √(M.trace + 2 * √M.det) = M := by
  have hs0 : 0 < √M.det := Real.sqrt_pos.mpr hM.2.2
  have hs : √M.det ^ 2 = M.det := Real.sq_sqrt hM.2.2.le
  have harg : 0 < M.trace + 2 * √M.det := by have := hM.trace_pos; positivity
  have ht0 : 0 < √(M.trace + 2 * √M.det) := Real.sqrt_pos.mpr harg
  have htt : √(M.trace + 2 * √M.det) ^ 2 = M.trace + 2 * √M.det := Real.sq_sqrt harg.le
  exact ⟨constraintRoot_isPosDef2 hM.1 hs0 hs ht0 htt, constraintRoot_mul_self ht0.ne' hs htt⟩

/-- [proved-standard; formal-checked] **One real positive definite root**: a positive definite form over `ℝ`
has one and only one positive definite square root. -/
theorem real_existsUnique_root {M : Matrix (Fin 2) (Fin 2) ℝ} (hM : IsPosDef2 M) :
    ∃! P : Matrix (Fin 2) (Fin 2) ℝ, IsPosDef2 P ∧ P * P = M := by
  have hs0 : 0 < √M.det := Real.sqrt_pos.mpr hM.2.2
  have harg : 0 < M.trace + 2 * √M.det := by have := hM.trace_pos; positivity
  exact existsUnique_root hM.1 hs0 (Real.sq_sqrt hM.2.2.le) (Real.sqrt_pos.mpr harg)
    (Real.sq_sqrt harg.le)

/-- [proved-standard; formal-checked] **The real polar decomposition on two coordinates**: an invertible real
move has one and only one pair of an orthogonal turn `U` and a positive definite boost `P` with `A = U P`. -/
theorem real_existsUnique_polar {A : Matrix (Fin 2) (Fin 2) ℝ} (hA : A.det ≠ 0) :
    ∃! p : Matrix (Fin 2) (Fin 2) ℝ × Matrix (Fin 2) (Fin 2) ℝ,
      p.1ᵀ * p.1 = 1 ∧ IsPosDef2 p.2 ∧ A = p.1 * p.2 := by
  have harg : 0 < (Aᵀ * A).trace + 2 * |A.det| := by
    have := (gram_isPosDef2 hA).trace_pos
    positivity
  have ht0 : 0 < √((Aᵀ * A).trace + 2 * |A.det|) := Real.sqrt_pos.mpr harg
  have htt := Real.sq_sqrt harg.le
  refine ⟨(polarTurn A _, polarBoost A _), ⟨polarTurn_orthogonal hA ht0 htt,
    polarBoost_isPosDef2 hA ht0 htt, (polarTurn_mul_polarBoost hA ht0 htt).symm⟩, ?_⟩
  rintro ⟨U, P⟩ ⟨hU, hP, h⟩
  obtain ⟨h1, h2⟩ := polar_unique hA ht0 htt hU hP h
  exact Prod.ext h1 h2

end Real

/-! ## 6. The complex form: a unitary turn after a Hermitian boost -/

section Complex

open scoped ComplexOrder

/-- [proved-standard; formal-checked] **The complex polar factors by their constraints**: for invertible
complex `A`, real `s > 0` with `s² = |det A|²` and real `t > 0` with `t² = tr AᴴA + 2s`, the boost
`P = (AᴴA + s·1)/t` is positive definite with `P² = AᴴA`, `det P = s`, `tr P = t`, and the turn
`U = A P⁻¹` is unitary with `A = U P`. -/
theorem complex_polar {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.det ≠ 0) {s t : ℝ} (hs0 : 0 < s)
    (hs : s ^ 2 = Complex.normSq A.det) (ht0 : 0 < t) (htt : (t : ℂ) ^ 2 = (Aᴴ * A).trace + 2 * s) :
    (constraintRoot (Aᴴ * A) s t).PosDef ∧
      constraintRoot (Aᴴ * A) s t * constraintRoot (Aᴴ * A) s t = Aᴴ * A ∧
      (constraintRoot (Aᴴ * A) s t).det = s ∧ (constraintRoot (Aᴴ * A) s t).trace = t ∧
      (A * (constraintRoot (Aᴴ * A) s t)⁻¹)ᴴ * (A * (constraintRoot (Aᴴ * A) s t)⁻¹) = 1 ∧
      A * (constraintRoot (Aᴴ * A) s t)⁻¹ * constraintRoot (Aᴴ * A) s t = A := by
  have ht : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht0.ne'
  have hsd : (s : ℂ) ^ 2 = (Aᴴ * A).det := by
    rw [det_mul, det_conjTranspose, mul_comm, Complex.star_def, Complex.mul_conj, ← hs]
    push_cast
    ring
  set P := constraintRoot (Aᴴ * A) (s : ℂ) (t : ℂ) with hPdef
  have hPP : P * P = Aᴴ * A := constraintRoot_mul_self ht hsd htt
  have hdet : P.det = s := constraintRoot_det ht hsd htt
  have hu : IsUnit P.det := by
    rw [hdet]
    exact isUnit_iff_ne_zero.mpr (Complex.ofReal_ne_zero.mpr hs0.ne')
  have hPh : Pᴴ = P := by
    simp [hPdef, constraintRoot, conjTranspose_smul, conjTranspose_add, conjTranspose_mul,
      conjTranspose_conjTranspose, Complex.conj_ofReal]
  have hinj : Function.Injective A.mulVec :=
    mulVec_injective_iff_isUnit.mpr ((isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr hA))
  have hpd : P.PosDef := by
    rw [hPdef, constraintRoot]
    refine PosDef.smul ?_ (inv_pos.mpr (Complex.zero_lt_real.mpr ht0))
    exact (PosDef.conjTranspose_mul_self A hinj).add (PosDef.one.smul (Complex.zero_lt_real.mpr hs0))
  refine ⟨hpd, hPP, hdet, constraintRoot_trace ht htt, ?_, nonsing_inv_mul_cancel_right _ A hu⟩
  calc (A * P⁻¹)ᴴ * (A * P⁻¹) = P⁻¹ * (Aᴴ * A) * P⁻¹ := by
        rw [conjTranspose_mul, conjTranspose_nonsing_inv, hPh, Matrix.mul_assoc, Matrix.mul_assoc,
          Matrix.mul_assoc]
    _ = P⁻¹ * (P * P) * P⁻¹ := by rw [hPP]
    _ = 1 := by
        rw [← Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.one_mul, mul_nonsing_inv _ hu]

end Complex

end Holonics.Geometry.PolarConstraint
