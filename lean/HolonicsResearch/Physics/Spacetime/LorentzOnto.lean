import Mathlib
import HolonicsResearch.Physics.Spacetime.LorentzCover

/-!
# Every restricted Lorentz map is the map of a move of determinant one: `SL(2, ℂ)/±1 → SO⁺(1, 3)` is onto

Source: #410's box for `PSL(2, ℂ) ≅ SO⁺(1, 3)` and the Limits of `Physics/Spacetime/LorentzCover`. That module builds
the map `lorentz A` of a move `X ↦ Aᴴ X A` on the Hermitian chart of `ℝ⁴` (the Einstein record of November 11, §11;
atlas `lorentz.pair-hermitian-signature`), proves that a move of determinant one gives a proper map that keeps the
Minkowski pairing and the direction of time, and that two such moves give one map if and only if they agree up to
sign. It leaves surjectivity and names the construction that closes it: a turn followed by a boost. This file writes
that construction.

[proved-standard; formal-checked] What is proved.

1. **The half-turn about a unit axis** (§1). For a spatial unit `b`, the move `i · herm b` has determinant one
   (`det_halfTurn`), acts on a form as `X ↦ herm b · X · herm b` (`halfTurn_move`), keeps time and sends a spatial
   displacement `w` to `2 (b · w) b − w` (`lorentz_halfTurn`, with `lorentz_halfTurn_e0` and `lorentz_halfTurn_e3`).
2. **The root of a future unit form, in closed form** (§2). For `v` with interval one and positive time,
   `root v = (v + e₀)/√(2 v₀ + 2)` is again a future unit displacement (`mink_root`, `root_time_pos`); its Hermitian
   form squares to the form of `v` (`herm_root_sq`, from `herm_sq`) and has determinant one (`det_herm_root`); and its
   move carries the unit of time to `v` (`lorentz_root`). The form of such a `v` is positive definite (`herm_posDef`),
   so every future unit displacement is reached from the unit of time by a positive Hermitian move of determinant one
   (`exists_boost`), and a Hermitian form of determinant one and positive trace is positive definite with a Hermitian
   square root of determinant one (`exists_herm_sqrt`).
3. **A map that fixes the unit of time is a rotation of space** (§3). A form-keeping map with `Λ e₀ = e₀` keeps every
   displacement's time (`time_kept_of_fix`) and the Euclidean pairing of the three spatial coordinates
   (`space_pairing_kept`); and a move fixes the unit of time if and only if it is unitary (`lorentz_e0_eq_iff`).
4. **Peeling a move off a map** (§4). For a move `A` of determinant one, `lorentz A⁻¹ ∘ Λ` keeps the form when `Λ`
   does (`peeled_keeps`), is proper when `Λ` is (`peeled_det`), and gives `Λ` back under `lorentz A` (`unpeel`, with
   `det_inv_eq_one` and `lorentz_inv_apply`).
5. **A unit axis is reached from the unit of `z`** (§5). Every spatial unit `n` is `lorentz U e₃` for a move `U` of
   determinant one that fixes the unit of time: the half-turn about the bisector `(n + e₃)/|n + e₃|`, or about the `x`
   axis when `n = −e₃` (`exists_turn_to`).
6. **A map that fixes the units of time and of `z` is a turn about `z`** (§6). A proper form-keeping map with
   `Λ e₀ = e₀` and `Λ e₃ = e₃` is `lorentz (turnZ θ)` for some `θ` (`axis_fixed`): the form gives the images of `e₁` and
   `e₂` as an orthonormal pair of the `(x, y)` plane, the determinant (`det_block`) excludes the reflection, and a
   point of the unit circle has an angle (`exists_angle`).
7. **Onto** (§7). A proper form-keeping map that fixes the unit of time is the map of a unitary move of determinant
   one, which is `SU(2) → SO(3)` onto (`rotation_onto`). A proper form-keeping map that keeps the direction of time is
   a turn followed by a boost, `Λ = lorentz B ∘ lorentz U` with `U` unitary and `B` positive Hermitian, both of
   determinant one (`lorentz_polar`); so it is `lorentz (U * B)`, the map of a move of determinant one
   (`lorentz_onto`).
8. **The bijection** (§8). With `restricted` the set of real-linear maps of `ℝ⁴` that keep the Minkowski pairing, have
   determinant one and send the unit of time to positive time, the image of the moves of determinant one is
   `restricted` (`image_lorentz`); the moves of determinant one over the map of `A` are `A` and `−A`, which differ
   (`fibre_lorentz`, `ne_neg_of_det`); so every map of `restricted` has two moves of determinant one over it, a move
   and its negative (`restricted_two_moves`). The set is closed under composition and holds each member's inverse
   (`restricted_comp`, `restricted_inv`), read off the moves.

Existing owners, cited and not repeated: `Physics/Spacetime/LorentzCover` (the chart `herm`/`coords`, `lorentz`,
`herm_lorentz`, `lorentz_mul`, `lorentz_keeps_form_of_det`, `lorentz_inv_comp`, `lorentz_comp_inv`, `lorentz_eq_iff`,
`lorentz_proper_orthochronous`, `det_lorentz_eq_one`, `turnZ` with `lorentz_turnZ` and `det_turnZ`), imported and used.

Limits. `PSL(2, ℂ) ≅ SO⁺(1, 3)` stands here as a bijection of sets with the product law beside it
(`LorentzCover.lorentz_mul`): it is not packaged as a `MulEquiv` from Mathlib's
`Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ` onto a subgroup of the units of the endomorphisms of `ℝ⁴`. With the
move written `Aᴴ X A` the map reverses products, so that packaging goes through `A ↦ lorentz A⁻¹` or the opposite
group. The polar factors of `lorentz_polar` are shown to exist; that they are the only such pair up to the common
sign of `U` and `B` is not proved. `restricted` asks `0 < (Λ e₀) 0`; that this is `1 ≤ (Λ e₀) 0` and that the whole
future cone is kept follow through `image_lorentz` from `LorentzCover` and are not restated. Nothing topological is
touched: that the map is a covering, and that `SL(2, ℂ)` is simply connected, are not statements of this file. The
general boost and turn are reached as the root form and as half-turns composed with `turnZ`; the conjugates of
`boostZ` by turns are not written.

The computational object is the helical pair interaction: a restricted Lorentz map is the move of a contact's undivided
complex pair, a unitary factor (the turn) followed by a positive Hermitian factor (the boost), and the two moves `±A`
over one map are the pair's half-angle carry. Of the winding guide's six general objects this touches the pair (the
move and its two polar factors), the helix (the half-turn about an axis and the turn about `z`, whose whole turn is the
move `−1`) and faces and placement (the chart of a form and the four units a map is read on); cell holonomy, the tube
and the tower thread stay attached.

Consumers: #410's box for `PSL(2, ℂ) ≅ SO⁺(1, 3)`; atlas `lorentz.pair-move-double-cover` and
`lorentz.pair-hermitian-signature`.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.Physics.Spacetime.LorentzOnto

open Matrix Complex
open Holonics.Physics.Spacetime.LorentzCover

/-! ## 1. The four units, and the half-turn about a unit axis -/

/-- [definition] The unit of the `y` axis. -/
def e2 : Fin 4 → ℝ := ![0, 0, 1, 0]

/-- [proved-standard] A displacement is its four coordinates on the four units. -/
theorem decomp (v : Fin 4 → ℝ) : v = v 0 • e0 + v 1 • e1 + v 2 • e2 + v 3 • e3 := by
  ext i
  fin_cases i <;> simp [e0, e1, e2, e3]

/-- [proved-standard] Two linear maps of `ℝ⁴` that agree on the four units agree. -/
theorem lin_ext4 {f g : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ)} (h0 : f e0 = g e0) (h1 : f e1 = g e1)
    (h2 : f e2 = g e2) (h3 : f e3 = g e3) : f = g := by
  refine LinearMap.ext fun v => ?_
  rw [decomp v]
  simp only [map_add, map_smul, h0, h1, h2, h3]

/-- [proved-standard] A displacement is read from its four coordinates. -/
theorem vec4_ext {a b c d : ℝ} {v : Fin 4 → ℝ} (h0 : a = v 0) (h1 : b = v 1) (h2 : c = v 2) (h3 : d = v 3) :
    ![a, b, c, d] = v := by
  subst h0 h1 h2 h3
  ext i
  fin_cases i <;> rfl

/-- [proved-standard] A positive real has a scale whose square inverts it. -/
theorem exists_scale {x : ℝ} (hx : 0 < x) : ∃ r : ℝ, r ^ 2 * x = 1 :=
  ⟨(Real.sqrt x)⁻¹, by rw [inv_pow, Real.sq_sqrt hx.le, inv_mul_cancel₀ hx.ne']⟩

/-- [proved-standard] A Hermitian move carries the unit of time to the form of its own square. -/
theorem lorentz_herm_e0 (b : Fin 4 → ℝ) :
    lorentz (herm b) e0 =
      ![b 0 ^ 2 + b 1 ^ 2 + b 2 ^ 2 + b 3 ^ 2, 2 * b 0 * b 1, 2 * b 0 * b 2, 2 * b 0 * b 3] := by
  have happ : ∀ i, lorentz (herm b) e0 i = coords (herm b * herm b) i := by
    intro i
    show coords ((herm b)ᴴ * herm e0 * herm b) i = _
    rw [herm_e0, Matrix.mul_one, (herm_isHermitian b).eq]
  ext i
  rw [happ]
  fin_cases i
  all_goals
    simp [coords, Matrix.mul_apply, Fin.sum_univ_two]
    ring

/-- [proved-standard] The half-turn's move acts by the Hermitian form of its axis on both sides. -/
theorem halfTurn_move (b : Fin 4 → ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    (I • herm b)ᴴ * X * (I • herm b) = herm b * X * herm b := by
  rw [conjTranspose_smul, (herm_isHermitian b).eq, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  simp

/-- [proved-standard] **The half-turn about a unit axis** `b`: time is kept and a spatial displacement `w` goes to
`2 (b · w) b − w`. -/
theorem lorentz_halfTurn {b : Fin 4 → ℝ} (hb0 : b 0 = 0) (hb : b 1 ^ 2 + b 2 ^ 2 + b 3 ^ 2 = 1) (v : Fin 4 → ℝ) :
    lorentz (I • herm b) v =
      ![v 0, 2 * (b 1 * v 1 + b 2 * v 2 + b 3 * v 3) * b 1 - v 1,
        2 * (b 1 * v 1 + b 2 * v 2 + b 3 * v 3) * b 2 - v 2,
        2 * (b 1 * v 1 + b 2 * v 2 + b 3 * v 3) * b 3 - v 3] := by
  ext i
  fin_cases i
  · show coords ((I • herm b)ᴴ * herm v * (I • herm b)) 0 = _
    rw [halfTurn_move]
    simp [coords, Matrix.mul_apply, Fin.sum_univ_two, hb0]
    linear_combination (v 0) * hb
  · show coords ((I • herm b)ᴴ * herm v * (I • herm b)) 1 = _
    rw [halfTurn_move]
    simp [coords, Matrix.mul_apply, Fin.sum_univ_two, hb0]
    linear_combination (-(v 1)) * hb
  · show coords ((I • herm b)ᴴ * herm v * (I • herm b)) 2 = _
    rw [halfTurn_move]
    simp [coords, Matrix.mul_apply, Fin.sum_univ_two, hb0]
    linear_combination (-(v 2)) * hb
  · show coords ((I • herm b)ᴴ * herm v * (I • herm b)) 3 = _
    rw [halfTurn_move]
    simp [coords, Matrix.mul_apply, Fin.sum_univ_two, hb0]
    linear_combination (-(v 3)) * hb

/-- [proved-standard] The determinant of a map that turns the `(x, y)` plane and fixes `t` and `z`. -/
theorem det_block (a b c d : ℝ) :
    (!![1, 0, 0, 0; 0, a, c, 0; 0, b, d, 0; 0, 0, 0, (1 : ℝ)]).det = a * d - b * c := by
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring

/-- [proved-standard] The half-turn about a unit axis has determinant one. -/
theorem det_halfTurn {b : Fin 4 → ℝ} (hb0 : b 0 = 0) (hb : b 1 ^ 2 + b 2 ^ 2 + b 3 ^ 2 = 1) :
    (I • herm b).det = 1 := by
  have hm : mink b b = -1 := by
    unfold mink
    rw [hb0]
    linear_combination -hb
  rw [Matrix.det_smul, det_herm, hm]
  simp

/-- [proved-standard] The half-turn about a unit axis keeps the unit of time. -/
theorem lorentz_halfTurn_e0 {b : Fin 4 → ℝ} (hb0 : b 0 = 0) (hb : b 1 ^ 2 + b 2 ^ 2 + b 3 ^ 2 = 1) :
    lorentz (I • herm b) e0 = e0 := by
  rw [lorentz_halfTurn hb0 hb]
  ext i
  fin_cases i <;> simp [e0]

/-- [proved-standard] The half-turn about a unit axis `b` carries the unit of `z` to `2 b₃ b − e₃`. -/
theorem lorentz_halfTurn_e3 {b : Fin 4 → ℝ} (hb0 : b 0 = 0) (hb : b 1 ^ 2 + b 2 ^ 2 + b 3 ^ 2 = 1) :
    lorentz (I • herm b) e3 = ![0, 2 * b 3 * b 1, 2 * b 3 * b 2, 2 * b 3 ^ 2 - 1] := by
  rw [lorentz_halfTurn hb0 hb]
  ext i
  fin_cases i
  · simp [e3]
  · simp [e3]
  · simp [e3]
  · simp [e3]
    ring

/-! ## 2. The root of a future unit form, and the boost that reaches it -/

/-- [definition] **The root's coordinates**: for a future unit displacement `v`, the displacement
`(v + e₀) / √(2 v₀ + 2)`, whose Hermitian form squares to `v`'s. -/
def root (v : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![(Real.sqrt (2 * v 0 + 2))⁻¹ * (v 0 + 1), (Real.sqrt (2 * v 0 + 2))⁻¹ * v 1,
    (Real.sqrt (2 * v 0 + 2))⁻¹ * v 2, (Real.sqrt (2 * v 0 + 2))⁻¹ * v 3]

/-- [proved-standard] The root's scale squares to the inverse of `2 v₀ + 2`. -/
theorem root_scale {v : Fin 4 → ℝ} (hv0 : 0 < v 0) :
    ((Real.sqrt (2 * v 0 + 2))⁻¹) ^ 2 * (2 * v 0 + 2) = 1 := by
  have hx : (0 : ℝ) < 2 * v 0 + 2 := by linarith
  rw [inv_pow, Real.sq_sqrt hx.le, inv_mul_cancel₀ hx.ne']

/-- [proved-standard] The root of a future unit displacement is a unit displacement. -/
theorem mink_root {v : Fin 4 → ℝ} (hv : mink v v = 1) (hv0 : 0 < v 0) : mink (root v) (root v) = 1 := by
  have hr := root_scale hv0
  unfold mink at hv
  simp only [mink, root, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  linear_combination hr + ((Real.sqrt (2 * v 0 + 2))⁻¹) ^ 2 * hv

/-- [proved-standard] The root of a future displacement points to the future. -/
theorem root_time_pos {v : Fin 4 → ℝ} (hv0 : 0 < v 0) : 0 < root v 0 := by
  have hx : (0 : ℝ) < 2 * v 0 + 2 := by linarith
  have hs : 0 < (Real.sqrt (2 * v 0 + 2))⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr hx)
  simp only [root, Matrix.cons_val_zero]
  exact mul_pos hs (by linarith)

/-- [proved-standard] **The root's Hermitian move carries the unit of time to `v`.** -/
theorem lorentz_root {v : Fin 4 → ℝ} (hv : mink v v = 1) (hv0 : 0 < v 0) : lorentz (herm (root v)) e0 = v := by
  have hr := root_scale hv0
  unfold mink at hv
  rw [lorentz_herm_e0]
  refine vec4_ext ?_ ?_ ?_ ?_
  · simp only [root, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    linear_combination (v 0) * hr - ((Real.sqrt (2 * v 0 + 2))⁻¹) ^ 2 * hv
  · simp only [root, Matrix.cons_val_zero, Matrix.cons_val_one]
    linear_combination (v 1) * hr
  · simp only [root, Matrix.cons_val_zero, Matrix.cons_val]
    linear_combination (v 2) * hr
  · simp only [root, Matrix.cons_val_zero, Matrix.cons_val]
    linear_combination (v 3) * hr

/-- [proved-standard] A Hermitian form's square is the form of the place it carries the unit of time to. -/
theorem herm_sq (b : Fin 4 → ℝ) : herm b * herm b = herm (lorentz (herm b) e0) := by
  rw [herm_lorentz, herm_e0, Matrix.mul_one, (herm_isHermitian b).eq]

/-- [proved-standard] **The closed-form square root of a future unit form**: the Hermitian form of
`(v + e₀) / √(2 v₀ + 2)` squares to the form of `v`. -/
theorem herm_root_sq {v : Fin 4 → ℝ} (hv : mink v v = 1) (hv0 : 0 < v 0) :
    herm (root v) * herm (root v) = herm v := by
  rw [herm_sq, lorentz_root hv hv0]

/-- [proved-standard] The root's form has determinant one. -/
theorem det_herm_root {v : Fin 4 → ℝ} (hv : mink v v = 1) (hv0 : 0 < v 0) : (herm (root v)).det = 1 := by
  rw [det_herm, mink_root hv hv0]
  simp

open scoped ComplexOrder in
/-- [proved-standard] **The form of a future unit displacement is positive definite**: it is the square of its
root's form, a Hermitian form of determinant one. -/
theorem herm_posDef {v : Fin 4 → ℝ} (hv : mink v v = 1) (hv0 : 0 < v 0) : (herm v).PosDef := by
  have hU : IsUnit (herm (root v)) := by
    rw [Matrix.isUnit_iff_isUnit_det, det_herm_root hv hv0]
    exact isUnit_one
  have h := (Matrix.IsUnit.posDef_star_left_conjugate_iff (x := (1 : Matrix (Fin 2) (Fin 2) ℂ)) hU).mpr
    Matrix.PosDef.one
  rw [Matrix.mul_one, Matrix.star_eq_conjTranspose, (herm_isHermitian _).eq, herm_root_sq hv hv0] at h
  exact h

open scoped ComplexOrder in
/-- [proved-standard] **Every future unit displacement is reached from the unit of time by a positive Hermitian move
of determinant one.** -/
theorem exists_boost {v : Fin 4 → ℝ} (hv : mink v v = 1) (hv0 : 0 < v 0) :
    ∃ B : Matrix (Fin 2) (Fin 2) ℂ, B.PosDef ∧ B.det = 1 ∧ lorentz B e0 = v :=
  ⟨herm (root v), herm_posDef (mink_root hv hv0) (root_time_pos hv0), det_herm_root hv hv0, lorentz_root hv hv0⟩

open scoped ComplexOrder in
/-- [proved-standard] **A Hermitian form of determinant one and positive trace is positive definite and has a
Hermitian square root of determinant one**, the form of the root of its coordinates. -/
theorem exists_herm_sqrt {X : Matrix (Fin 2) (Fin 2) ℂ} (hX : X.IsHermitian) (hdet : X.det = 1)
    (htr : 0 < (X 0 0).re + (X 1 1).re) :
    X.PosDef ∧ ∃ B : Matrix (Fin 2) (Fin 2) ℂ, B.IsHermitian ∧ B.det = 1 ∧ B * B = X := by
  have hv : mink (coords X) (coords X) = 1 := by
    have h : ((mink (coords X) (coords X) : ℝ) : ℂ) = 1 := by rw [← det_herm, herm_coords hX, hdet]
    exact_mod_cast h
  have hv0 : 0 < coords X 0 := by
    show 0 < ((X 0 0).re + (X 1 1).re) / 2
    linarith
  refine ⟨?_, herm (root (coords X)), herm_isHermitian _, det_herm_root hv hv0, ?_⟩
  · have h := herm_posDef hv hv0
    rwa [herm_coords hX] at h
  · rw [herm_root_sq hv hv0, herm_coords hX]

/-! ## 3. A map that fixes the unit of time is a rotation of space -/

/-- [proved-standard] A form-keeping map that fixes the unit of time keeps every displacement's time. -/
theorem time_kept_of_fix {Λ : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ)} (hΛ : ∀ v w, mink (Λ v) (Λ w) = mink v w)
    (h0 : Λ e0 = e0) (v : Fin 4 → ℝ) : (Λ v) 0 = v 0 := by
  have h := hΛ e0 v
  rw [h0] at h
  simpa [mink, e0] using h

/-- [proved-standard] **A form-keeping map that fixes the unit of time is a rotation of space**: it keeps the
Euclidean pairing of the three spatial coordinates. -/
theorem space_pairing_kept {Λ : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ)} (hΛ : ∀ v w, mink (Λ v) (Λ w) = mink v w)
    (h0 : Λ e0 = e0) (v w : Fin 4 → ℝ) :
    (Λ v) 1 * (Λ w) 1 + (Λ v) 2 * (Λ w) 2 + (Λ v) 3 * (Λ w) 3 = v 1 * w 1 + v 2 * w 2 + v 3 * w 3 := by
  have h := hΛ v w
  have hv := time_kept_of_fix hΛ h0 v
  have hw := time_kept_of_fix hΛ h0 w
  unfold mink at h
  rw [hv, hw] at h
  linear_combination -h

/-- [proved-standard] **A move fixes the unit of time if and only if it is unitary.** -/
theorem lorentz_e0_eq_iff (U : Matrix (Fin 2) (Fin 2) ℂ) : lorentz U e0 = e0 ↔ Uᴴ * U = 1 := by
  constructor
  · intro h
    have h1 := herm_lorentz U e0
    rw [h, herm_e0, Matrix.mul_one] at h1
    exact h1.symm
  · intro h
    apply herm_injective
    rw [herm_lorentz, herm_e0, Matrix.mul_one, h]

/-! ## 4. Peeling a move of determinant one off a map -/

/-- [proved-standard] The inverse of a move of determinant one has determinant one. -/
theorem det_inv_eq_one {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.det = 1) : A⁻¹.det = 1 := by
  rw [Matrix.det_nonsing_inv, hA]
  simp

/-- [proved-standard] The inverse move undoes the map at a displacement. -/
theorem lorentz_inv_apply {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.det = 1) (v : Fin 4 → ℝ) :
    lorentz A⁻¹ (lorentz A v) = v := by
  have h := lorentz_inv_comp (A := A) (by rw [hA]; exact isUnit_one)
  exact LinearMap.congr_fun h v

/-- [proved-standard] A map with a move peeled off is recovered by putting the move back. -/
theorem unpeel {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.det = 1) (Λ : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ)) :
    lorentz A ∘ₗ (lorentz A⁻¹ ∘ₗ Λ) = Λ := by
  rw [← LinearMap.comp_assoc, lorentz_comp_inv (by rw [hA]; exact isUnit_one), LinearMap.id_comp]

/-- [proved-standard] Peeling a move of determinant one off a form-keeping map leaves a form-keeping map. -/
theorem peeled_keeps {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.det = 1) {Λ : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ)}
    (hΛ : ∀ v w, mink (Λ v) (Λ w) = mink v w) (v w : Fin 4 → ℝ) :
    mink ((lorentz A⁻¹ ∘ₗ Λ) v) ((lorentz A⁻¹ ∘ₗ Λ) w) = mink v w := by
  rw [LinearMap.comp_apply, LinearMap.comp_apply, lorentz_keeps_form_of_det (det_inv_eq_one hA), hΛ]

/-- [proved-standard] Peeling a move of determinant one off a proper map leaves a proper map. -/
theorem peeled_det {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.det = 1) {Λ : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ)}
    (hdet : LinearMap.det Λ = 1) : LinearMap.det (lorentz A⁻¹ ∘ₗ Λ) = 1 := by
  rw [LinearMap.det_comp, hdet, mul_one, det_lorentz_eq_one (by rw [det_inv_eq_one hA, norm_one])]

/-! ## 5. A unit axis is reached from the unit of `z` by a half-turn -/

/-- [proved-standard] **Every unit axis is reached from the unit of `z` by a move of determinant one that fixes the
unit of time**: the half-turn about the bisector of the two, or about the `x` axis when the axis is `−e₃`. -/
theorem exists_turn_to {n : Fin 4 → ℝ} (hn0 : n 0 = 0) (hn : n 1 ^ 2 + n 2 ^ 2 + n 3 ^ 2 = 1) :
    ∃ U : Matrix (Fin 2) (Fin 2) ℂ, U.det = 1 ∧ lorentz U e0 = e0 ∧ lorentz U e3 = n := by
  by_cases h : n 3 = -1
  · have h12 : n 1 ^ 2 + n 2 ^ 2 = 0 := by
      rw [h] at hn
      linarith
    have h1 : n 1 = 0 := by nlinarith [sq_nonneg (n 1), sq_nonneg (n 2)]
    have h2 : n 2 = 0 := by nlinarith [sq_nonneg (n 1), sq_nonneg (n 2)]
    have hb0 : e1 0 = 0 := by simp [e1]
    have hb : e1 1 ^ 2 + e1 2 ^ 2 + e1 3 ^ 2 = 1 := by simp [e1]
    refine ⟨I • herm e1, det_halfTurn hb0 hb, lorentz_halfTurn_e0 hb0 hb, ?_⟩
    rw [lorentz_halfTurn_e3 hb0 hb]
    ext i
    fin_cases i
    · simp [hn0]
    · simp [e1, h1]
    · simp [e1, h2]
    · simp [e1, h]
  · have hle : -1 ≤ n 3 := by nlinarith [sq_nonneg (n 1), sq_nonneg (n 2), sq_nonneg (n 3 - 1)]
    have hpos : (0 : ℝ) < 2 + 2 * n 3 := by
      rcases lt_or_eq_of_le hle with h' | h'
      · linarith
      · exact absurd h'.symm h
    obtain ⟨r, hr⟩ := exists_scale hpos
    have hb0 : (![0, r * n 1, r * n 2, r * (n 3 + 1)] : Fin 4 → ℝ) 0 = 0 := by simp
    have hb : (![0, r * n 1, r * n 2, r * (n 3 + 1)] : Fin 4 → ℝ) 1 ^ 2 +
        (![0, r * n 1, r * n 2, r * (n 3 + 1)] : Fin 4 → ℝ) 2 ^ 2 +
        (![0, r * n 1, r * n 2, r * (n 3 + 1)] : Fin 4 → ℝ) 3 ^ 2 = 1 := by
      simp only [Matrix.cons_val_one, Matrix.cons_val]
      linear_combination hr + r ^ 2 * hn
    refine ⟨I • herm ![0, r * n 1, r * n 2, r * (n 3 + 1)], det_halfTurn hb0 hb, lorentz_halfTurn_e0 hb0 hb, ?_⟩
    rw [lorentz_halfTurn_e3 hb0 hb]
    refine vec4_ext hn0.symm ?_ ?_ ?_
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      linear_combination (n 1) * hr
    · simp only [Matrix.cons_val]
      linear_combination (n 2) * hr
    · simp only [Matrix.cons_val]
      linear_combination (n 3 + 1) * hr

/-! ## 6. A map that fixes the units of time and of `z` is a turn about `z` -/

/-- [proved-standard] A point of the unit circle has an angle. -/
theorem exists_angle {a b : ℝ} (h : a ^ 2 + b ^ 2 = 1) : ∃ θ : ℝ, Real.cos θ = a ∧ Real.sin θ = b := by
  have hn : ‖(⟨a, b⟩ : ℂ)‖ = 1 := by
    have h2 : ‖(⟨a, b⟩ : ℂ)‖ ^ 2 = 1 := by
      rw [Complex.sq_norm, Complex.normSq_mk]
      linear_combination h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).mp h2
  have hx : (⟨a, b⟩ : ℂ) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hn
    exact zero_ne_one hn
  refine ⟨Complex.arg ⟨a, b⟩, ?_, ?_⟩
  · rw [Complex.cos_arg hx, hn]
    simp
  · rw [Complex.sin_arg, hn]
    simp

/-- [proved-standard] The matrix's map on the four units reads its four columns. -/
theorem toLin'_units (M : Matrix (Fin 4) (Fin 4) ℝ) :
    Matrix.toLin' M e0 = (fun i => M i 0) ∧ Matrix.toLin' M e1 = (fun i => M i 1) ∧
      Matrix.toLin' M e2 = (fun i => M i 2) ∧ Matrix.toLin' M e3 = (fun i => M i 3) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · ext i
      simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_four, e0, e1, e2, e3]

/-- [proved-standard] The turn about `z` on the four units. -/
theorem lorentz_turnZ_units (θ : ℝ) :
    lorentz (turnZ θ) e0 = e0 ∧ lorentz (turnZ θ) e1 = ![0, Real.cos θ, Real.sin θ, 0] ∧
      lorentz (turnZ θ) e2 = ![0, -Real.sin θ, Real.cos θ, 0] ∧ lorentz (turnZ θ) e3 = e3 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · rw [lorentz_turnZ]
      ext i
      fin_cases i <;> simp [e0, e1, e2, e3]

/-- [proved-standard] **A proper form-keeping map that fixes the units of time and of `z` is a turn about `z`.** -/
theorem axis_fixed {Λ : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ)} (hΛ : ∀ v w, mink (Λ v) (Λ w) = mink v w)
    (hdet : LinearMap.det Λ = 1) (h0 : Λ e0 = e0) (h3 : Λ e3 = e3) : ∃ θ : ℝ, Λ = lorentz (turnZ θ) := by
  have p0 : (Λ e1) 0 = 0 := by
    have h := time_kept_of_fix hΛ h0 e1
    rw [h]
    simp [e1]
  have q0 : (Λ e2) 0 = 0 := by
    have h := time_kept_of_fix hΛ h0 e2
    rw [h]
    simp [e2]
  have p3 : (Λ e1) 3 = 0 := by
    have h : mink (Λ e1) e3 = 0 := by
      rw [← h3, hΛ]
      simp [mink, e1, e3]
    simpa [mink, e3] using h
  have q3 : (Λ e2) 3 = 0 := by
    have h : mink (Λ e2) e3 = 0 := by
      rw [← h3, hΛ]
      simp [mink, e2, e3]
    simpa [mink, e3] using h
  have pp : (Λ e1) 1 ^ 2 + (Λ e1) 2 ^ 2 = 1 := by
    have h : mink (Λ e1) (Λ e1) = -1 := by
      rw [hΛ]
      simp [mink, e1]
    unfold mink at h
    rw [p0, p3] at h
    linear_combination -h
  have pq : (Λ e1) 1 * (Λ e2) 1 + (Λ e1) 2 * (Λ e2) 2 = 0 := by
    have h : mink (Λ e1) (Λ e2) = 0 := by
      rw [hΛ]
      simp [mink, e1, e2]
    unfold mink at h
    rw [p0, p3, q3] at h
    linear_combination -h
  have hM : Λ = Matrix.toLin'
      !![1, 0, 0, 0; 0, (Λ e1) 1, (Λ e2) 1, 0; 0, (Λ e1) 2, (Λ e2) 2, 0; 0, 0, 0, (1 : ℝ)] := by
    obtain ⟨t0, t1, t2, t3⟩ := toLin'_units
      !![1, 0, 0, 0; 0, (Λ e1) 1, (Λ e2) 1, 0; 0, (Λ e1) 2, (Λ e2) 2, 0; 0, 0, 0, (1 : ℝ)]
    apply lin_ext4
    · rw [t0, h0]
      ext i
      fin_cases i <;> simp [e0]
    · rw [t1]
      ext i
      fin_cases i
      · simpa using p0
      · simp
      · simp
      · simpa using p3
    · rw [t2]
      ext i
      fin_cases i
      · simpa using q0
      · simp
      · simp
      · simpa using q3
    · rw [t3, h3]
      ext i
      fin_cases i <;> simp [e3]
  have dt : (Λ e1) 1 * (Λ e2) 2 - (Λ e1) 2 * (Λ e2) 1 = 1 := by
    rw [← det_block, ← LinearMap.det_toLin', ← hM]
    exact hdet
  have hq1 : (Λ e2) 1 = -(Λ e1) 2 := by
    linear_combination (-((Λ e2) 1)) * pp + (Λ e1) 1 * pq - (Λ e1) 2 * dt
  have hq2 : (Λ e2) 2 = (Λ e1) 1 := by
    linear_combination (-((Λ e2) 2)) * pp + (Λ e1) 2 * pq + (Λ e1) 1 * dt
  obtain ⟨θ, hc, hs⟩ := exists_angle pp
  obtain ⟨u0, u1, u2, u3⟩ := lorentz_turnZ_units θ
  refine ⟨θ, lin_ext4 ?_ ?_ ?_ ?_⟩
  · rw [h0, u0]
  · rw [u1]
    ext i
    fin_cases i
    · simpa using p0
    · simpa using hc.symm
    · simpa using hs.symm
    · simpa using p3
  · rw [u2]
    ext i
    fin_cases i
    · simpa using q0
    · simpa [hs] using hq1
    · simpa [hc] using hq2
    · simpa using q3
  · rw [h3, u3]

/-! ## 7. Onto: rotations, then the whole group -/

/-- [proved-standard] **`SU(2) → SO(3)` is onto**: every proper form-keeping map that fixes the unit of time is the
map of a unitary move of determinant one. -/
theorem rotation_onto {Λ : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ)} (hΛ : ∀ v w, mink (Λ v) (Λ w) = mink v w)
    (hdet : LinearMap.det Λ = 1) (h0 : Λ e0 = e0) :
    ∃ U : Matrix (Fin 2) (Fin 2) ℂ, U.det = 1 ∧ Uᴴ * U = 1 ∧ lorentz U = Λ := by
  have hn0 : (Λ e3) 0 = 0 := by
    rw [time_kept_of_fix hΛ h0 e3]
    simp [e3]
  have hn : (Λ e3) 1 ^ 2 + (Λ e3) 2 ^ 2 + (Λ e3) 3 ^ 2 = 1 := by
    have h := space_pairing_kept hΛ h0 e3 e3
    have he : e3 1 * e3 1 + e3 2 * e3 2 + e3 3 * e3 3 = (1 : ℝ) := by simp [e3]
    rw [he] at h
    linear_combination h
  obtain ⟨W, hW, hW0, hW3⟩ := exists_turn_to hn0 hn
  have k0 : (lorentz W⁻¹ ∘ₗ Λ) e0 = e0 := by
    rw [LinearMap.comp_apply, h0]
    nth_rewrite 1 [← hW0]
    exact lorentz_inv_apply hW e0
  have k3 : (lorentz W⁻¹ ∘ₗ Λ) e3 = e3 := by
    rw [LinearMap.comp_apply, ← hW3]
    exact lorentz_inv_apply hW e3
  obtain ⟨θ, hθ⟩ := axis_fixed (peeled_keeps hW hΛ) (peeled_det hW hdet) k0 k3
  have hU : lorentz (turnZ θ * W) = Λ := by
    rw [lorentz_mul, ← hθ, unpeel hW]
  refine ⟨turnZ θ * W, ?_, ?_, hU⟩
  · rw [Matrix.det_mul, det_turnZ, hW, mul_one]
  · rw [← lorentz_e0_eq_iff, hU, h0]

open scoped ComplexOrder in
/-- [proved-standard] **Every proper form-keeping map that keeps the direction of time is a turn followed by a
boost**: `Λ = lorentz B ∘ lorentz U` with `U` unitary and `B` positive Hermitian, both of determinant one. -/
theorem lorentz_polar {Λ : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ)} (hΛ : ∀ v w, mink (Λ v) (Λ w) = mink v w)
    (hdet : LinearMap.det Λ = 1) (ht : 0 < (Λ e0) 0) :
    ∃ B U : Matrix (Fin 2) (Fin 2) ℂ, B.PosDef ∧ B.det = 1 ∧ U.det = 1 ∧ Uᴴ * U = 1 ∧
      Λ = lorentz B ∘ₗ lorentz U := by
  have hv : mink (Λ e0) (Λ e0) = 1 := by
    rw [hΛ]
    simp [mink, e0]
  obtain ⟨B, hBh, hB, hB0⟩ := exists_boost hv ht
  have k0 : (lorentz B⁻¹ ∘ₗ Λ) e0 = e0 := by
    rw [LinearMap.comp_apply, ← hB0]
    exact lorentz_inv_apply hB e0
  obtain ⟨U, hU, hUu, hUΛ⟩ := rotation_onto (peeled_keeps hB hΛ) (peeled_det hB hdet) k0
  refine ⟨B, U, hBh, hB, hU, hUu, ?_⟩
  rw [hUΛ, unpeel hB]

/-- [proved-standard] **The map `SL(2, ℂ) → SO⁺(1, 3)` is onto**: every real-linear map of `ℝ⁴` that keeps the
Minkowski form, has determinant one and keeps the direction of time is the map of a move of determinant one. -/
theorem lorentz_onto {Λ : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ)} (hΛ : ∀ v w, mink (Λ v) (Λ w) = mink v w)
    (hdet : LinearMap.det Λ = 1) (ht : 0 < (Λ e0) 0) :
    ∃ A : Matrix (Fin 2) (Fin 2) ℂ, A.det = 1 ∧ lorentz A = Λ := by
  obtain ⟨B, U, -, hB, hU, -, h⟩ := lorentz_polar hΛ hdet ht
  refine ⟨U * B, ?_, ?_⟩
  · rw [Matrix.det_mul, hU, hB, mul_one]
  · rw [lorentz_mul, h]

/-! ## 8. The bijection `SL(2, ℂ)/±1 ≅ SO⁺(1, 3)` -/

/-- [definition] **The restricted Lorentz group** `SO⁺(1, 3)` as a set of maps: form-keeping, proper, and keeping
the direction of time. -/
def restricted : Set ((Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ)) :=
  {Λ | (∀ v w, mink (Λ v) (Λ w) = mink v w) ∧ LinearMap.det Λ = 1 ∧ 0 < (Λ e0) 0}

/-- [proved-standard] **The image of the moves of determinant one is the restricted Lorentz group.** -/
theorem image_lorentz : lorentz '' {A : Matrix (Fin 2) (Fin 2) ℂ | A.det = 1} = restricted := by
  ext Λ
  constructor
  · rintro ⟨A, hA, rfl⟩
    obtain ⟨h1, h2, h3⟩ := lorentz_proper_orthochronous hA
    exact ⟨h1, h2, lt_of_lt_of_le one_pos h3⟩
  · rintro ⟨h1, h2, h3⟩
    obtain ⟨A, hA, rfl⟩ := lorentz_onto h1 h2 h3
    exact ⟨A, hA, rfl⟩

/-- [proved-standard] A move of determinant one differs from its negative. -/
theorem ne_neg_of_det {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.det = 1) : A ≠ -A := by
  intro h
  have h2 : (2 : ℂ) • A = 0 := by
    rw [two_smul]
    nth_rewrite 2 [h]
    exact add_neg_cancel A
  have hA0 : A = 0 := by
    rcases smul_eq_zero.mp h2 with h' | h'
    · exact absurd h' two_ne_zero
    · exact h'
  rw [hA0] at hA
  simp at hA

/-- [proved-standard] **The fibre over a map is a move and its negative**: the moves of determinant one with the
map of `A` are `A` and `−A`, and these two differ. -/
theorem fibre_lorentz {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.det = 1) :
    {B : Matrix (Fin 2) (Fin 2) ℂ | B.det = 1 ∧ lorentz B = lorentz A} = {A, -A} ∧ A ≠ -A := by
  refine ⟨?_, ne_neg_of_det hA⟩
  ext B
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hB, h⟩
    exact (lorentz_eq_iff hB hA).mp h
  · rintro (rfl | rfl)
    · exact ⟨hA, rfl⟩
    · refine ⟨?_, lorentz_neg A⟩
      rw [Matrix.det_neg, hA]
      simp

/-- [proved-standard] **`SL(2, ℂ)/±1 ≅ SO⁺(1, 3)` as a bijection**: every map of the restricted Lorentz group has
a move of determinant one, and the moves over it are that move and its negative, two in number. -/
theorem restricted_two_moves {Λ : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ)} (h : Λ ∈ restricted) :
    ∃ A : Matrix (Fin 2) (Fin 2) ℂ, A.det = 1 ∧ A ≠ -A ∧
      ∀ B : Matrix (Fin 2) (Fin 2) ℂ, (B.det = 1 ∧ lorentz B = Λ) ↔ (B = A ∨ B = -A) := by
  obtain ⟨A, hA, rfl⟩ := lorentz_onto h.1 h.2.1 h.2.2
  refine ⟨A, hA, ne_neg_of_det hA, fun B => ?_⟩
  have hf := (fibre_lorentz hA).1
  have hB : B ∈ {B : Matrix (Fin 2) (Fin 2) ℂ | B.det = 1 ∧ lorentz B = lorentz A} ↔ B ∈ ({A, -A} : Set _) := by
    rw [hf]
  simpa using hB

/-- [proved-standard] **The restricted Lorentz group is closed under composition**, read off the moves: the map of
`B * A` is the composite of the maps of `A` and `B`. -/
theorem restricted_comp {Λ₁ Λ₂ : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ)} (h₁ : Λ₁ ∈ restricted) (h₂ : Λ₂ ∈ restricted) :
    Λ₁ ∘ₗ Λ₂ ∈ restricted := by
  rw [← image_lorentz] at h₁ h₂ ⊢
  obtain ⟨A, hA, rfl⟩ := h₁
  obtain ⟨B, hB, rfl⟩ := h₂
  refine ⟨B * A, ?_, lorentz_mul B A⟩
  show (B * A).det = 1
  rw [Matrix.det_mul, hA, hB, mul_one]

/-- [proved-standard] **Every restricted Lorentz map has its inverse in the group**: the map of the inverse move. -/
theorem restricted_inv {Λ : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ)} (h : Λ ∈ restricted) :
    ∃ Λ' ∈ restricted, Λ' ∘ₗ Λ = LinearMap.id ∧ Λ ∘ₗ Λ' = LinearMap.id := by
  rw [← image_lorentz] at h
  obtain ⟨A, hA, rfl⟩ := h
  have hu : IsUnit A.det := by
    rw [hA]
    exact isUnit_one
  refine ⟨lorentz A⁻¹, ?_, lorentz_inv_comp hu, lorentz_comp_inv hu⟩
  rw [← image_lorentz]
  exact ⟨A⁻¹, det_inv_eq_one hA, rfl⟩

end Holonics.Physics.Spacetime.LorentzOnto
