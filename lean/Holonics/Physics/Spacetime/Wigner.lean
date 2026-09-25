import Holonics.Physics.Spacetime.Boost

/-!
# The Thomas–Wigner rotation is the angle defect of the velocity triangle

[definition] Rebuild step 6, K4 (#75, the Lorentz scope of its comment); null-cone record
(2026-09-24) §1, "non-collinear composition carries winding". In `2 + 1` dimensions (rows and
columns `(t, x, y)`), the boost of Doppler ratio `k` along `x` is `boostX k` and along `y` is
`boostY k`, with `γ = (k + k⁻¹)/2` and `γβ = (k − k⁻¹)/2` (`Boost.gammaOf`, `Boost.gammaBetaOf`).

[proved-derived; formal-checked] Over any ordered field, exactly, for positive Doppler ratios:

* **Collinear boosts are flat.** `boostX k₁ · boostX k₂ = boostX (k₁k₂)` (`boostX_mul_boostX`): the
  Doppler ratios multiply and no rotation appears.
* **Perpendicular boosts carry a rotation.** `boostX k₁ · boostY k₂ = B(w) · R(θ)`
  (`wigner_decomposition`), where `B(w)` is the pure boost whose first column is the composite
  velocity `(γ₁γ₂, γβ₁γ₂, γβ₂)` (`pureBoost`) and `R(θ)` the rotation of the `(x, y)` plane with
  `cos θ = (γ₁ + γ₂)/(1 + γ₁γ₂)`, `sin θ = −γβ₁γβ₂/(1 + γ₁γ₂)` (`wignerCos`, `wignerSin`,
  `wigner_unit`). The loop of boosts `0 → P → W → 0` returns exactly `R(θ)`
  (`loop_returns_rotation`, with `pureBoost_inverse`).
* **The velocity triangle and its angles, read from its vertices.** The triangle has the vertices
  `O = e₀`, `P = boostX k₁ e₀` and `W = (boostX k₁ · boostY k₂) e₀` on the velocity hyperboloid
  (`restVertex`, `vertexP`, `vertexW`). At a vertex `V` the tangent toward `X` is
  `t_{V→X} = X + ⟨V, X⟩V` (`tangent`), the angle's cosine is `⟨t, t′⟩/(|t||t′|)` and its sine the
  unsigned oriented area `|det[V, t, t′]|/(|t||t′|)` (`pairing3`, `orientedArea`). Computed from the
  vertices: the angle at `P` is right (`right_angle_at_P`); at `O`, `|t_OP| = |γβ₁|`,
  `|t_OW| = S` with `S² = γ₁²γ₂² − 1` (`scaleSq`), and the scaled cosine and sine are
  `S cos α = |γβ₁|γ₂`, `S sin α = |γβ₂|` (`rest_vertex_angle`); at `W`, `|t_WP| = |γβ₂|`,
  `|t_WO| = S`, `S cos β = γ₁|γβ₂|`, `S sin β = |γβ₁|` (`far_vertex_angle`). For every positive
  Doppler ratio the four are nonnegative (`vertexAngles_nonneg`) and each pair lies on the circle of
  radius `S` (`vertexAngles_on_circle`): they are interior angles in `[0, π/2]`.
* **The angle is the defect of the velocity triangle.** With the triangle's orientation
  `σ = sign det[O, P, W] = sign(γβ₁γβ₂)` (`orientedArea_triangle`, `orientation`),
  `S² cos θ = S² sin(α + β)` and `S² sin θ = −σ S² cos(α + β)` (`wigner_angle_is_defect`):
  `θ = −σ(π − (π/2 + α + β))`, the rotation by the angle defect of the triangle, opposite to the
  loop's orientation (Thomas precession is retrograde).
* **A finite exact instance.** At `k₁ = 2`, `k₂ = 3` the rotation is `(cos θ, sin θ) =
  (35/37, −12/37)` (`wigner_two_three`), nontrivial.

[proved-standard] The defect of a hyperbolic triangle of curvature `−1` is its area
(Gauss–Bonnet); `[open]` its formal statement over the velocity hyperboloid, and the general
non-perpendicular composition, are owed (#62). `[open]` The gyration reading of the same return
(`Geometry/HolonicCurvedArcEinstein.gyrationCurvatureReturn`) is not joined to this module; the
join is owed (#62).
-/

noncomputable section

namespace Holonics.Physics.Spacetime.Wigner

open Matrix
open Holonics.Physics.Spacetime.Boost
open Holonics.Physics.CompositeMassEnergy

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- [definition] The boost of Doppler ratio `k` along `x`, on `(t, x, y)`. -/
def boostX (k : K) : Matrix (Fin 3) (Fin 3) K :=
  !![gammaOf k, gammaBetaOf k, 0; gammaBetaOf k, gammaOf k, 0; 0, 0, 1]

/-- [definition] The boost of Doppler ratio `k` along `y`. -/
def boostY (k : K) : Matrix (Fin 3) (Fin 3) K :=
  !![gammaOf k, 0, gammaBetaOf k; 0, 1, 0; gammaBetaOf k, 0, gammaOf k]

/-- [definition] **The pure boost** with first column `(γ, pₓ, p_y)`. -/
def pureBoost (γ px py : K) : Matrix (Fin 3) (Fin 3) K :=
  !![γ, px, py;
    px, 1 + px ^ 2 / (γ + 1), px * py / (γ + 1);
    py, px * py / (γ + 1), 1 + py ^ 2 / (γ + 1)]

/-- [definition] The rotation of the `(x, y)` plane with cosine `c` and sine `s`. -/
def rotation (c s : K) : Matrix (Fin 3) (Fin 3) K := !![1, 0, 0; 0, c, -s; 0, s, c]

/-- [definition] The composite velocity's `γ`, `γβₓ`, `γβ_y`. -/
def compositeGamma (k₁ k₂ : K) : K := gammaOf k₁ * gammaOf k₂
def compositeX (k₁ k₂ : K) : K := gammaBetaOf k₁ * gammaOf k₂
def compositeY (k₂ : K) : K := gammaBetaOf k₂

/-- [definition] **The Wigner cosine** `(γ₁ + γ₂)/(1 + γ₁γ₂)`. -/
def wignerCos (k₁ k₂ : K) : K := (gammaOf k₁ + gammaOf k₂) / (1 + gammaOf k₁ * gammaOf k₂)

/-- [definition] **The Wigner sine** `−γβ₁γβ₂/(1 + γ₁γ₂)`. -/
def wignerSin (k₁ k₂ : K) : K := -(gammaBetaOf k₁ * gammaBetaOf k₂) / (1 + gammaOf k₁ * gammaOf k₂)

theorem gammaOf_pos {k : K} (hk : 0 < k) : 0 < gammaOf k := by
  unfold gammaOf; positivity

/-- [proved-derived; formal-checked] **Collinear boosts compose without rotation.** -/
theorem boostX_mul_boostX {k₁ k₂ : K} (h₁ : 0 < k₁) (h₂ : 0 < k₂) :
    boostX k₁ * boostX k₂ = boostX (k₁ * k₂) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [boostX, Matrix.mul_apply, Fin.sum_univ_three, gammaOf, gammaBetaOf] <;>
    field_simp <;> ring

/-- [proved-derived; formal-checked] **The Wigner decomposition**: two perpendicular boosts are a
pure boost to the composite velocity followed by a rotation. -/
theorem wigner_decomposition {k₁ k₂ : K} (h₁ : 0 < k₁) (h₂ : 0 < k₂) :
    boostX k₁ * boostY k₂ =
      pureBoost (compositeGamma k₁ k₂) (compositeX k₁ k₂) (compositeY k₂) *
        rotation (wignerCos k₁ k₂) (wignerSin k₁ k₂) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [boostX, boostY, pureBoost, rotation, compositeGamma, compositeX, compositeY, wignerCos,
      wignerSin, Matrix.mul_apply, Fin.sum_univ_three, gammaOf, gammaBetaOf] <;>
    field_simp <;> ring

/-- [proved-derived; formal-checked] The Wigner rotation is a rotation: `cos²θ + sin²θ = 1`. -/
theorem wigner_unit {k₁ k₂ : K} (h₁ : 0 < k₁) (h₂ : 0 < k₂) :
    wignerCos k₁ k₂ ^ 2 + wignerSin k₁ k₂ ^ 2 = 1 := by
  have hD : 0 < 1 + gammaOf k₁ * gammaOf k₂ := by
    have := gammaOf_pos h₁; have := gammaOf_pos h₂; positivity
  unfold wignerCos wignerSin
  field_simp
  unfold gammaOf gammaBetaOf
  field_simp
  ring

/-- [proved-derived; formal-checked] The composite pure boost's inverse reverses its velocity. -/
theorem pureBoost_inverse {k₁ k₂ : K} (h₁ : 0 < k₁) (h₂ : 0 < k₂) :
    pureBoost (compositeGamma k₁ k₂) (-compositeX k₁ k₂) (-compositeY k₂) *
      pureBoost (compositeGamma k₁ k₂) (compositeX k₁ k₂) (compositeY k₂) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pureBoost, compositeGamma, compositeX, compositeY, Matrix.mul_apply, Fin.sum_univ_three,
      gammaOf, gammaBetaOf] <;>
    field_simp <;> ring

/-- [proved-derived; formal-checked] **The loop of boosts returns the Wigner rotation**:
`B(w)⁻¹ · boostX k₁ · boostY k₂ = R(θ)`. -/
theorem loop_returns_rotation {k₁ k₂ : K} (h₁ : 0 < k₁) (h₂ : 0 < k₂) :
    pureBoost (compositeGamma k₁ k₂) (-compositeX k₁ k₂) (-compositeY k₂) *
        (boostX k₁ * boostY k₂) = rotation (wignerCos k₁ k₂) (wignerSin k₁ k₂) := by
  rw [wigner_decomposition h₁ h₂, ← Matrix.mul_assoc, pureBoost_inverse h₁ h₂, Matrix.one_mul]

/-! ## The velocity triangle, read from its vertices -/

/-- [definition] The Minkowski pairing on `(t, x, y)`. -/
def pairing3 (a b : Fin 3 → K) : K := -(a 0 * b 0) + a 1 * b 1 + a 2 * b 2

/-- [definition] **The tangent at the vertex `V` toward `X`**: `t_{V→X} = X + ⟨V, X⟩V`, orthogonal
to `V` when `⟨V, V⟩ = −1`. -/
def tangent (V X : Fin 3 → K) : Fin 3 → K := fun i => X i + pairing3 V X * V i

/-- [definition] **The oriented area** `det[V, a, b]` of two tangents at `V`, the triple product
(`orientedArea_eq_det`). -/
def orientedArea (V a b : Fin 3 → K) : K :=
  V 0 * (a 1 * b 2 - a 2 * b 1) - V 1 * (a 0 * b 2 - a 2 * b 0) + V 2 * (a 0 * b 1 - a 1 * b 0)

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem orientedArea_eq_det (V a b : Fin 3 → K) :
    orientedArea V a b = Matrix.det !![V 0, V 1, V 2; a 0, a 1, a 2; b 0, b 1, b 2] := by
  rw [Matrix.det_fin_three]; simp [orientedArea]; ring

/-- [definition] The rest vertex `O = e₀`. -/
def restVertex : Fin 3 → K := ![1, 0, 0]

/-- [definition] The vertex `P`: the rest vertex boosted along `x`. -/
def vertexP (k₁ : K) : Fin 3 → K := boostX k₁ *ᵥ restVertex

/-- [definition] The vertex `W`: the rest vertex carried by the composite. -/
def vertexW (k₁ k₂ : K) : Fin 3 → K := (boostX k₁ * boostY k₂) *ᵥ restVertex

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem vertexP_apply (k₁ : K) : vertexP k₁ = ![gammaOf k₁, gammaBetaOf k₁, 0] := by
  ext i; fin_cases i <;> simp [vertexP, boostX, restVertex, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three]

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem vertexW_apply (k₁ k₂ : K) :
    vertexW k₁ k₂ = ![gammaOf k₁ * gammaOf k₂, gammaBetaOf k₁ * gammaOf k₂, gammaBetaOf k₂] := by
  ext i; fin_cases i <;> simp [vertexW, boostX, boostY, restVertex, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three, Matrix.mul_apply]

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- [proved-derived; formal-checked] The pairing of two tangents at `V`:
`⟨t_{V→X}, t_{V→Y}⟩ = ⟨X, Y⟩ + ⟨V, X⟩⟨V, Y⟩(2 + ⟨V, V⟩)`. -/
theorem pairing3_tangent (V X Y : Fin 3 → K) :
    pairing3 (tangent V X) (tangent V Y) =
      pairing3 X Y + pairing3 V X * pairing3 V Y * (2 + pairing3 V V) := by
  simp only [pairing3, tangent]; ring

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- [proved-derived; formal-checked] The oriented area of the tangents at `V` is that of the
vertices: `det[V, t_{V→X}, t_{V→Y}] = det[V, X, Y]`. -/
theorem orientedArea_tangent (V X Y : Fin 3 → K) :
    orientedArea V (tangent V X) (tangent V Y) = orientedArea V X Y := by
  simp only [orientedArea, tangent]
  ring

/-- [proved-derived; formal-checked] **The vertices' pairings**: each vertex is a unit timelike
event, `⟨O, P⟩ = −γ₁`, `⟨O, W⟩ = −γ₁γ₂`, `⟨P, W⟩ = −γ₂`. -/
theorem vertex_pairings {k₁ k₂ : K} (h₁ : 0 < k₁) (h₂ : 0 < k₂) :
    pairing3 (restVertex : Fin 3 → K) restVertex = -1 ∧
      pairing3 (vertexP k₁) (vertexP k₁) = -1 ∧
      pairing3 (vertexW k₁ k₂) (vertexW k₁ k₂) = -1 ∧
      pairing3 restVertex (vertexP k₁) = -gammaOf k₁ ∧
      pairing3 restVertex (vertexW k₁ k₂) = -(gammaOf k₁ * gammaOf k₂) ∧
      pairing3 (vertexP k₁) (vertexW k₁ k₂) = -gammaOf k₂ ∧
      pairing3 (vertexW k₁ k₂) (vertexP k₁) = -gammaOf k₂ := by
  have hh₁ : gammaOf k₁ ^ 2 - gammaBetaOf k₁ ^ 2 = 1 := multiplicativeScale_lorentz_identity h₁.ne'
  have hh₂ : gammaOf k₂ ^ 2 - gammaBetaOf k₂ ^ 2 = 1 := multiplicativeScale_lorentz_identity h₂.ne'
  simp only [pairing3, vertexP_apply, vertexW_apply, restVertex, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  refine ⟨by ring, ?_, ?_, by ring, by ring, ?_, ?_⟩
  · linear_combination (-1 : K) * hh₁
  · linear_combination (-(gammaOf k₂ ^ 2)) * hh₁ - hh₂
  · linear_combination (-(gammaOf k₂)) * hh₁
  · linear_combination (-(gammaOf k₂)) * hh₁

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- [proved-derived; formal-checked] The triangle's oriented area is `γβ₁γβ₂`. -/
theorem orientedArea_triangle (k₁ k₂ : K) :
    orientedArea restVertex (vertexP k₁) (vertexW k₁ k₂) = gammaBetaOf k₁ * gammaBetaOf k₂ := by
  simp only [orientedArea, vertexP_apply, vertexW_apply, restVertex, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- [proved-derived; formal-checked] The oriented area is cyclic: `det[W, O, P] = det[O, P, W]`. -/
theorem orientedArea_cyclic (A B C : Fin 3 → K) : orientedArea C A B = orientedArea A B C := by
  simp only [orientedArea]
  ring

/-- [definition] `S² = γ_W² − 1 = γ₁²γ₂² − 1`, the squared hyperbolic sine of the hypotenuse. -/
def scaleSq (k₁ k₂ : K) : K := (gammaOf k₁ * gammaOf k₂) ^ 2 - 1

/-- [definition] The interior angles scaled by `S`: `S sin α`, `S cos α`, `S sin β`, `S cos β`,
as `rest_vertex_angle` and `far_vertex_angle` read them from the vertices. -/
def sinAlpha (k₂ : K) : K := |gammaBetaOf k₂|
def cosAlpha (k₁ k₂ : K) : K := |gammaBetaOf k₁| * gammaOf k₂
def sinBeta (k₁ : K) : K := |gammaBetaOf k₁|
def cosBeta (k₁ k₂ : K) : K := gammaOf k₁ * |gammaBetaOf k₂|

/-- [definition] **The triangle's orientation** `σ = sign det[O, P, W]`. -/
def orientation (k₁ k₂ : K) : K :=
  SignType.sign (orientedArea restVertex (vertexP k₁) (vertexW k₁ k₂))

/-- [proved-derived; formal-checked] **The right angle at `P`**: `⟨t_PO, t_PW⟩ = 0`. -/
theorem right_angle_at_P {k₁ k₂ : K} (h₁ : 0 < k₁) (h₂ : 0 < k₂) :
    pairing3 (tangent (vertexP k₁) restVertex) (tangent (vertexP k₁) (vertexW k₁ k₂)) = 0 := by
  obtain ⟨-, hPP, -, hOP, hOW, hPW, -⟩ := vertex_pairings h₁ h₂
  have hPO : pairing3 (vertexP k₁) restVertex = -gammaOf k₁ := by
    rw [← hOP]; simp only [pairing3]; ring
  rw [pairing3_tangent, hPP, hPO, hPW, hOW]
  ring

/-- [proved-derived; formal-checked] **The angle at the rest vertex, read from the vertices**:
`⟨t_OP, t_OW⟩ = |γβ₁| · S cos α`, `|det[O, t_OP, t_OW]| = |γβ₁| · S sin α`, `⟨t_OP, t_OP⟩ = |γβ₁|²`
and `⟨t_OW, t_OW⟩ = S²`. -/
theorem rest_vertex_angle {k₁ k₂ : K} (h₁ : 0 < k₁) (h₂ : 0 < k₂) :
    pairing3 (tangent restVertex (vertexP k₁)) (tangent restVertex (vertexW k₁ k₂)) =
        |gammaBetaOf k₁| * cosAlpha k₁ k₂ ∧
      |orientedArea restVertex (tangent restVertex (vertexP k₁))
          (tangent restVertex (vertexW k₁ k₂))| = |gammaBetaOf k₁| * sinAlpha k₂ ∧
      pairing3 (tangent restVertex (vertexP k₁)) (tangent restVertex (vertexP k₁)) =
        |gammaBetaOf k₁| ^ 2 ∧
      pairing3 (tangent restVertex (vertexW k₁ k₂)) (tangent restVertex (vertexW k₁ k₂)) =
        scaleSq k₁ k₂ := by
  have hh₁ : gammaOf k₁ ^ 2 - gammaBetaOf k₁ ^ 2 = 1 := multiplicativeScale_lorentz_identity h₁.ne'
  obtain ⟨hOO, hPP, hWW, hOP, hOW, hPW, -⟩ := vertex_pairings h₁ h₂
  have hsq : |gammaBetaOf k₁| * (|gammaBetaOf k₁| * gammaOf k₂) =
      gammaBetaOf k₁ ^ 2 * gammaOf k₂ := by
    rw [← mul_assoc, abs_mul_abs_self]; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [pairing3_tangent, hOO, hOP, hOW, hPW, cosAlpha, hsq]
    linear_combination gammaOf k₂ * hh₁
  · rw [orientedArea_tangent, orientedArea_triangle, sinAlpha, abs_mul]
  · rw [pairing3_tangent, hOO, hOP, hPP, sq_abs]
    linear_combination hh₁
  · rw [pairing3_tangent, hOO, hOW, hWW, scaleSq]
    ring

/-- [proved-derived; formal-checked] **The angle at `W`, read from the vertices**:
`⟨t_WO, t_WP⟩ = |γβ₂| · S cos β`, `|det[W, t_WO, t_WP]| = |γβ₂| · S sin β`, `⟨t_WP, t_WP⟩ = |γβ₂|²`
and `⟨t_WO, t_WO⟩ = S²`. -/
theorem far_vertex_angle {k₁ k₂ : K} (h₁ : 0 < k₁) (h₂ : 0 < k₂) :
    pairing3 (tangent (vertexW k₁ k₂) restVertex) (tangent (vertexW k₁ k₂) (vertexP k₁)) =
        |gammaBetaOf k₂| * cosBeta k₁ k₂ ∧
      |orientedArea (vertexW k₁ k₂) (tangent (vertexW k₁ k₂) restVertex)
          (tangent (vertexW k₁ k₂) (vertexP k₁))| = |gammaBetaOf k₂| * sinBeta k₁ ∧
      pairing3 (tangent (vertexW k₁ k₂) (vertexP k₁)) (tangent (vertexW k₁ k₂) (vertexP k₁)) =
        |gammaBetaOf k₂| ^ 2 ∧
      pairing3 (tangent (vertexW k₁ k₂) restVertex) (tangent (vertexW k₁ k₂) restVertex) =
        scaleSq k₁ k₂ := by
  have hh₂ : gammaOf k₂ ^ 2 - gammaBetaOf k₂ ^ 2 = 1 := multiplicativeScale_lorentz_identity h₂.ne'
  obtain ⟨hOO, hPP, hWW, hOP, hOW, -, hWP⟩ := vertex_pairings h₁ h₂
  have hWO : pairing3 (vertexW k₁ k₂) restVertex = -(gammaOf k₁ * gammaOf k₂) := by
    rw [← hOW]; simp only [pairing3]; ring
  have hsq : |gammaBetaOf k₂| * (gammaOf k₁ * |gammaBetaOf k₂|) =
      gammaOf k₁ * gammaBetaOf k₂ ^ 2 := by
    rw [mul_left_comm, abs_mul_abs_self]; ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [pairing3_tangent, hWW, hOP, hWO, hWP, cosBeta, hsq]
    linear_combination gammaOf k₁ * hh₂
  · rw [orientedArea_tangent, orientedArea_cyclic, orientedArea_triangle, sinBeta, abs_mul,
      mul_comm]
  · rw [pairing3_tangent, hWW, hWP, hPP, sq_abs]
    linear_combination hh₂
  · rw [pairing3_tangent, hWW, hOO, hWO, scaleSq]
    ring

/-- [proved-derived; formal-checked] **The interior angles are in `[0, π/2]`** for every positive
Doppler ratio: the scaled sines and cosines are nonnegative. -/
theorem vertexAngles_nonneg {k₁ k₂ : K} (h₁ : 0 < k₁) (h₂ : 0 < k₂) :
    0 ≤ sinAlpha k₂ ∧ 0 ≤ cosAlpha k₁ k₂ ∧ 0 ≤ sinBeta k₁ ∧ 0 ≤ cosBeta k₁ k₂ := by
  have g₁ := (gammaOf_pos h₁).le
  have g₂ := (gammaOf_pos h₂).le
  exact ⟨abs_nonneg _, mul_nonneg (abs_nonneg _) g₂, abs_nonneg _, mul_nonneg g₁ (abs_nonneg _)⟩

/-- [proved-derived; formal-checked] **Each scaled pair lies on the circle of radius `S`.** -/
theorem vertexAngles_on_circle {k₁ k₂ : K} (h₁ : 0 < k₁) (h₂ : 0 < k₂) :
    sinAlpha k₂ ^ 2 + cosAlpha k₁ k₂ ^ 2 = scaleSq k₁ k₂ ∧
      sinBeta k₁ ^ 2 + cosBeta k₁ k₂ ^ 2 = scaleSq k₁ k₂ := by
  have hh₁ : gammaOf k₁ ^ 2 - gammaBetaOf k₁ ^ 2 = 1 := multiplicativeScale_lorentz_identity h₁.ne'
  have hh₂ : gammaOf k₂ ^ 2 - gammaBetaOf k₂ ^ 2 = 1 := multiplicativeScale_lorentz_identity h₂.ne'
  simp only [sinAlpha, cosAlpha, sinBeta, cosBeta, scaleSq, mul_pow, sq_abs]
  constructor
  · linear_combination (-(gammaOf k₂ ^ 2)) * hh₁ - hh₂
  · linear_combination (-1 : K) * hh₁ - gammaOf k₁ ^ 2 * hh₂

/-- [proved-derived; formal-checked] **The Wigner angle is the oriented defect**:
`S² cos θ = S² sin(α + β)` and `S² sin θ = −σ S² cos(α + β)`, with
`sin(α + β) = sin α cos β + cos α sin β` and `cos(α + β) = cos α cos β − sin α sin β` read on the
scaled interior angles and `σ` the triangle's orientation. -/
theorem wigner_angle_is_defect {k₁ k₂ : K} (h₁ : 0 < k₁) (h₂ : 0 < k₂) :
    wignerCos k₁ k₂ * scaleSq k₁ k₂ =
        sinAlpha k₂ * cosBeta k₁ k₂ + cosAlpha k₁ k₂ * sinBeta k₁ ∧
      wignerSin k₁ k₂ * scaleSq k₁ k₂ =
        -(orientation k₁ k₂ * (cosAlpha k₁ k₂ * cosBeta k₁ k₂ - sinAlpha k₂ * sinBeta k₁)) := by
  have hD : 1 + gammaOf k₁ * gammaOf k₂ ≠ 0 := by
    have := gammaOf_pos h₁; have := gammaOf_pos h₂; positivity
  have hh₁ : gammaOf k₁ ^ 2 - gammaBetaOf k₁ ^ 2 = 1 := multiplicativeScale_lorentz_identity h₁.ne'
  have hh₂ : gammaOf k₂ ^ 2 - gammaBetaOf k₂ ^ 2 = 1 := multiplicativeScale_lorentz_identity h₂.ne'
  have hsign : orientation k₁ k₂ * |gammaBetaOf k₁ * gammaBetaOf k₂| =
      gammaBetaOf k₁ * gammaBetaOf k₂ := by
    rw [orientation, orientedArea_triangle, sign_mul_abs]
  constructor
  · have e : sinAlpha k₂ * cosBeta k₁ k₂ + cosAlpha k₁ k₂ * sinBeta k₁ =
        gammaOf k₁ * gammaBetaOf k₂ ^ 2 + gammaOf k₂ * gammaBetaOf k₁ ^ 2 := by
      simp only [sinAlpha, cosAlpha, sinBeta, cosBeta]
      have a₁ := abs_mul_abs_self (gammaBetaOf k₁)
      have a₂ := abs_mul_abs_self (gammaBetaOf k₂)
      linear_combination gammaOf k₁ * a₂ + gammaOf k₂ * a₁
    rw [e, wignerCos, scaleSq, div_mul_eq_mul_div, div_eq_iff hD]
    linear_combination (1 + gammaOf k₁ * gammaOf k₂) *
      (gammaOf k₁ * hh₂ + gammaOf k₂ * hh₁)
  · have e : cosAlpha k₁ k₂ * cosBeta k₁ k₂ - sinAlpha k₂ * sinBeta k₁ =
        |gammaBetaOf k₁ * gammaBetaOf k₂| * (gammaOf k₁ * gammaOf k₂ - 1) := by
      simp only [sinAlpha, cosAlpha, sinBeta, cosBeta, abs_mul]; ring
    rw [e, ← mul_assoc, hsign, wignerSin, scaleSq, div_mul_eq_mul_div, div_eq_iff hD]
    ring

/-- [proved-derived; formal-checked] **A nontrivial exact rotation**: at `k₁ = 2`, `k₂ = 3`,
`(cos θ, sin θ) = (35/37, −12/37)`. -/
theorem wigner_two_three : wignerCos (2 : ℚ) 3 = 35 / 37 ∧ wignerSin (2 : ℚ) 3 = -12 / 37 := by
  constructor <;> norm_num [wignerCos, wignerSin, gammaOf, gammaBetaOf]

section Audit

#print axioms boostX_mul_boostX
#print axioms wigner_decomposition
#print axioms wigner_unit
#print axioms pureBoost_inverse
#print axioms loop_returns_rotation
#print axioms vertexP_apply
#print axioms vertexW_apply
#print axioms pairing3_tangent
#print axioms orientedArea_tangent
#print axioms vertex_pairings
#print axioms orientedArea_cyclic
#print axioms right_angle_at_P
#print axioms rest_vertex_angle
#print axioms far_vertex_angle
#print axioms vertexAngles_nonneg
#print axioms vertexAngles_on_circle
#print axioms orientedArea_triangle
#print axioms wigner_angle_is_defect
#print axioms wigner_two_three

end Audit

end Holonics.Physics.Spacetime.Wigner
