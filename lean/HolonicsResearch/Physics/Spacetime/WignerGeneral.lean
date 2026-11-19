import Holonics.Physics.Spacetime.Wigner
import Holonics.Geometry.HolonicCurvedArcEinstein
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# Two boosts at any angle return a turn: the general Wigner rotation, its gyration and its area

[definition] Formal obligations #410, the box "Wigner: the Gauss–Bonnet area, non-perpendicular
composition and the gyration join (`Physics/Spacetime/Wigner`)". `Physics/Spacetime/Wigner` proves
the perpendicular case and leaves owed (under #62, whose obligations moved to #410): "the defect of
a hyperbolic triangle of curvature `−1` is its area (Gauss–Bonnet); its formal statement over the
velocity hyperboloid, and the general non-perpendicular composition", and "the gyration reading of
the same return (`Geometry/HolonicCurvedArcEinstein.gyrationCurvatureReturn`)". The null-cone
record `research/records/2026-09-24_THE_NULL_CONE_IS_THE_CONSTITUTIONS_LOCK_AND_CLOSURE_IS_A_RECEIVER_READING.md`
§1 states the claim this file writes: "non-collinear composition carries winding", a Thomas–Wigner
rotation whose angle is the area defect of the velocity triangle, the face of a cell as a holonomy
and the gyration `gyr[a,b]` of `gr.route-curvature`. Atlas rows: `lorentz.thomas-wigner-holonomy`,
`lorentz.wigner-perpendicular-defect`, `lorentz.collinear-flat`, `gr.route-curvature`,
`ym.gyration-curvature`; `lorentz.thomas-half` consumes the finite angle.

The chart is Wigner's: rows and columns `(t, x, y)`, Doppler ratio `k > 0`, `γ = (k + k⁻¹)/2`,
`γβ = (k − k⁻¹)/2`, `boostX`, `boostY`, `pureBoost` and `rotation` from `Physics/Spacetime/Wigner`.
A velocity is also read in the disk chart: `z = γβ (cos φ, sin φ)/(1 + γ)`, of modulus
`tanh(a/2) = (k − 1)/(k + 1)` at rapidity `a = log k` (`halfTanh`, `halfTanh_eq`, `halfTanh_exp`).

## What is proved

[proved-standard; formal-checked] Over any ordered field unless ℝ is named.

1. **Any two boosts compose into a boost and a turn** (`disk_composition`). For disk velocities
   `z₁`, `z₂` the pure boosts satisfy `B(z₁) · B(z₂) = B(z₁ ⊕ z₂) · R(θ)` (`diskBoost`), with the
   Möbius sum `z₁ ⊕ z₂ = (z₁ + z₂)/(1 + z̄₁z₂)` (`mobX`, `mobY`) and, writing `1 + z̄₁z₂ = A + iB`
   and `M = A² + B²`, `cos θ = (A² − B²)/M`, `sin θ = −2AB/M` (`gyrCos`, `gyrSin`); the sum stays in
   the disk, `1 − |z₁ ⊕ z₂|² = (1 − |z₁|²)(1 − |z₂|²)/M` (`mobM_sub`, `mob_den`, `mob_in_disk`), and
   `B(−z) = B(z)⁻¹` (`diskBoost_neg_mul`).
2. **Non-perpendicular composition** (`general_decomposition`). With `boostAlong k₂ c s =
   R(c, s) · boostX k₂ · R(c, −s)`, `c² + s² = 1` (`boostAlong`, `rotation_diskBoost`):
   `boostX k₁ · boostAlong k₂ c s = pureBoost(γ, γβₓ, γβ_y) · R(cos θ, sin θ)`, where the composite
   velocity is `(γ₁γ₂ + γβ₁γβ₂c, γβ₁γ₂ + γ₁γβ₂c, γβ₂s)` (`compGamma`, `compX`, `compY`) and, with
   `τ = γβ₁γβ₂/((1 + γ₁)(1 + γ₂))` (`tau`, `tau_eq`), `cos θ = ((1 + τc)² − τ²s²)/((1 + τc)² + τ²s²)`
   and `sin θ = −2τs(1 + τc)/((1 + τc)² + τ²s²)` (`generalCos`, `generalSin`). The turn is a
   rotation (`general_unit`); Wigner's γ-form holds, `cos θ = N²/D − 1`, `sin θ = −γβ₁γβ₂sN/D`
   with `N = 1 + γ + γ₁ + γ₂`, `D = (1 + γ)(1 + γ₁)(1 + γ₂)` (`general_gamma_form`); the half-angle
   form `sin θ · (1 + τc) = −τs(1 + cos θ)` (`general_half_angle`) reads over ℝ, for every angle
   `θ` of the turn, with `shⱼ = sinh(aⱼ/2)` and `chⱼ = cosh(aⱼ/2)`,
   `tan(θ/2) = −s sh₁ sh₂/(ch₁ ch₂ + c sh₁ sh₂)` (`half_angle_rapidity`). The loop returns the
   turn, `B(w)⁻¹ · boostX k₁ · boostAlong k₂ c s = R(θ)` (`composite_inverse`,
   `general_loop_returns_rotation`). At `c = 0`, `s = 1` everything is Wigner's perpendicular
   statement (`boostAlong_perpendicular`, `general_at_perpendicular`,
   `wigner_decomposition_of_general`); at `s = 0` there is no turn and the composite is a pure
   boost whose ratio is `k₁k₂` or `k₁/k₂` (`general_collinear`, `rotation_one_zero`,
   `collinear_pure_boost`, `collinear_doppler`).
3. **The gyration join** (over ℝ). The open unit disk of `ℂ` (`VelocityDisk`) with Möbius addition
   and the gyration `gyr[a, b] w = ((1 + ab̄)/(1 + āb)) w` (`mobAdd`, `gyrFactor`, `gyrEquiv`) is a
   `Gyrogroup` (`mobiusGyrogroup`: `normSq_mobAdd_lt`, `normSq_gyrFactor`, `mobAdd_assoc`,
   `gyrFactor_loop`). Its sum is the composite of boosts and its gyration the turn:
   `B(a) · B(b) = B(a ⊕ b) · R(gyr[a, b])` for every pair (`op_is_lorentz_composite`, through
   `mobAdd_re_im`, `gyrFactor_re_im`), and on the velocity hyperboloid (`hyperboloidPoint`)
   `gyrationCurvatureReturn a b` acts as that turn (`gyrationCurvatureReturn_apply`,
   `gyration_on_hyperboloid`). For the velocities of `boostX k₁` and `boostAlong k₂ c s`
   (`boostDisk`) the sum is the composite velocity (`op_is_composite_velocity`) and the gyration is
   `(generalCos, generalSin)` (`gyration_is_wigner_rotation`, `gyrationCurvatureReturn_is_wigner`),
   Wigner's `(wignerCos, wignerSin)` when perpendicular (`gyration_perpendicular`); at `k = (2, 3)`
   the return is not flat (`gyration_nontrivial_two_three`). The composite three-velocity is the
   Einstein sum of `(β₁, 0)` and `β₂(c, s)` (`einsteinX`, `einsteinY`,
   `composite_velocity_is_einstein_sum`).
4. **Gauss–Bonnet for the velocity triangle** (over ℝ, rapidities `a₁, a₂ > 0`, the right triangle
   `O, P, W` of `Physics/Spacetime/Wigner` at `k = eᵃ`). The angles `α` at `O` and `β` at `W`
   (`restAngle`, `farAngle`) have sines and cosines `(sinh a₂, sinh a₁ cosh a₂)/S` and
   `(sinh a₁, cosh a₁ sinh a₂)/S`, Wigner's scaled readings, with `S² = cosh²a₁ cosh²a₂ − 1`
   (`hypSinh`, `angles_trig`, `angles_mem`). In geodesic polar coordinates about `O`
   (`polarPoint`) the side `PW` is the curve `r = ρ(θ)`, `tanh ρ cos θ = tanh a₁` (`sideRadius`,
   `cosh_sideRadius`): it lies on the geodesic through `P` and `W` (`side_on_geodesic`), starts at
   `P` and ends at `W` (`side_start`, `side_end`). The area `∫₀^α ∫₀^ρ(θ) sinh r dr dθ`
   (`triangleArea`, `integral_sinh_eq`) is the defect `π/2 − α − β` (`gauss_bonnet`), and with
   `Wigner.wigner_angle_is_defect` the Wigner rotation turns by minus the area,
   `cos θ = cos A`, `sin θ = −sin A` (`wigner_rotation_turns_by_area`): Thomas precession is
   retrograde by the area the velocities enclose.

## What is not claimed

* The area is a definition: the iterated integral in geodesic polar coordinates about `O` with the
  element `sinh r dr dθ`. That this element is the area form the hyperboloid's metric induces, and
  that the polar region is the geodesic triangle as a set, are not proved; the file proves only that
  the region's outer curve runs on the geodesic `PW` from `P` to `W`.
* Gauss–Bonnet is written for the right triangle of perpendicular boosts. For a non-perpendicular
  composition the triangle `O, P, W` has three non-right angles; its angles, and the reading of the
  general turn as its defect and its area, are not written.
* The `Gyrogroup` instance is the Möbius (Poincaré disk) chart of velocity space. Einstein's
  gyrogroup on the velocity ball is not built as an instance, the isomorphism between the two
  charts is not stated, and Einstein's addition is joined only as the composite three-velocity of
  the composition above. Gyrocommutativity is not proved.
* The infinitesimal limit (Thomas precession of an accelerated orbit, `lorentz.thomas-half`) and
  dimensions above `2 + 1` are not touched.

## The computational object

The computational object is the helical pair interaction read as swings: each boost is a swing of
the boost kind, and two boosts whose axes are not aligned compose into one boost and one turn,
boost · boost = boost · turn, the polar factorization of the swing; the turn is what the loop of
boosts returns, and collinear boosts (`s = 0`) return none. Of the winding guide's six general
objects this touches the cell holonomy (the turn is the velocity triangle's holonomy, and
Gauss–Bonnet reads it as the cell's area) and the pair (the Möbius sum and its gyration are the
composite of two velocities and the relative return of their two routes, `gyrationCurvatureReturn`);
the helix (the rapidity `a = log k` as the boost's carry, halved in the disk chart), faces and
placement, the tube and the tower thread stay attached.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.Physics.Spacetime.WignerGeneral

open Matrix
open Holonics.Physics.Spacetime.Boost
open Holonics.Physics.Spacetime.Wigner (boostX boostY pureBoost rotation)

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-! ## Any two boosts, in the disk chart -/

/-- [definition] **The pure boost of the disk velocity `z = (x, y)`**: `pureBoost` at
`(1 + |z|², 2x, 2y)/(1 − |z|²)`. -/
def diskBoost (x y : K) : Matrix (Fin 3) (Fin 3) K :=
  pureBoost ((1 + x ^ 2 + y ^ 2) / (1 - x ^ 2 - y ^ 2)) (2 * x / (1 - x ^ 2 - y ^ 2))
    (2 * y / (1 - x ^ 2 - y ^ 2))

/-- [definition] `A = 1 + x₁x₂ + y₁y₂`, the real part of `1 + z̄₁z₂`. -/
def mobA (x₁ y₁ x₂ y₂ : K) : K := 1 + x₁ * x₂ + y₁ * y₂
/-- [definition] `B = x₁y₂ − y₁x₂`, the imaginary part of `1 + z̄₁z₂`. -/
def mobB (x₁ y₁ x₂ y₂ : K) : K := x₁ * y₂ - y₁ * x₂
/-- [definition] `M = A² + B² = |1 + z̄₁z₂|²`. -/
def mobM (x₁ y₁ x₂ y₂ : K) : K := mobA x₁ y₁ x₂ y₂ ^ 2 + mobB x₁ y₁ x₂ y₂ ^ 2
/-- [definition] The first coordinate of the Möbius sum `z₁ ⊕ z₂ = (z₁ + z₂)/(1 + z̄₁z₂)`. -/
def mobX (x₁ y₁ x₂ y₂ : K) : K :=
  ((x₁ + x₂) * mobA x₁ y₁ x₂ y₂ + (y₁ + y₂) * mobB x₁ y₁ x₂ y₂) / mobM x₁ y₁ x₂ y₂
/-- [definition] The second coordinate of the Möbius sum. -/
def mobY (x₁ y₁ x₂ y₂ : K) : K :=
  ((y₁ + y₂) * mobA x₁ y₁ x₂ y₂ - (x₁ + x₂) * mobB x₁ y₁ x₂ y₂) / mobM x₁ y₁ x₂ y₂
/-- [definition] **The gyration cosine** `(A² − B²)/M`, the real part of `(1 + z₁z̄₂)/(1 + z̄₁z₂)`. -/
def gyrCos (x₁ y₁ x₂ y₂ : K) : K :=
  (mobA x₁ y₁ x₂ y₂ ^ 2 - mobB x₁ y₁ x₂ y₂ ^ 2) / mobM x₁ y₁ x₂ y₂
/-- [definition] **The gyration sine** `−2AB/M`, its imaginary part. -/
def gyrSin (x₁ y₁ x₂ y₂ : K) : K :=
  -(2 * mobA x₁ y₁ x₂ y₂ * mobB x₁ y₁ x₂ y₂) / mobM x₁ y₁ x₂ y₂

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- [proved-standard; formal-checked] `|1 + z̄₁z₂|² − |z₁ + z₂|² = (1 − |z₁|²)(1 − |z₂|²)`. -/
theorem mobM_sub (x₁ y₁ x₂ y₂ : K) :
    mobM x₁ y₁ x₂ y₂ - ((x₁ + x₂) ^ 2 + (y₁ + y₂) ^ 2) =
      (1 - x₁ ^ 2 - y₁ ^ 2) * (1 - x₂ ^ 2 - y₂ ^ 2) := by
  simp only [mobM, mobA, mobB]; ring

/-- [proved-standard; formal-checked] `M > 0` for two disk velocities. -/
theorem mobM_pos {x₁ y₁ x₂ y₂ : K} (h₁ : x₁ ^ 2 + y₁ ^ 2 < 1) (h₂ : x₂ ^ 2 + y₂ ^ 2 < 1) :
    0 < mobM x₁ y₁ x₂ y₂ := by
  have := mobM_sub x₁ y₁ x₂ y₂
  have : 0 < (1 - x₁ ^ 2 - y₁ ^ 2) * (1 - x₂ ^ 2 - y₂ ^ 2) := mul_pos (by linarith) (by linarith)
  nlinarith [sq_nonneg (x₁ + x₂), sq_nonneg (y₁ + y₂)]

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- [proved-standard; formal-checked] `1 − |z₁ ⊕ z₂|² = (1 − |z₁|²)(1 − |z₂|²)/M`. -/
theorem mob_den {x₁ y₁ x₂ y₂ : K} (hM : mobM x₁ y₁ x₂ y₂ ≠ 0) :
    1 - mobX x₁ y₁ x₂ y₂ ^ 2 - mobY x₁ y₁ x₂ y₂ ^ 2 =
      (1 - x₁ ^ 2 - y₁ ^ 2) * (1 - x₂ ^ 2 - y₂ ^ 2) / mobM x₁ y₁ x₂ y₂ := by
  rw [← mobM_sub]
  simp only [mobX, mobY]
  rw [eq_div_iff hM]
  field_simp
  simp only [mobM, mobA, mobB]
  ring

/-- [proved-derived; formal-checked] The disk boost's entries over the one denominator `1 − |z|²`. -/
theorem diskBoost_eq {x y : K} (hd : 1 - x ^ 2 - y ^ 2 ≠ 0) :
    diskBoost x y =
      !![(1 + x ^ 2 + y ^ 2) / (1 - x ^ 2 - y ^ 2), 2 * x / (1 - x ^ 2 - y ^ 2),
          2 * y / (1 - x ^ 2 - y ^ 2);
        2 * x / (1 - x ^ 2 - y ^ 2), 1 + 2 * x ^ 2 / (1 - x ^ 2 - y ^ 2),
          2 * x * y / (1 - x ^ 2 - y ^ 2);
        2 * y / (1 - x ^ 2 - y ^ 2), 2 * x * y / (1 - x ^ 2 - y ^ 2),
          1 + 2 * y ^ 2 / (1 - x ^ 2 - y ^ 2)] := by
  have h2 : (1 + x ^ 2 + y ^ 2) / (1 - x ^ 2 - y ^ 2) + 1 = 2 / (1 - x ^ 2 - y ^ 2) := by
    field_simp; ring
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [diskBoost, pureBoost, h2] <;> simp <;>
    field_simp

/-- [proved-standard; formal-checked] **Any two boosts compose into a boost and a turn**:
`B(z₁)B(z₂) = B(z₁ ⊕ z₂) · R(θ)`. -/
theorem disk_composition {x₁ y₁ x₂ y₂ : K} (h₁ : x₁ ^ 2 + y₁ ^ 2 < 1)
    (h₂ : x₂ ^ 2 + y₂ ^ 2 < 1) :
    diskBoost x₁ y₁ * diskBoost x₂ y₂ =
      diskBoost (mobX x₁ y₁ x₂ y₂) (mobY x₁ y₁ x₂ y₂) *
        rotation (gyrCos x₁ y₁ x₂ y₂) (gyrSin x₁ y₁ x₂ y₂) := by
  have hM := (mobM_pos h₁ h₂).ne'
  have hd₁ : 1 - x₁ ^ 2 - y₁ ^ 2 ≠ 0 := by intro h; linarith
  have hd₂ : 1 - x₂ ^ 2 - y₂ ^ 2 ≠ 0 := by intro h; linarith
  have hw := mob_den hM
  have hdw : 1 - mobX x₁ y₁ x₂ y₂ ^ 2 - mobY x₁ y₁ x₂ y₂ ^ 2 ≠ 0 := by
    rw [hw]; exact div_ne_zero (mul_ne_zero hd₁ hd₂) hM
  have hw' : 1 + mobX x₁ y₁ x₂ y₂ ^ 2 + mobY x₁ y₁ x₂ y₂ ^ 2 =
      2 - (1 - x₁ ^ 2 - y₁ ^ 2) * (1 - x₂ ^ 2 - y₂ ^ 2) / mobM x₁ y₁ x₂ y₂ := by
    rw [← hw]; ring
  rw [diskBoost_eq hd₁, diskBoost_eq hd₂, diskBoost_eq hdw, hw, hw']
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotation, Matrix.mul_apply, Fin.sum_univ_three] <;>
    (try simp only [mobX, mobY, gyrCos, gyrSin]) <;>
    field_simp <;>
    simp only [mobM, mobA, mobB] <;>
    ring


/-! ## A boost along `x` followed by a boost along any direction -/

/-- [definition] **The half-rapidity** `t = γβ/(1 + γ)`, the disk modulus of the boost of ratio `k`. -/
def halfTanh (k : K) : K := gammaBetaOf k / (1 + gammaOf k)

/-- [proved-derived; formal-checked] In the Doppler chart `t = (k − 1)/(k + 1)`. -/
theorem halfTanh_eq {k : K} (hk : 0 < k) : halfTanh k = (k - 1) / (k + 1) := by
  have h1 : (0 : K) < k + 1 := by linarith
  have h2 : 1 + gammaOf k ≠ 0 := by unfold gammaOf; positivity
  unfold halfTanh
  rw [div_eq_div_iff h2 h1.ne']
  unfold gammaOf gammaBetaOf
  field_simp
  ring

/-- [proved-derived; formal-checked] `t² < 1`: the half-rapidity lies in the disk. -/
theorem halfTanh_sq_lt_one {k : K} (hk : 0 < k) : halfTanh k ^ 2 < 1 := by
  rw [halfTanh_eq hk, div_pow, div_lt_one (by positivity)]
  nlinarith

/-- [proved-derived; formal-checked] `1 − t² = 4k/(k + 1)²`. -/
theorem one_sub_halfTanh_sq {k : K} (hk : 0 < k) :
    1 - halfTanh k ^ 2 = 4 * k / (k + 1) ^ 2 := by
  have h1 : (k + 1) ≠ 0 := by intro h; linarith
  rw [halfTanh_eq hk]; field_simp; ring

/-- [proved-standard; formal-checked] `γ = (1 + t²)/(1 − t²)` and `γβ = 2t/(1 − t²)`. -/
theorem gammaOf_halfTanh {k : K} (hk : 0 < k) :
    gammaOf k = (1 + halfTanh k ^ 2) / (1 - halfTanh k ^ 2) ∧
      gammaBetaOf k = 2 * halfTanh k / (1 - halfTanh k ^ 2) := by
  have h1 : (k + 1) ≠ 0 := by intro h; linarith
  rw [one_sub_halfTanh_sq hk, halfTanh_eq hk]
  unfold gammaOf gammaBetaOf
  constructor <;> field_simp <;> ring

/-- [proved-derived; formal-checked] `boostX k` is the disk boost of `(t, 0)`. -/
theorem boostX_eq_diskBoost {k : K} (hk : 0 < k) : boostX k = diskBoost (halfTanh k) 0 := by
  have hd : 1 - halfTanh k ^ 2 ≠ 0 := (sub_pos.2 (halfTanh_sq_lt_one hk)).ne'
  obtain ⟨hg, hb⟩ := gammaOf_halfTanh hk
  rw [diskBoost_eq (by simpa using hd)]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [boostX, hg, hb]
  all_goals field_simp
  ring

/-- [definition] **The boost of ratio `k` along the direction `(c, s)`**: `R(c, s) · boostX k · R(c, −s)`. -/
def boostAlong (k c s : K) : Matrix (Fin 3) (Fin 3) K := rotation c s * boostX k * rotation c (-s)

/-- [proved-standard; formal-checked] A turn carries the disk boost of `(t, 0)` to that of `(tc, ts)`. -/
theorem rotation_diskBoost {t c s : K} (ht : t ^ 2 < 1) (hcs : c ^ 2 + s ^ 2 = 1) :
    rotation c s * diskBoost t 0 * rotation c (-s) = diskBoost (t * c) (t * s) := by
  have hd : 1 - t ^ 2 ≠ 0 := (sub_pos.2 ht).ne'
  have e1 : 1 - (t * c) ^ 2 - (t * s) ^ 2 = 1 - t ^ 2 := by linear_combination (-t ^ 2) * hcs
  have e2 : 1 + (t * c) ^ 2 + (t * s) ^ 2 = 1 + t ^ 2 := by linear_combination (t ^ 2) * hcs
  rw [diskBoost_eq (by simpa using hd), diskBoost_eq (by rw [e1]; exact hd), e1, e2]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotation, Matrix.mul_apply, Fin.sum_univ_three] <;>
    field_simp <;> first | ring1 | linear_combination (1 - t ^ 2) * hcs


/-- [definition] `τ = t₁t₂ = γβ₁γβ₂/((1 + γ₁)(1 + γ₂))`, the product of the half-rapidities. -/
def tau (k₁ k₂ : K) : K := halfTanh k₁ * halfTanh k₂

/-- [definition] The composite velocity's `γ`: `γ₁γ₂ + γβ₁γβ₂c`. -/
def compGamma (k₁ k₂ c : K) : K := gammaOf k₁ * gammaOf k₂ + gammaBetaOf k₁ * gammaBetaOf k₂ * c
/-- [definition] The composite velocity's `γβₓ`: `γβ₁γ₂ + γ₁γβ₂c`. -/
def compX (k₁ k₂ c : K) : K := gammaBetaOf k₁ * gammaOf k₂ + gammaOf k₁ * gammaBetaOf k₂ * c
/-- [definition] The composite velocity's `γβ_y`: `γβ₂s`. -/
def compY (k₂ s : K) : K := gammaBetaOf k₂ * s

/-- [definition] **The general Wigner cosine** `((1 + τc)² − τ²s²)/((1 + τc)² + τ²s²)`. -/
def generalCos (k₁ k₂ c s : K) : K :=
  ((1 + tau k₁ k₂ * c) ^ 2 - (tau k₁ k₂ * s) ^ 2) / ((1 + tau k₁ k₂ * c) ^ 2 + (tau k₁ k₂ * s) ^ 2)
/-- [definition] **The general Wigner sine** `−2τs(1 + τc)/((1 + τc)² + τ²s²)`. -/
def generalSin (k₁ k₂ c s : K) : K :=
  -(2 * (1 + tau k₁ k₂ * c) * (tau k₁ k₂ * s)) /
    ((1 + tau k₁ k₂ * c) ^ 2 + (tau k₁ k₂ * s) ^ 2)

/-- [proved-derived; formal-checked] `τ² < 1`. -/
theorem tau_sq_lt_one {k₁ k₂ : K} (h₁ : 0 < k₁) (h₂ : 0 < k₂) : tau k₁ k₂ ^ 2 < 1 := by
  have a := halfTanh_sq_lt_one h₁
  have b := halfTanh_sq_lt_one h₂
  rw [tau, mul_pow]
  nlinarith [sq_nonneg (halfTanh k₁), sq_nonneg (halfTanh k₂)]

/-- [proved-derived; formal-checked] `1 + τc > 0` for `c² ≤ 1`. -/
theorem one_add_tau_mul_pos {k₁ k₂ c : K} (h₁ : 0 < k₁) (h₂ : 0 < k₂) (hc : c ^ 2 ≤ 1) :
    0 < 1 + tau k₁ k₂ * c := by
  have ht := tau_sq_lt_one h₁ h₂
  have : (tau k₁ k₂ * c) ^ 2 < 1 := by
    rw [mul_pow]; nlinarith [sq_nonneg (tau k₁ k₂), sq_nonneg c]
  have := abs_lt.mp ((sq_lt_one_iff_abs_lt_one _).mp this)
  linarith [this.1]

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- [proved-derived; formal-checked] The disk gyration of `(t₁, 0)` and `t₂(c, s)` is the general Wigner turn.
-/
theorem gyr_specialize (k₁ k₂ c s : K) :
    gyrCos (halfTanh k₁) 0 (halfTanh k₂ * c) (halfTanh k₂ * s) = generalCos k₁ k₂ c s ∧
      gyrSin (halfTanh k₁) 0 (halfTanh k₂ * c) (halfTanh k₂ * s) = generalSin k₁ k₂ c s := by
  constructor <;> simp only [gyrCos, gyrSin, mobA, mobB, mobM, generalCos, generalSin, tau] <;> ring

/-- [proved-derived; formal-checked] The composite in the disk chart:
`boostX k₁ · boostAlong k₂ c s = B(w) · R(θ)`. -/
theorem product_eq_disk {k₁ k₂ c s : K} (h₁ : 0 < k₁) (h₂ : 0 < k₂) (hcs : c ^ 2 + s ^ 2 = 1) :
    boostX k₁ * boostAlong k₂ c s =
      diskBoost (mobX (halfTanh k₁) 0 (halfTanh k₂ * c) (halfTanh k₂ * s))
          (mobY (halfTanh k₁) 0 (halfTanh k₂ * c) (halfTanh k₂ * s)) *
        rotation (generalCos k₁ k₂ c s) (generalSin k₁ k₂ c s) := by
  have ht₁ : halfTanh k₁ ^ 2 + 0 ^ 2 < 1 := by simpa using halfTanh_sq_lt_one h₁
  have ht₂ : (halfTanh k₂ * c) ^ 2 + (halfTanh k₂ * s) ^ 2 < 1 := by
    have := halfTanh_sq_lt_one h₂
    linear_combination this + halfTanh k₂ ^ 2 * hcs
  obtain ⟨gc, gs⟩ := gyr_specialize k₁ k₂ c s
  rw [boostX_eq_diskBoost h₁, boostAlong, boostX_eq_diskBoost h₂,
    rotation_diskBoost (halfTanh_sq_lt_one h₂) hcs, disk_composition ht₁ ht₂, gc, gs]

/-- [proved-derived; formal-checked] The disk boost of the Möbius sum is `pureBoost` at the composite velocity.
-/
theorem composite_column {k₁ k₂ c s : K} (h₁ : 0 < k₁) (h₂ : 0 < k₂) (hcs : c ^ 2 + s ^ 2 = 1) :
    diskBoost (mobX (halfTanh k₁) 0 (halfTanh k₂ * c) (halfTanh k₂ * s))
        (mobY (halfTanh k₁) 0 (halfTanh k₂ * c) (halfTanh k₂ * s)) =
      pureBoost (compGamma k₁ k₂ c) (compX k₁ k₂ c) (compY k₂ s) := by
  have hp := product_eq_disk h₁ h₂ hcs
  set wx := mobX (halfTanh k₁) 0 (halfTanh k₂ * c) (halfTanh k₂ * s)
  set wy := mobY (halfTanh k₁) 0 (halfTanh k₂ * c) (halfTanh k₂ * s)
  have col : ∀ i, (boostX k₁ * boostAlong k₂ c s) i 0 =
      (diskBoost wx wy * rotation (generalCos k₁ k₂ c s) (generalSin k₁ k₂ c s)) i 0 := by
    intro i; rw [hp]
  have c0 := col 0
  have c1 := col 1
  have c2 := col 2
  simp [boostX, boostAlong, rotation, diskBoost, pureBoost, Matrix.mul_apply,
    Fin.sum_univ_three] at c0 c1 c2
  unfold diskBoost
  congr 1
  · rw [compGamma]; linear_combination -c0
  · rw [compX]; linear_combination -c1
  · rw [compY]; linear_combination -c2

/-- [proved-standard; formal-checked] **The general Wigner decomposition**:
`boostX k₁ · boostAlong k₂ c s = B(w) · R(θ)`. -/
theorem general_decomposition {k₁ k₂ c s : K} (h₁ : 0 < k₁) (h₂ : 0 < k₂)
    (hcs : c ^ 2 + s ^ 2 = 1) :
    boostX k₁ * boostAlong k₂ c s =
      pureBoost (compGamma k₁ k₂ c) (compX k₁ k₂ c) (compY k₂ s) *
        rotation (generalCos k₁ k₂ c s) (generalSin k₁ k₂ c s) := by
  rw [product_eq_disk h₁ h₂ hcs, composite_column h₁ h₂ hcs]


/-- [proved-derived; formal-checked] The Wigner denominator `(1 + τc)² + τ²s²` is positive. -/
theorem general_den_pos {k₁ k₂ c s : K} (h₁ : 0 < k₁) (h₂ : 0 < k₂) (hc : c ^ 2 ≤ 1) :
    0 < (1 + tau k₁ k₂ * c) ^ 2 + (tau k₁ k₂ * s) ^ 2 := by
  have := one_add_tau_mul_pos h₁ h₂ hc
  positivity

/-- [proved-standard; formal-checked] The general Wigner turn is a rotation: `cos²θ + sin²θ = 1`. -/
theorem general_unit {k₁ k₂ c s : K} (h₁ : 0 < k₁) (h₂ : 0 < k₂) (hcs : c ^ 2 + s ^ 2 = 1) :
    generalCos k₁ k₂ c s ^ 2 + generalSin k₁ k₂ c s ^ 2 = 1 := by
  have hD := (general_den_pos (c := c) (s := s) h₁ h₂ (by nlinarith [sq_nonneg s])).ne'
  rw [mul_pow] at hD
  unfold generalCos generalSin
  field_simp
  ring

/-- [proved-standard; formal-checked] **The half-angle form** `sin θ · (1 + τc) = −τs · (1 + cos θ)`. -/
theorem general_half_angle (k₁ k₂ c s : K) (h₁ : 0 < k₁) (h₂ : 0 < k₂) (hc : c ^ 2 ≤ 1) :
    generalSin k₁ k₂ c s * (1 + tau k₁ k₂ * c) = -(tau k₁ k₂ * s) * (1 + generalCos k₁ k₂ c s) := by
  have hD := (general_den_pos (s := s) h₁ h₂ hc).ne'
  rw [mul_pow] at hD
  unfold generalCos generalSin
  field_simp
  ring

/-- [proved-derived; formal-checked] In Doppler ratios `τ = (k₁ − 1)(k₂ − 1)/((k₁ + 1)(k₂ + 1))`. -/
theorem tau_eq {k₁ k₂ : K} (h₁ : 0 < k₁) (h₂ : 0 < k₂) :
    tau k₁ k₂ = (k₁ - 1) * (k₂ - 1) / ((k₁ + 1) * (k₂ + 1)) := by
  rw [tau, halfTanh_eq h₁, halfTanh_eq h₂, div_mul_div_comm]

/-- [proved-derived; formal-checked] On the unit circle the Wigner denominator is `1 + 2τc + τ²`. -/
theorem general_den_eq {k₁ k₂ c s : K} (hcs : c ^ 2 + s ^ 2 = 1) :
    (1 + tau k₁ k₂ * c) ^ 2 + (tau k₁ k₂ * s) ^ 2 = 1 + 2 * tau k₁ k₂ * c + tau k₁ k₂ ^ 2 := by
  linear_combination tau k₁ k₂ ^ 2 * hcs

/-- [proved-derived; formal-checked] `1 + γⱼ`, `γβ₁γβ₂`, `1 + γ` and `1 + γ + γ₁ + γ₂` in the half-rapidity
chart. -/
theorem gamma_halfTanh_forms {k₁ k₂ c : K} (h₁ : 0 < k₁) (h₂ : 0 < k₂) :
    1 + gammaOf k₁ = 2 / (1 - halfTanh k₁ ^ 2) ∧ 1 + gammaOf k₂ = 2 / (1 - halfTanh k₂ ^ 2) ∧
      gammaBetaOf k₁ * gammaBetaOf k₂ =
        4 * tau k₁ k₂ / ((1 - halfTanh k₁ ^ 2) * (1 - halfTanh k₂ ^ 2)) ∧
      1 + compGamma k₁ k₂ c =
        2 * (1 + 2 * tau k₁ k₂ * c + tau k₁ k₂ ^ 2) /
          ((1 - halfTanh k₁ ^ 2) * (1 - halfTanh k₂ ^ 2)) ∧
      1 + compGamma k₁ k₂ c + gammaOf k₁ + gammaOf k₂ =
        4 * (1 + tau k₁ k₂ * c) / ((1 - halfTanh k₁ ^ 2) * (1 - halfTanh k₂ ^ 2)) := by
  have d₁ : 1 - halfTanh k₁ ^ 2 ≠ 0 := (sub_pos.2 (halfTanh_sq_lt_one h₁)).ne'
  have d₂ : 1 - halfTanh k₂ ^ 2 ≠ 0 := (sub_pos.2 (halfTanh_sq_lt_one h₂)).ne'
  obtain ⟨g₁, b₁⟩ := gammaOf_halfTanh h₁
  obtain ⟨g₂, b₂⟩ := gammaOf_halfTanh h₂
  simp only [compGamma, tau, g₁, b₁, g₂, b₂]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> field_simp <;> ring

/-- [proved-standard; formal-checked] **Wigner's γ-form**: `cos θ = N²/D − 1`, `sin θ = −γβ₁γβ₂sN/D`. -/
theorem general_gamma_form {k₁ k₂ c s : K} (h₁ : 0 < k₁) (h₂ : 0 < k₂)
    (hcs : c ^ 2 + s ^ 2 = 1) :
    generalCos k₁ k₂ c s =
        (1 + compGamma k₁ k₂ c + gammaOf k₁ + gammaOf k₂) ^ 2 /
          ((1 + compGamma k₁ k₂ c) * (1 + gammaOf k₁) * (1 + gammaOf k₂)) - 1 ∧
      generalSin k₁ k₂ c s =
        -(gammaBetaOf k₁ * gammaBetaOf k₂ * s * (1 + compGamma k₁ k₂ c + gammaOf k₁ + gammaOf k₂)) /
          ((1 + compGamma k₁ k₂ c) * (1 + gammaOf k₁) * (1 + gammaOf k₂)) := by
  have d₁ : 1 - halfTanh k₁ ^ 2 ≠ 0 := (sub_pos.2 (halfTanh_sq_lt_one h₁)).ne'
  have d₂ : 1 - halfTanh k₂ ^ 2 ≠ 0 := (sub_pos.2 (halfTanh_sq_lt_one h₂)).ne'
  have hD := (general_den_pos (c := c) (s := s) h₁ h₂ (by nlinarith [sq_nonneg s])).ne'
  rw [mul_pow] at hD
  obtain ⟨g₁, g₂, bb, hG, hN⟩ := gamma_halfTanh_forms (c := c) h₁ h₂
  rw [← general_den_eq hcs] at hG
  have e : gammaBetaOf k₁ * gammaBetaOf k₂ * s * (1 + compGamma k₁ k₂ c + gammaOf k₁ + gammaOf k₂) =
      gammaBetaOf k₁ * gammaBetaOf k₂ * (s * (1 + compGamma k₁ k₂ c + gammaOf k₁ + gammaOf k₂)) := by
    ring
  unfold generalCos generalSin
  rw [e, hN, hG, g₁, g₂, bb]
  constructor <;> field_simp <;> ring


/-! ## The perpendicular and collinear cases, and the loop -/

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- [proved-derived; formal-checked] Along `(0, 1)` the boost is `boostY`. -/
theorem boostAlong_perpendicular (k : K) : boostAlong k 0 1 = boostY k := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [boostAlong, rotation, boostX, boostY, Matrix.mul_apply, Fin.sum_univ_three]

/-- [proved-derived; formal-checked] **At `c = 0`, `s = 1`** the composite and the turn are Wigner's. -/
theorem general_at_perpendicular {k₁ k₂ : K} (h₁ : 0 < k₁) (h₂ : 0 < k₂) :
    compGamma k₁ k₂ 0 = Wigner.compositeGamma k₁ k₂ ∧ compX k₁ k₂ 0 = Wigner.compositeX k₁ k₂ ∧
      compY k₂ 1 = Wigner.compositeY k₂ ∧ generalCos k₁ k₂ 0 1 = Wigner.wignerCos k₁ k₂ ∧
      generalSin k₁ k₂ 0 1 = Wigner.wignerSin k₁ k₂ := by
  have g₁ := Wigner.gammaOf_pos h₁
  have g₂ := Wigner.gammaOf_pos h₂
  have e₁ : 1 + gammaOf k₁ ≠ 0 := by positivity
  have e₂ : 1 + gammaOf k₂ ≠ 0 := by positivity
  have e₃ : 1 + gammaOf k₁ * gammaOf k₂ ≠ 0 := by positivity
  obtain ⟨hc, hs⟩ := general_gamma_form (c := (0 : K)) (s := 1) h₁ h₂ (by norm_num)
  refine ⟨by simp [compGamma, Wigner.compositeGamma], by simp [compX, Wigner.compositeX],
    by simp [compY, Wigner.compositeY], ?_, ?_⟩
  · rw [hc]; simp only [compGamma, Wigner.wignerCos, mul_zero, add_zero]
    field_simp; ring
  · rw [hs]; simp only [compGamma, Wigner.wignerSin, mul_zero, add_zero, mul_one]
    field_simp; ring

/-- [proved-derived; formal-checked] `Wigner.wigner_decomposition` read off the general decomposition. -/
theorem wigner_decomposition_of_general {k₁ k₂ : K} (h₁ : 0 < k₁) (h₂ : 0 < k₂) :
    boostX k₁ * boostY k₂ =
      pureBoost (Wigner.compositeGamma k₁ k₂) (Wigner.compositeX k₁ k₂) (Wigner.compositeY k₂) *
        rotation (Wigner.wignerCos k₁ k₂) (Wigner.wignerSin k₁ k₂) := by
  obtain ⟨a, b, c, d, e⟩ := general_at_perpendicular h₁ h₂
  rw [← boostAlong_perpendicular, general_decomposition h₁ h₂ (by norm_num), a, b, c, d, e]

/-- [proved-derived; formal-checked] **Collinear boosts carry no turn**: at `s = 0`, `cos θ = 1` and
`sin θ = 0`. -/
theorem general_collinear {k₁ k₂ c : K} (h₁ : 0 < k₁) (h₂ : 0 < k₂) (hc : c ^ 2 = 1) :
    generalCos k₁ k₂ c 0 = 1 ∧ generalSin k₁ k₂ c 0 = 0 := by
  have hP := (one_add_tau_mul_pos h₁ h₂ hc.le).ne'
  constructor
  · simp only [generalCos, mul_zero, sq, sub_zero, add_zero]
    exact div_self (mul_ne_zero hP hP)
  · simp [generalSin]

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- [proved-derived; formal-checked] The turn of cosine `1` and sine `0` is the identity. -/
theorem rotation_one_zero : rotation (1 : K) 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotation]

/-- [proved-standard; formal-checked] At `s = 0` the composite is a pure boost. -/
theorem collinear_pure_boost {k₁ k₂ c : K} (h₁ : 0 < k₁) (h₂ : 0 < k₂) (hc : c ^ 2 = 1) :
    boostX k₁ * boostAlong k₂ c 0 = pureBoost (compGamma k₁ k₂ c) (compX k₁ k₂ c) 0 := by
  obtain ⟨a, b⟩ := general_collinear h₁ h₂ hc
  rw [general_decomposition h₁ h₂ (by simpa using hc), a, b, rotation_one_zero, mul_one, compY,
    mul_zero]

/-- [proved-standard; formal-checked] Parallel Doppler ratios multiply, antiparallel ones divide. -/
theorem collinear_doppler {k₁ k₂ : K} (h₁ : 0 < k₁) (h₂ : 0 < k₂) :
    boostX k₁ * boostAlong k₂ 1 0 = boostX (k₁ * k₂) ∧
      boostX k₁ * boostAlong k₂ (-1) 0 = boostX (k₁ * k₂⁻¹) := by
  have par : boostAlong k₂ 1 0 = boostX k₂ := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [boostAlong, rotation, boostX, Matrix.mul_apply,
      Fin.sum_univ_three]
  have anti : boostAlong k₂ (-1) 0 = boostX k₂⁻¹ := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [boostAlong, rotation, boostX, Matrix.mul_apply,
      Fin.sum_univ_three, gammaOf, gammaBetaOf] <;> ring
  rw [par, anti, Wigner.boostX_mul_boostX h₁ h₂, Wigner.boostX_mul_boostX h₁ (inv_pos.2 h₂)]
  exact ⟨rfl, rfl⟩

/-- [proved-standard; formal-checked] The Möbius sum of two disk velocities lies in the disk. -/
theorem mob_in_disk {x₁ y₁ x₂ y₂ : K} (h₁ : x₁ ^ 2 + y₁ ^ 2 < 1) (h₂ : x₂ ^ 2 + y₂ ^ 2 < 1) :
    mobX x₁ y₁ x₂ y₂ ^ 2 + mobY x₁ y₁ x₂ y₂ ^ 2 < 1 := by
  have hM := mobM_pos h₁ h₂
  have h := mob_den hM.ne'
  have : 0 < (1 - x₁ ^ 2 - y₁ ^ 2) * (1 - x₂ ^ 2 - y₂ ^ 2) / mobM x₁ y₁ x₂ y₂ :=
    div_pos (mul_pos (by linarith) (by linarith)) hM
  linarith

/-- [proved-standard; formal-checked] The disk boost of `−z` inverts that of `z`. -/
theorem diskBoost_neg_mul {x y : K} (h : x ^ 2 + y ^ 2 < 1) :
    diskBoost (-x) (-y) * diskBoost x y = 1 := by
  have hd : 1 - x ^ 2 - y ^ 2 ≠ 0 := by intro e; linarith
  rw [diskBoost_eq hd, diskBoost_eq (by simpa using hd)]
  simp only [neg_sq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three] <;>
    field_simp <;> ring

/-- [proved-derived; formal-checked] The composite pure boost's inverse reverses its velocity. -/
theorem composite_inverse {k₁ k₂ c s : K} (h₁ : 0 < k₁) (h₂ : 0 < k₂) (hcs : c ^ 2 + s ^ 2 = 1) :
    pureBoost (compGamma k₁ k₂ c) (-compX k₁ k₂ c) (-compY k₂ s) *
      pureBoost (compGamma k₁ k₂ c) (compX k₁ k₂ c) (compY k₂ s) = 1 := by
  have hw := composite_column h₁ h₂ hcs
  set wx := mobX (halfTanh k₁) 0 (halfTanh k₂ * c) (halfTanh k₂ * s)
  set wy := mobY (halfTanh k₁) 0 (halfTanh k₂ * c) (halfTanh k₂ * s)
  have hin : wx ^ 2 + wy ^ 2 < 1 := by
    have ht₂ : (halfTanh k₂ * c) ^ 2 + (halfTanh k₂ * s) ^ 2 < 1 := by
      have := halfTanh_sq_lt_one h₂
      linear_combination this + halfTanh k₂ ^ 2 * hcs
    exact mob_in_disk (by simpa using halfTanh_sq_lt_one h₁) ht₂
  have a0 := congrArg (fun m => m 0 0) hw
  have a1 := congrArg (fun m => m 1 0) hw
  have a2 := congrArg (fun m => m 2 0) hw
  simp [diskBoost, pureBoost] at a0 a1 a2
  have hneg : diskBoost (-wx) (-wy) =
      pureBoost (compGamma k₁ k₂ c) (-compX k₁ k₂ c) (-compY k₂ s) := by
    unfold diskBoost
    simp only [neg_sq, mul_neg, neg_div]
    rw [a0, a1, a2]
  rw [← hneg, ← hw, diskBoost_neg_mul hin]

/-- [proved-standard; formal-checked] **The loop returns the general turn**:
`B(w)⁻¹ · boostX k₁ · boostAlong k₂ c s = R(θ)`. -/
theorem general_loop_returns_rotation {k₁ k₂ c s : K} (h₁ : 0 < k₁) (h₂ : 0 < k₂)
    (hcs : c ^ 2 + s ^ 2 = 1) :
    pureBoost (compGamma k₁ k₂ c) (-compX k₁ k₂ c) (-compY k₂ s) * (boostX k₁ * boostAlong k₂ c s) =
      rotation (generalCos k₁ k₂ c s) (generalSin k₁ k₂ c s) := by
  rw [general_decomposition h₁ h₂ hcs, ← Matrix.mul_assoc, composite_inverse h₁ h₂ hcs,
    Matrix.one_mul]


/-! ## The half-angle form in rapidities -/

/-- [proved-standard; formal-checked] At `k = eᵃ` the half-rapidity is `tanh(a/2)`. -/
theorem halfTanh_exp (a : ℝ) : halfTanh (Real.exp a) = Real.tanh (a / 2) := by
  have e : Real.exp a = Real.exp (a / 2) * Real.exp (a / 2) := by
    rw [← Real.exp_add]; ring_nf
  have hp := Real.exp_pos (a / 2)
  rw [halfTanh_eq (Real.exp_pos a), Real.tanh_eq, Real.exp_neg, e]
  field_simp

/-- [proved-standard; formal-checked] **The classical half-angle form** of the turn in half rapidities. -/
theorem half_angle_rapidity (a₁ a₂ φ θ : ℝ)
    (hθ : Real.cos θ = generalCos (Real.exp a₁) (Real.exp a₂) (Real.cos φ) (Real.sin φ) ∧
      Real.sin θ = generalSin (Real.exp a₁) (Real.exp a₂) (Real.cos φ) (Real.sin φ)) :
    Real.tan (θ / 2) = -(Real.sin φ * Real.sinh (a₁ / 2) * Real.sinh (a₂ / 2)) /
      (Real.cosh (a₁ / 2) * Real.cosh (a₂ / 2) + Real.cos φ * Real.sinh (a₁ / 2) * Real.sinh (a₂ / 2)) := by
  have h₁ := Real.exp_pos a₁
  have h₂ := Real.exp_pos a₂
  have hc : Real.cos φ ^ 2 ≤ 1 := by nlinarith [Real.sin_sq_add_cos_sq φ, sq_nonneg (Real.sin φ)]
  have hP := one_add_tau_mul_pos h₁ h₂ hc
  have hhalf := general_half_angle _ _ (Real.cos φ) (Real.sin φ) h₁ h₂ hc
  have hτ : tau (Real.exp a₁) (Real.exp a₂) = Real.tanh (a₁ / 2) * Real.tanh (a₂ / 2) := by
    rw [tau, halfTanh_exp, halfTanh_exp]
  rw [← hθ.1, ← hθ.2] at hhalf
  have c2 : Real.cos θ = 2 * Real.cos (θ / 2) ^ 2 - 1 := by
    rw [← Real.cos_two_mul]; ring_nf
  have s2 : Real.sin θ = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
    rw [← Real.sin_two_mul]; ring_nf
  have hpos : 0 < 1 + Real.cos θ := by
    rw [hθ.1]
    have hD := general_den_pos (c := Real.cos φ) (s := Real.sin φ) h₁ h₂ hc
    have e : 1 + generalCos (Real.exp a₁) (Real.exp a₂) (Real.cos φ) (Real.sin φ) =
        2 * (1 + tau (Real.exp a₁) (Real.exp a₂) * Real.cos φ) ^ 2 /
          ((1 + tau (Real.exp a₁) (Real.exp a₂) * Real.cos φ) ^ 2 +
            (tau (Real.exp a₁) (Real.exp a₂) * Real.sin φ) ^ 2) := by
      unfold generalCos; field_simp; ring
    rw [e]; positivity
  have hcos : Real.cos (θ / 2) ≠ 0 := by
    intro h; rw [c2, h] at hpos; norm_num at hpos
  have ch₁ := Real.cosh_pos (a₁ / 2)
  have ch₂ := Real.cosh_pos (a₂ / 2)
  rw [hτ, Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh, c2, s2] at hhalf
  rw [hτ, Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh] at hP
  have hden : Real.cosh (a₁ / 2) * Real.cosh (a₂ / 2) +
      Real.cos φ * Real.sinh (a₁ / 2) * Real.sinh (a₂ / 2) ≠ 0 := by
    have : 0 < Real.cosh (a₁ / 2) * Real.cosh (a₂ / 2) *
        (1 + Real.sinh (a₁ / 2) / Real.cosh (a₁ / 2) * (Real.sinh (a₂ / 2) / Real.cosh (a₂ / 2)) *
          Real.cos φ) := by positivity
    refine ne_of_gt (lt_of_lt_of_eq this ?_)
    field_simp
  rw [Real.tan_eq_sin_div_cos, eq_div_iff hden, div_mul_eq_mul_div, div_eq_iff hcos]
  field_simp at hhalf
  apply mul_left_cancel₀ hcos
  linear_combination (1 / 2 : ℝ) * hhalf


/-! ## The gyration join: the Möbius gyrogroup of the velocity disk -/

section Gyration

open ComplexConjugate Complex
open Holonics.Geometry.HolonicCurvedArcEinstein (gyrationCurvatureReturn)

/-- [definition] **The velocity disk**: the open unit disk of `ℂ`, the Poincaré chart of the velocity
hyperboloid. -/
def VelocityDisk : Type := {z : ℂ // Complex.normSq z < 1}

/-- [definition] **Möbius addition** `a ⊕ b = (a + b)/(1 + āb)`. -/
def mobAdd (a b : ℂ) : ℂ := (a + b) / (1 + conj a * b)

/-- [definition] **The gyration factor** `(1 + ab̄)/(1 + āb)`. -/
def gyrFactor (a b : ℂ) : ℂ := (1 + a * conj b) / (1 + conj a * b)

/-- [proved-standard; formal-checked] `|1 + āb|² − |a + b|² = (1 − |a|²)(1 − |b|²)`. -/
theorem normSq_den_sub (a b : ℂ) :
    normSq (1 + conj a * b) - normSq (a + b) = (1 - normSq a) * (1 - normSq b) := by
  simp only [normSq_apply, add_re, add_im, mul_re, mul_im, conj_re, conj_im, one_re, one_im]
  ring

/-- [proved-standard; formal-checked] `1 + āb ≠ 0` on the disk. -/
theorem den_ne_zero {a b : ℂ} (ha : normSq a < 1) (hb : normSq b < 1) : 1 + conj a * b ≠ 0 := by
  intro h
  have e := normSq_den_sub a b
  rw [h, map_zero] at e
  have : 0 < (1 - normSq a) * (1 - normSq b) := mul_pos (by linarith) (by linarith)
  nlinarith [normSq_nonneg (a + b)]

/-- [proved-standard; formal-checked] `1 + ab̄ ≠ 0` on the disk. -/
theorem den_ne_zero' {a b : ℂ} (ha : normSq a < 1) (hb : normSq b < 1) : 1 + a * conj b ≠ 0 := by
  rw [mul_comm]; exact den_ne_zero hb ha

/-- [proved-standard; formal-checked] The disk is closed under Möbius addition. -/
theorem normSq_mobAdd_lt {a b : ℂ} (ha : normSq a < 1) (hb : normSq b < 1) :
    normSq (mobAdd a b) < 1 := by
  have hd := normSq_pos.2 (den_ne_zero ha hb)
  rw [mobAdd, normSq_div, div_lt_one hd]
  have e := normSq_den_sub a b
  have : 0 < (1 - normSq a) * (1 - normSq b) := mul_pos (by linarith) (by linarith)
  linarith

/-- [proved-standard; formal-checked] The gyration factor is a unit. -/
theorem normSq_gyrFactor {a b : ℂ} (ha : normSq a < 1) (hb : normSq b < 1) :
    normSq (gyrFactor a b) = 1 := by
  have hd := (normSq_pos.2 (den_ne_zero ha hb)).ne'
  have e : 1 + a * conj b = conj (1 + conj a * b) := by simp
  rw [gyrFactor, normSq_div, e, normSq_conj, div_self hd]

/-- [proved-standard; formal-checked] `conj(gyr) · gyr = 1`. -/
theorem conj_gyrFactor_mul {a b : ℂ} (ha : normSq a < 1) (hb : normSq b < 1) :
    conj (gyrFactor a b) * gyrFactor a b = 1 := by
  rw [← normSq_eq_conj_mul_self, normSq_gyrFactor ha hb, ofReal_one]

/-- [definition] **The gyration** `gyr[a, b]`: multiplication by the gyration factor, an equivalence of the
disk. -/
def gyrEquiv (a b : VelocityDisk) : VelocityDisk ≃ VelocityDisk where
  toFun w := ⟨gyrFactor a.1 b.1 * w.1, by rw [normSq_mul, normSq_gyrFactor a.2 b.2, one_mul]; exact w.2⟩
  invFun w := ⟨conj (gyrFactor a.1 b.1) * w.1, by
    rw [normSq_mul, normSq_conj, normSq_gyrFactor a.2 b.2, one_mul]; exact w.2⟩
  left_inv w := Subtype.ext (by
    simp only; rw [← mul_assoc, conj_gyrFactor_mul a.2 b.2, one_mul])
  right_inv w := Subtype.ext (by
    simp only; rw [← mul_assoc, mul_comm _ (conj _), conj_gyrFactor_mul a.2 b.2, one_mul])

/-- [proved-standard; formal-checked] **The left gyroassociative law** `a ⊕ (b ⊕ c) = (a ⊕ b) ⊕ gyr[a, b]c`. -/
theorem mobAdd_assoc {a b c : ℂ} (ha : normSq a < 1) (hb : normSq b < 1) (hc : normSq c < 1) :
    mobAdd a (mobAdd b c) = mobAdd (mobAdd a b) (gyrFactor a b * c) := by
  have hab := den_ne_zero ha hb
  have hab' := den_ne_zero' ha hb
  have hbc := den_ne_zero hb hc
  have hab₂ : 1 + b * conj a ≠ 0 := by rwa [mul_comm]
  have hbc₂ : 1 + c * conj b ≠ 0 := by rwa [mul_comm]
  have hab₃ : 1 + conj b * a ≠ 0 := by rwa [mul_comm]
  have hL := den_ne_zero ha (normSq_mobAdd_lt hb hc)
  have hR := den_ne_zero (normSq_mobAdd_lt ha hb)
    (show normSq (gyrFactor a b * c) < 1 by rw [normSq_mul, normSq_gyrFactor ha hb, one_mul]; exact hc)
  unfold mobAdd at hL hR ⊢
  rw [div_eq_div_iff hL hR]
  simp only [gyrFactor, map_div₀, map_add, map_mul, map_one, conj_conj]
  field_simp
  ring

/-- [proved-standard; formal-checked] **The left loop law** `gyr[a, b] = gyr[a ⊕ b, b]`. -/
theorem gyrFactor_loop {a b : ℂ} (ha : normSq a < 1) (hb : normSq b < 1) :
    gyrFactor a b = gyrFactor (mobAdd a b) b := by
  have hab := den_ne_zero ha hb
  have hab' := den_ne_zero' ha hb
  have h2 := den_ne_zero (normSq_mobAdd_lt ha hb) hb
  unfold gyrFactor
  rw [div_eq_div_iff hab h2]
  simp only [mobAdd, map_div₀, map_add, map_mul, map_one, conj_conj]
  field_simp
  ring

/-- [proved-standard; formal-checked] **The Möbius gyrogroup of the velocity disk.** -/
instance mobiusGyrogroup : Gyrogroup VelocityDisk where
  op a b := ⟨mobAdd a.1 b.1, normSq_mobAdd_lt a.2 b.2⟩
  zero := ⟨0, by simp⟩
  inv a := ⟨-a.1, by simpa using a.2⟩
  gyr := gyrEquiv
  zero_op a := Subtype.ext (by simp [mobAdd])
  inv_op a := Subtype.ext (by simp [mobAdd])
  gyroassociative a b c := Subtype.ext (mobAdd_assoc a.2 b.2 c.2)
  gyr_automorphism a b c d := Subtype.ext (by
    show gyrFactor a.1 b.1 * mobAdd c.1 d.1 =
      mobAdd (gyrFactor a.1 b.1 * c.1) (gyrFactor a.1 b.1 * d.1)
    have e : conj (gyrFactor a.1 b.1 * c.1) * (gyrFactor a.1 b.1 * d.1) = conj c.1 * d.1 := by
      rw [map_mul, show conj (gyrFactor a.1 b.1) * conj c.1 * (gyrFactor a.1 b.1 * d.1) =
        (conj (gyrFactor a.1 b.1) * gyrFactor a.1 b.1) * (conj c.1 * d.1) by ring,
        conj_gyrFactor_mul a.2 b.2, one_mul]
    rw [mobAdd, mobAdd, e, ← mul_add, mul_div_assoc])
  loop a b := Equiv.ext fun w => Subtype.ext (by
    show gyrFactor a.1 b.1 * w.1 = gyrFactor (mobAdd a.1 b.1) b.1 * w.1
    rw [← gyrFactor_loop a.2 b.2])


/-- [proved-derived; formal-checked] The coordinates of `a ⊕ b` are `mobX` and `mobY`. -/
theorem mobAdd_re_im (a b : ℂ) :
    (mobAdd a b).re = mobX a.re a.im b.re b.im ∧ (mobAdd a b).im = mobY a.re a.im b.re b.im := by
  have hn : normSq (1 + conj a * b) = mobM a.re a.im b.re b.im := by
    simp only [normSq_apply, add_re, add_im, mul_re, mul_im, conj_re, conj_im, one_re, one_im,
      mobM, mobA, mobB]
    ring
  have hr : (1 + conj a * b).re = mobA a.re a.im b.re b.im := by simp [mobA]; ring
  have hi : (1 + conj a * b).im = mobB a.re a.im b.re b.im := by simp [mobB]; ring
  rw [mobAdd, div_re, div_im, hn, hr, hi, mobX, mobY]
  simp only [add_re, add_im]
  constructor <;> ring

/-- [proved-derived; formal-checked] The gyration factor's coordinates are `gyrCos` and `gyrSin`. -/
theorem gyrFactor_re_im (a b : ℂ) :
    (gyrFactor a b).re = gyrCos a.re a.im b.re b.im ∧
      (gyrFactor a b).im = gyrSin a.re a.im b.re b.im := by
  have hn : normSq (1 + conj a * b) = mobM a.re a.im b.re b.im := by
    simp only [normSq_apply, add_re, add_im, mul_re, mul_im, conj_re, conj_im, one_re, one_im,
      mobM, mobA, mobB]
    ring
  have hr : (1 + conj a * b).re = mobA a.re a.im b.re b.im := by simp [mobA]; ring
  have hi : (1 + conj a * b).im = mobB a.re a.im b.re b.im := by simp [mobB]; ring
  have hr' : (1 + a * conj b).re = mobA a.re a.im b.re b.im := by simp [mobA]; ring
  have hi' : (1 + a * conj b).im = -mobB a.re a.im b.re b.im := by simp [mobB]; ring
  rw [gyrFactor, div_re, div_im, hn, hr, hi, hr', hi', gyrCos, gyrSin]
  constructor <;> ring

/-- [proved-derived; formal-checked] A disk point's coordinates satisfy `x² + y² < 1`. -/
theorem disk_coords {z : ℂ} (h : normSq z < 1) : z.re ^ 2 + z.im ^ 2 < 1 := by
  rw [normSq_apply] at h; nlinarith

/-- [definition] **The event of the disk velocity `(x, y)`** on the velocity hyperboloid. -/
def hyperboloidPoint (x y : K) : Fin 3 → K :=
  ![(1 + x ^ 2 + y ^ 2) / (1 - x ^ 2 - y ^ 2), 2 * x / (1 - x ^ 2 - y ^ 2),
    2 * y / (1 - x ^ 2 - y ^ 2)]

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- [proved-derived; formal-checked] The disk boost carries the rest event to the event of its velocity. -/
theorem diskBoost_col (x y : K) (i : Fin 3) : diskBoost x y i 0 = hyperboloidPoint x y i := by
  fin_cases i <;> simp [diskBoost, pureBoost, hyperboloidPoint]

/-- [proved-standard; formal-checked] **The sum is the boosts' composite**:
`B(a)B(b) = B(a ⊕ b) · R(gyr[a, b])`. -/
theorem op_is_lorentz_composite (a b : VelocityDisk) :
    diskBoost a.1.re a.1.im * diskBoost b.1.re b.1.im =
      diskBoost (Gyrogroup.op a b).1.re (Gyrogroup.op a b).1.im *
        rotation (gyrFactor a.1 b.1).re (gyrFactor a.1 b.1).im := by
  obtain ⟨hx, hy⟩ := mobAdd_re_im a.1 b.1
  obtain ⟨hc, hs⟩ := gyrFactor_re_im a.1 b.1
  show _ = diskBoost (mobAdd a.1 b.1).re (mobAdd a.1 b.1).im * _
  rw [hx, hy, hc, hs]
  exact disk_composition (disk_coords a.2) (disk_coords b.2)

/-- [proved-derived; formal-checked] `gyrationCurvatureReturn a b` multiplies by the gyration factor. -/
theorem gyrationCurvatureReturn_apply (a b w : VelocityDisk) :
    (gyrationCurvatureReturn a b w).1 = gyrFactor a.1 b.1 * w.1 := rfl

/-- [proved-standard; formal-checked] On the hyperboloid the gyration curvature return is the turn
`R(gyr[a, b])`. -/
theorem gyration_on_hyperboloid (a b w : VelocityDisk) :
    hyperboloidPoint (gyrationCurvatureReturn a b w).1.re
        (gyrationCurvatureReturn a b w).1.im =
      rotation (gyrFactor a.1 b.1).re (gyrFactor a.1 b.1).im *ᵥ hyperboloidPoint w.1.re w.1.im := by
  rw [gyrationCurvatureReturn_apply]
  have hu := normSq_gyrFactor a.2 b.2
  rw [normSq_apply] at hu
  set u := gyrFactor a.1 b.1
  have hn : (u.re * w.1.re - u.im * w.1.im) ^ 2 + (u.re * w.1.im + u.im * w.1.re) ^ 2 =
      w.1.re ^ 2 + w.1.im ^ 2 := by
    linear_combination (w.1.re ^ 2 + w.1.im ^ 2) * hu
  have h1 : 1 - (u.re * w.1.re - u.im * w.1.im) ^ 2 - (u.re * w.1.im + u.im * w.1.re) ^ 2 =
      1 - w.1.re ^ 2 - w.1.im ^ 2 := by linear_combination -hn
  have h2 : 1 + (u.re * w.1.re - u.im * w.1.im) ^ 2 + (u.re * w.1.im + u.im * w.1.re) ^ 2 =
      1 + w.1.re ^ 2 + w.1.im ^ 2 := by linear_combination hn
  ext i
  fin_cases i <;>
    simp [hyperboloidPoint, rotation, Matrix.mulVec, dotProduct, Fin.sum_univ_three, h1, h2] <;>
    ring

/-- [definition] The disk velocity `t(c + is)` of the boost of ratio `k` along `(c, s)`. -/
def boostDisk (k c s : ℝ) (hk : 0 < k) (hcs : c ^ 2 + s ^ 2 = 1) : VelocityDisk :=
  ⟨((halfTanh k : ℝ) : ℂ) * (c + s * I), by
    rw [normSq_mul, normSq_ofReal, normSq_apply]
    simp only [add_re, add_im, ofReal_re, ofReal_im, mul_re, mul_im, I_re, I_im]
    have := halfTanh_sq_lt_one hk
    nlinarith⟩

/-- [proved-derived; formal-checked] Its coordinates are `(tc, ts)`. -/
theorem boostDisk_re_im (k c s : ℝ) (hk : 0 < k) (hcs : c ^ 2 + s ^ 2 = 1) :
    (boostDisk k c s hk hcs).1.re = halfTanh k * c ∧ (boostDisk k c s hk hcs).1.im = halfTanh k * s := by
  simp [boostDisk]

/-- [proved-standard; formal-checked] **The gyration of the two boost velocities is the general Wigner turn.**
-/
theorem gyration_is_wigner_rotation {k₁ k₂ c s : ℝ} (h₁ : 0 < k₁) (h₂ : 0 < k₂)
    (hcs : c ^ 2 + s ^ 2 = 1) :
    (gyrFactor (boostDisk k₁ 1 0 h₁ (by norm_num)).1 (boostDisk k₂ c s h₂ hcs).1).re =
        generalCos k₁ k₂ c s ∧
      (gyrFactor (boostDisk k₁ 1 0 h₁ (by norm_num)).1 (boostDisk k₂ c s h₂ hcs).1).im =
        generalSin k₁ k₂ c s := by
  obtain ⟨hc, hs⟩ := gyrFactor_re_im (boostDisk k₁ 1 0 h₁ (by norm_num)).1 (boostDisk k₂ c s h₂ hcs).1
  obtain ⟨a1, a2⟩ := boostDisk_re_im k₁ 1 0 h₁ (by norm_num)
  obtain ⟨b1, b2⟩ := boostDisk_re_im k₂ c s h₂ hcs
  obtain ⟨g1, g2⟩ := gyr_specialize k₁ k₂ c s
  rw [hc, hs, a1, a2, b1, b2, mul_one, mul_zero]
  exact ⟨g1, g2⟩

/-- [proved-standard; formal-checked] **The join**: `gyrationCurvatureReturn` acts on the hyperboloid as `R(θ)`.
-/
theorem gyrationCurvatureReturn_is_wigner {k₁ k₂ c s : ℝ} (h₁ : 0 < k₁) (h₂ : 0 < k₂)
    (hcs : c ^ 2 + s ^ 2 = 1) (w : VelocityDisk) :
    hyperboloidPoint
        (gyrationCurvatureReturn (boostDisk k₁ 1 0 h₁ (by norm_num))
          (boostDisk k₂ c s h₂ hcs) w).1.re
        (gyrationCurvatureReturn (boostDisk k₁ 1 0 h₁ (by norm_num))
          (boostDisk k₂ c s h₂ hcs) w).1.im =
      rotation (generalCos k₁ k₂ c s) (generalSin k₁ k₂ c s) *ᵥ hyperboloidPoint w.1.re w.1.im := by
  obtain ⟨g1, g2⟩ := gyration_is_wigner_rotation h₁ h₂ hcs
  rw [gyration_on_hyperboloid, g1, g2]

/-- [proved-standard; formal-checked] The Möbius sum of the two boost velocities is the composite velocity. -/
theorem op_is_composite_velocity {k₁ k₂ c s : ℝ} (h₁ : 0 < k₁) (h₂ : 0 < k₂)
    (hcs : c ^ 2 + s ^ 2 = 1) :
    hyperboloidPoint
        (Gyrogroup.op (boostDisk k₁ 1 0 h₁ (by norm_num)) (boostDisk k₂ c s h₂ hcs)).1.re
        (Gyrogroup.op (boostDisk k₁ 1 0 h₁ (by norm_num)) (boostDisk k₂ c s h₂ hcs)).1.im =
      ![compGamma k₁ k₂ c, compX k₁ k₂ c, compY k₂ s] := by
  have hcol := composite_column h₁ h₂ hcs
  obtain ⟨hx, hy⟩ := mobAdd_re_im (boostDisk k₁ 1 0 h₁ (by norm_num)).1 (boostDisk k₂ c s h₂ hcs).1
  obtain ⟨a1, a2⟩ := boostDisk_re_im k₁ 1 0 h₁ (by norm_num)
  obtain ⟨b1, b2⟩ := boostDisk_re_im k₂ c s h₂ hcs
  show hyperboloidPoint (mobAdd _ _).re (mobAdd _ _).im = _
  rw [hx, hy, a1, a2, b1, b2, mul_one, mul_zero]
  ext i
  rw [← diskBoost_col, hcol]
  fin_cases i <;> simp [pureBoost]

/-- [proved-derived; formal-checked] For perpendicular boosts the gyration is `(wignerCos, wignerSin)`. -/
theorem gyration_perpendicular {k₁ k₂ : ℝ} (h₁ : 0 < k₁) (h₂ : 0 < k₂) :
    (gyrFactor (boostDisk k₁ 1 0 h₁ (by norm_num)).1 (boostDisk k₂ 0 1 h₂ (by norm_num)).1).re =
        Wigner.wignerCos k₁ k₂ ∧
      (gyrFactor (boostDisk k₁ 1 0 h₁ (by norm_num)).1 (boostDisk k₂ 0 1 h₂ (by norm_num)).1).im =
        Wigner.wignerSin k₁ k₂ := by
  obtain ⟨g1, g2⟩ := gyration_is_wigner_rotation (c := 0) (s := 1) h₁ h₂ (by norm_num)
  obtain ⟨-, -, -, w1, w2⟩ := general_at_perpendicular h₁ h₂
  exact ⟨g1.trans w1, g2.trans w2⟩

/-- [proved-derived; formal-checked] At `k = (2, 3)` the gyration curvature return is not flat. -/
theorem gyration_nontrivial_two_three :
    gyrationCurvatureReturn (boostDisk 2 1 0 two_pos (by norm_num))
      (boostDisk 3 0 1 three_pos (by norm_num)) ≠ 1 := by
  apply Holonics.Geometry.HolonicCurvedArcEinstein.gyrationCurvatureReturn_nontrivial_of_moves
    (x := ⟨1 / 2, by rw [normSq_apply]; norm_num⟩)
  intro h
  have e := congrArg (fun w : VelocityDisk => w.1.im) h
  obtain ⟨-, g2⟩ := gyration_perpendicular (k₁ := 2) (k₂ := 3) two_pos three_pos
  have hs : Wigner.wignerSin (2 : ℝ) 3 = -12 / 37 := by
    norm_num [Wigner.wignerSin, gammaOf, gammaBetaOf]
  change (gyrFactor _ _ * (1 / 2 : ℂ)).im = (1 / 2 : ℂ).im at e
  rw [mul_im, g2, hs] at e
  norm_num at e

end Gyration


/-! ## The composite three-velocity is Einstein's sum -/

/-- [definition] **Einstein addition**, first coordinate: `(u + v/γ_u + γ_u/(1 + γ_u) (u·v) u)/(1 + u·v)`. -/
def einsteinX (ux uy vx vy g : K) : K :=
  (ux + vx / g + g / (1 + g) * (ux * vx + uy * vy) * ux) / (1 + (ux * vx + uy * vy))
/-- [definition] Einstein addition, second coordinate. -/
def einsteinY (ux uy vx vy g : K) : K :=
  (uy + vy / g + g / (1 + g) * (ux * vx + uy * vy) * uy) / (1 + (ux * vx + uy * vy))

/-- [proved-derived; formal-checked] `β² < 1` for a positive Doppler ratio. -/
theorem betaOf_sq_lt_one {k : K} (hk : 0 < k) : betaOf k ^ 2 < 1 := by
  rw [betaOf, div_pow, div_lt_one (by positivity)]
  nlinarith [sq_nonneg k, mul_pos hk hk]

/-- [proved-standard; formal-checked] **The composite three-velocity is the Einstein sum** of `(β₁, 0)` and
`β₂(c, s)`. -/
theorem composite_velocity_is_einstein_sum {k₁ k₂ c s : K} (h₁ : 0 < k₁) (h₂ : 0 < k₂)
    (hc : c ^ 2 ≤ 1) :
    compX k₁ k₂ c / compGamma k₁ k₂ c =
        einsteinX (betaOf k₁) 0 (betaOf k₂ * c) (betaOf k₂ * s) (gammaOf k₁) ∧
      compY k₂ s / compGamma k₁ k₂ c =
        einsteinY (betaOf k₁) 0 (betaOf k₂ * c) (betaOf k₂ * s) (gammaOf k₁) := by
  have hb : (betaOf k₁ * (betaOf k₂ * c)) ^ 2 < 1 := by
    have := betaOf_sq_lt_one h₁; have := betaOf_sq_lt_one h₂
    rw [mul_pow, mul_pow]
    nlinarith [sq_nonneg (betaOf k₁), sq_nonneg (betaOf k₂), sq_nonneg c,
      mul_nonneg (sq_nonneg (betaOf k₂)) (sq_nonneg c)]
  have hE : 0 < 1 + (betaOf k₁ * (betaOf k₂ * c) + 0 * (betaOf k₂ * s)) := by
    have := abs_lt.mp ((sq_lt_one_iff_abs_lt_one _).mp hb)
    linarith [this.1]
  have hG : compGamma k₁ k₂ c =
      gammaOf k₁ * gammaOf k₂ * (1 + (betaOf k₁ * (betaOf k₂ * c) + 0 * (betaOf k₂ * s))) := by
    simp only [compGamma, betaOf, gammaOf, gammaBetaOf]
    field_simp
    ring
  have hGpos : 0 < compGamma k₁ k₂ c := by
    rw [hG]; have := Wigner.gammaOf_pos h₁; have := Wigner.gammaOf_pos h₂; positivity
  have hg1 : gammaOf k₁ / (1 + gammaOf k₁) = (k₁ ^ 2 + 1) / (k₁ + 1) ^ 2 := by
    have : (0 : K) < k₁ + 1 := by linarith
    unfold gammaOf; field_simp; ring
  unfold einsteinX einsteinY
  rw [hg1, div_eq_div_iff hGpos.ne' hE.ne', div_eq_div_iff hGpos.ne' hE.ne']
  have : (0 : K) < k₁ + 1 := by linarith
  simp only [compX, compY, compGamma, betaOf, gammaOf, gammaBetaOf]
  constructor <;> field_simp <;> ring


/-! ## Gauss–Bonnet: the defect of the velocity triangle is its area -/

section GaussBonnet

open Real

/-- [proved-standard; formal-checked] `γ = cosh a` at `k = eᵃ`. -/
theorem gammaOf_exp (a : ℝ) : gammaOf (exp a) = cosh a := by
  rw [gammaOf, cosh_eq, exp_neg]

/-- [proved-standard; formal-checked] `γβ = sinh a` at `k = eᵃ`. -/
theorem gammaBetaOf_exp (a : ℝ) : gammaBetaOf (exp a) = sinh a := by
  rw [gammaBetaOf, sinh_eq, exp_neg]

/-- [definition] `S = √(cosh²a₁ cosh²a₂ − 1)`, the hyperbolic sine of the hypotenuse `OW`. -/
def hypSinh (a₁ a₂ : ℝ) : ℝ := √(cosh a₁ ^ 2 * cosh a₂ ^ 2 - 1)

/-- [definition] **The angle `α` at the rest vertex**: `arctan(sinh a₂/(sinh a₁ cosh a₂))`. -/
def restAngle (a₁ a₂ : ℝ) : ℝ := arctan (sinh a₂ / (sinh a₁ * cosh a₂))
/-- [definition] **The angle `β` at `W`**: `arctan(sinh a₁/(cosh a₁ sinh a₂))`. -/
def farAngle (a₁ a₂ : ℝ) : ℝ := arctan (sinh a₁ / (cosh a₁ * sinh a₂))

/-- [definition] The event at geodesic distance `r` from `O` in the direction `θ`. -/
def polarPoint (r θ : ℝ) : Fin 3 → ℝ := ![cosh r, sinh r * cos θ, sinh r * sin θ]

/-- [definition] `ρ(θ) = arsinh(tanh a₁/√(cos²θ − tanh²a₁))`: `tanh ρ cos θ = tanh a₁`. -/
def sideRadius (a₁ θ : ℝ) : ℝ := arsinh (tanh a₁ / √(cos θ ^ 2 - tanh a₁ ^ 2))

/-- [definition] **The area of the velocity triangle** about `O`: `∫₀^α ∫₀^ρ(θ) sinh r dr dθ`. -/
def triangleArea (a₁ a₂ : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..restAngle a₁ a₂, ∫ r in (0 : ℝ)..sideRadius a₁ θ, sinh r

/-- [proved-standard; formal-checked] `(sin, cos)(arctan(q/p)) = (q, p)/√(p² + q²)` for `p > 0`. -/
theorem arctan_trig {p q : ℝ} (hp : 0 < p) :
    sin (arctan (q / p)) = q / √(p ^ 2 + q ^ 2) ∧ cos (arctan (q / p)) = p / √(p ^ 2 + q ^ 2) := by
  have e : √(1 + (q / p) ^ 2) = √(p ^ 2 + q ^ 2) / p := by
    rw [show 1 + (q / p) ^ 2 = (p ^ 2 + q ^ 2) / p ^ 2 by field_simp,
      sqrt_div' _ (sq_nonneg p), sqrt_sq hp.le]
  have hs : 0 < √(p ^ 2 + q ^ 2) := sqrt_pos.2 (by positivity)
  rw [sin_arctan, cos_arctan, e]
  constructor <;> field_simp

/-- [proved-standard; formal-checked] `S² = (sinh a₁ cosh a₂)² + sinh²a₂ = (cosh a₁ sinh a₂)² + sinh²a₁`. -/
theorem hypSinh_sq (a₁ a₂ : ℝ) :
    cosh a₁ ^ 2 * cosh a₂ ^ 2 - 1 = (sinh a₁ * cosh a₂) ^ 2 + sinh a₂ ^ 2 ∧
      cosh a₁ ^ 2 * cosh a₂ ^ 2 - 1 = (cosh a₁ * sinh a₂) ^ 2 + sinh a₁ ^ 2 := by
  have e₁ := cosh_sq a₁
  have e₂ := cosh_sq a₂
  constructor
  · linear_combination cosh a₂ ^ 2 * e₁ + e₂
  · linear_combination cosh a₁ ^ 2 * e₂ + e₁

/-- [proved-standard; formal-checked] The angles' sines and cosines are Wigner's scaled readings over `S`. -/
theorem angles_trig {a₁ a₂ : ℝ} (h₁ : 0 < a₁) (h₂ : 0 < a₂) :
    sin (restAngle a₁ a₂) = sinh a₂ / hypSinh a₁ a₂ ∧
      cos (restAngle a₁ a₂) = sinh a₁ * cosh a₂ / hypSinh a₁ a₂ ∧
      sin (farAngle a₁ a₂) = sinh a₁ / hypSinh a₁ a₂ ∧
      cos (farAngle a₁ a₂) = cosh a₁ * sinh a₂ / hypSinh a₁ a₂ := by
  have s₁ := sinh_pos_iff.2 h₁
  have s₂ := sinh_pos_iff.2 h₂
  obtain ⟨e₁, e₂⟩ := hypSinh_sq a₁ a₂
  obtain ⟨r1, r2⟩ := arctan_trig (q := sinh a₂) (mul_pos s₁ (cosh_pos a₂))
  obtain ⟨f1, f2⟩ := arctan_trig (q := sinh a₁) (mul_pos (cosh_pos a₁) s₂)
  unfold restAngle farAngle hypSinh
  rw [r1, r2, f1, f2, e₁, ← e₂, ← e₁]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- [proved-derived; formal-checked] `S > 0`. -/
theorem hypSinh_pos {a₁ a₂ : ℝ} (h₁ : 0 < a₁) : 0 < hypSinh a₁ a₂ := by
  have s₁ := sinh_pos_iff.2 h₁
  rw [hypSinh, (hypSinh_sq a₁ a₂).2]
  exact sqrt_pos.2 (by positivity)

/-- [proved-derived; formal-checked] `S² = cosh²a₁ cosh²a₂ − 1`. -/
theorem hypSinh_sq' (a₁ a₂ : ℝ) : hypSinh a₁ a₂ ^ 2 = cosh a₁ ^ 2 * cosh a₂ ^ 2 - 1 := by
  rw [hypSinh, sq_sqrt]
  rw [(hypSinh_sq a₁ a₂).1]; positivity

/-- [proved-derived; formal-checked] Both angles lie in `(0, π/2)`. -/
theorem angles_mem {a₁ a₂ : ℝ} (h₁ : 0 < a₁) (h₂ : 0 < a₂) :
    0 < restAngle a₁ a₂ ∧ restAngle a₁ a₂ < π / 2 ∧ 0 < farAngle a₁ a₂ ∧ farAngle a₁ a₂ < π / 2 := by
  have s₁ := sinh_pos_iff.2 h₁
  have s₂ := sinh_pos_iff.2 h₂
  have c₁ := cosh_pos a₁
  have c₂ := cosh_pos a₂
  refine ⟨arctan_pos.2 (by positivity), arctan_lt_pi_div_two _, arctan_pos.2 (by positivity),
    arctan_lt_pi_div_two _⟩

/-- [proved-derived; formal-checked] `cos²θ − tanh²a₁ > 0` on `[0, α]`. -/
theorem side_den_pos {a₁ a₂ θ : ℝ} (h₁ : 0 < a₁) (h₂ : 0 < a₂) (hθ : θ ∈ Set.Icc 0 (restAngle a₁ a₂)) :
    0 < cos θ ^ 2 - tanh a₁ ^ 2 := by
  obtain ⟨α0, απ, -, -⟩ := angles_mem h₁ h₂
  obtain ⟨-, ca, -, -⟩ := angles_trig h₁ h₂
  have hS := hypSinh_pos (a₂ := a₂) h₁
  have hS2 := hypSinh_sq' a₁ a₂
  have s₁ := sinh_pos_iff.2 h₁
  have c₁ := cosh_pos a₁
  have c₂ := cosh_pos a₂
  have hle : cos (restAngle a₁ a₂) ≤ cos θ :=
    cos_le_cos_of_nonneg_of_le_pi hθ.1 (by linarith [pi_pos]) hθ.2
  have hcα : 0 < cos (restAngle a₁ a₂) := by rw [ca]; positivity
  have key : cos (restAngle a₁ a₂) ^ 2 - tanh a₁ ^ 2 = sinh a₁ ^ 2 / (hypSinh a₁ a₂ ^ 2 * cosh a₁ ^ 2) := by
    rw [ca, tanh_eq_sinh_div_cosh]
    field_simp
    rw [hS2]
    ring
  have : 0 < cos (restAngle a₁ a₂) ^ 2 - tanh a₁ ^ 2 := by rw [key]; positivity
  nlinarith

/-- [proved-derived; formal-checked] `cosh ρ(θ) = cos θ/√(cos²θ − tanh²a₁)`. -/
theorem cosh_sideRadius {a₁ θ : ℝ} (hD : 0 < cos θ ^ 2 - tanh a₁ ^ 2) (hc : 0 ≤ cos θ) :
    cosh (sideRadius a₁ θ) = cos θ / √(cos θ ^ 2 - tanh a₁ ^ 2) := by
  have hs := sqrt_pos.2 hD
  rw [sideRadius, cosh_arsinh, div_pow, sq_sqrt hD.le,
    show 1 + tanh a₁ ^ 2 / (cos θ ^ 2 - tanh a₁ ^ 2) = cos θ ^ 2 / (cos θ ^ 2 - tanh a₁ ^ 2) by
      field_simp; ring,
    sqrt_div' _ hD.le, sqrt_sq hc]

/-- [proved-derived; formal-checked] The curve `r = ρ(θ)` lies on the geodesic through `P` and `W`. -/
theorem side_on_geodesic {a₁ a₂ θ : ℝ} (h₁ : 0 < a₁) (h₂ : 0 < a₂)
    (hθ : θ ∈ Set.Icc 0 (restAngle a₁ a₂)) :
    Wigner.orientedArea (polarPoint (sideRadius a₁ θ) θ) (Wigner.vertexP (exp a₁))
      (Wigner.vertexW (exp a₁) (exp a₂)) = 0 := by
  have hD := side_den_pos h₁ h₂ hθ
  have hc : 0 ≤ cos θ :=
    cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, pi_pos], by linarith [hθ.2, (angles_mem h₁ h₂).2.1]⟩
  have hs := sqrt_pos.2 hD
  have c₁ := cosh_pos a₁
  have hsinh : sinh (sideRadius a₁ θ) = tanh a₁ / √(cos θ ^ 2 - tanh a₁ ^ 2) := by
    rw [sideRadius, sinh_arsinh]
  rw [Wigner.vertexP_apply, Wigner.vertexW_apply, gammaOf_exp, gammaOf_exp, gammaBetaOf_exp,
    gammaBetaOf_exp]
  simp only [Wigner.orientedArea, polarPoint, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  rw [cosh_sideRadius hD hc, hsinh, tanh_eq_sinh_div_cosh]
  field_simp
  ring

/-- [proved-derived; formal-checked] The curve starts at `P`. -/
theorem side_start {a₁ : ℝ} (h₁ : 0 < a₁) :
    polarPoint (sideRadius a₁ 0) 0 = Wigner.vertexP (exp a₁) := by
  have c₁ := cosh_pos a₁
  have hC2 := cosh_sq a₁
  have e : sideRadius a₁ 0 = a₁ := by
    have hq : √(1 - tanh a₁ ^ 2) = 1 / cosh a₁ := by
      rw [tanh_eq_sinh_div_cosh, show 1 - (sinh a₁ / cosh a₁) ^ 2 = (1 / cosh a₁) ^ 2 by
        field_simp; linear_combination hC2, sqrt_sq (by positivity)]
    rw [sideRadius, cos_zero, one_pow, hq, tanh_eq_sinh_div_cosh,
      show sinh a₁ / cosh a₁ / (1 / cosh a₁) = sinh a₁ by field_simp, arsinh_sinh]
  rw [e, Wigner.vertexP_apply, gammaOf_exp, gammaBetaOf_exp]
  ext i
  fin_cases i <;> simp [polarPoint]

/-- [proved-derived; formal-checked] The curve ends at `W`. -/
theorem side_end {a₁ a₂ : ℝ} (h₁ : 0 < a₁) (h₂ : 0 < a₂) :
    polarPoint (sideRadius a₁ (restAngle a₁ a₂)) (restAngle a₁ a₂) =
      Wigner.vertexW (exp a₁) (exp a₂) := by
  obtain ⟨sa, ca, -, -⟩ := angles_trig h₁ h₂
  have hS := hypSinh_pos (a₂ := a₂) h₁
  have hS2 := hypSinh_sq' a₁ a₂
  have s₁ := sinh_pos_iff.2 h₁
  have c₁ := cosh_pos a₁
  have c₂ := cosh_pos a₂
  have hden : cos (restAngle a₁ a₂) ^ 2 - tanh a₁ ^ 2 = (sinh a₁ / (hypSinh a₁ a₂ * cosh a₁)) ^ 2 := by
    rw [ca, tanh_eq_sinh_div_cosh]
    field_simp
    rw [hS2]
    ring
  have e : sideRadius a₁ (restAngle a₁ a₂) = arsinh (hypSinh a₁ a₂) := by
    rw [sideRadius, hden, sqrt_sq (by positivity), tanh_eq_sinh_div_cosh]
    congr 1
    field_simp
  have hcosh : cosh (arsinh (hypSinh a₁ a₂)) = cosh a₁ * cosh a₂ := by
    rw [cosh_arsinh, hS2, show 1 + (cosh a₁ ^ 2 * cosh a₂ ^ 2 - 1) = (cosh a₁ * cosh a₂) ^ 2 by ring,
      sqrt_sq (by positivity)]
  rw [e, Wigner.vertexW_apply, gammaOf_exp, gammaOf_exp, gammaBetaOf_exp, gammaBetaOf_exp]
  ext i
  fin_cases i <;> simp [polarPoint, hcosh, sinh_arsinh, sa, ca] <;> field_simp

/-- [proved-standard; formal-checked] `∫₀^R sinh r dr = cosh R − 1`. -/
theorem integral_sinh_eq (R : ℝ) : ∫ r in (0 : ℝ)..R, sinh r = cosh R - 1 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_cosh x)
    (continuous_sinh.intervalIntegrable _ _), cosh_zero]

/-- [proved-standard; formal-checked] **Gauss–Bonnet for the velocity triangle**: its area is its defect
`π/2 − α − β`. -/
theorem gauss_bonnet {a₁ a₂ : ℝ} (h₁ : 0 < a₁) (h₂ : 0 < a₂) :
    triangleArea a₁ a₂ = π / 2 - restAngle a₁ a₂ - farAngle a₁ a₂ := by
  obtain ⟨α0, απ, β0, βπ⟩ := angles_mem h₁ h₂
  obtain ⟨sa, -, -, cb⟩ := angles_trig h₁ h₂
  have hS := hypSinh_pos (a₂ := a₂) h₁
  have hS2 := hypSinh_sq' a₁ a₂
  have s₁ := sinh_pos_iff.2 h₁
  have s₂ := sinh_pos_iff.2 h₂
  have c₁ := cosh_pos a₁
  have c₂ := cosh_pos a₂
  have hC2 := cosh_sq a₁
  have hT : tanh a₁ = sinh a₁ / cosh a₁ := tanh_eq_sinh_div_cosh a₁
  have hcb : cos (farAngle a₁ a₂) < 1 := by
    rw [cb, div_lt_one hS]
    have e := (hypSinh_sq a₁ a₂).2
    nlinarith [mul_pos c₁ s₂]
  unfold triangleArea
  simp_rw [integral_sinh_eq]
  have hmem : ∀ θ ∈ Set.uIcc 0 (restAngle a₁ a₂), θ ∈ Set.Icc 0 (restAngle a₁ a₂) := by
    intro θ hθ; rwa [Set.uIcc_of_le α0.le] at hθ
  have hcongr : Set.EqOn (fun θ => cosh (sideRadius a₁ θ) - 1)
      (fun θ => cos θ / √(cos θ ^ 2 - tanh a₁ ^ 2) - 1) (Set.uIcc 0 (restAngle a₁ a₂)) := by
    intro θ hθ
    have h := hmem θ hθ
    simp only
    rw [cosh_sideRadius (side_den_pos h₁ h₂ h)
      (cos_nonneg_of_mem_Icc ⟨by linarith [h.1, pi_pos], by linarith [h.2]⟩)]
  rw [intervalIntegral.integral_congr hcongr]
  have hderiv : ∀ θ ∈ Set.uIcc 0 (restAngle a₁ a₂),
      HasDerivAt (fun θ => arcsin (cosh a₁ * sin θ) - θ)
        (cos θ / √(cos θ ^ 2 - tanh a₁ ^ 2) - 1) θ := by
    intro θ hθ
    have h := hmem θ hθ
    have hD := side_den_pos h₁ h₂ h
    have hsin0 : 0 ≤ sin θ := sin_nonneg_of_nonneg_of_le_pi h.1 (by linarith [h.2])
    have hsinα : sin θ ≤ sin (restAngle a₁ a₂) :=
      sin_le_sin_of_le_of_le_pi_div_two (by linarith [h.1]) απ.le h.2
    have hx1 : cosh a₁ * sin θ < 1 := by
      have : cosh a₁ * sin (restAngle a₁ a₂) = cos (farAngle a₁ a₂) := by
        rw [sa, cb]; ring
      nlinarith [mul_le_mul_of_nonneg_left hsinα c₁.le]
    have hx0 : 0 ≤ cosh a₁ * sin θ := mul_nonneg c₁.le hsin0
    have inner : HasDerivAt (fun θ => cosh a₁ * sin θ) (cosh a₁ * cos θ) θ :=
      (hasDerivAt_sin θ).const_mul _
    have outer := (hasDerivAt_arcsin (x := cosh a₁ * sin θ) (by linarith) hx1.ne).comp θ inner
    refine (outer.sub (hasDerivAt_id θ)).congr_deriv ?_
    have e : 1 - (cosh a₁ * sin θ) ^ 2 = cosh a₁ ^ 2 * (cos θ ^ 2 - tanh a₁ ^ 2) := by
      rw [hT, cos_sq']
      field_simp
      linear_combination -hC2
    have hsq : √(1 - (cosh a₁ * sin θ) ^ 2) = cosh a₁ * √(cos θ ^ 2 - tanh a₁ ^ 2) := by
      rw [e, sqrt_mul (sq_nonneg _), sqrt_sq c₁.le]
    have hs := sqrt_pos.2 hD
    rw [hsq]
    field_simp
  have hint : IntervalIntegrable (fun θ => cos θ / √(cos θ ^ 2 - tanh a₁ ^ 2) - 1)
      MeasureTheory.volume 0 (restAngle a₁ a₂) := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.sub _ continuousOn_const
    apply ContinuousOn.div continuous_cos.continuousOn
    · exact (continuous_sqrt.comp ((continuous_cos.pow 2).sub continuous_const)).continuousOn
    · intro θ hθ
      exact (sqrt_pos.2 (side_den_pos h₁ h₂ (hmem θ hθ))).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  have : cosh a₁ * sin (restAngle a₁ a₂) = sin (π / 2 - farAngle a₁ a₂) := by
    rw [sin_pi_div_two_sub, sa, cb]; ring
  simp only [sin_zero, mul_zero, arcsin_zero, sub_zero]
  rw [this, arcsin_sin (by linarith) (by linarith)]
  ring

/-- [proved-standard; formal-checked] **The Wigner rotation turns by minus the area**: `cos θ = cos A`,
`sin θ = −sin A`. -/
theorem wigner_rotation_turns_by_area {a₁ a₂ : ℝ} (h₁ : 0 < a₁) (h₂ : 0 < a₂) :
    Wigner.wignerCos (exp a₁) (exp a₂) = cos (triangleArea a₁ a₂) ∧
      Wigner.wignerSin (exp a₁) (exp a₂) = -sin (triangleArea a₁ a₂) := by
  obtain ⟨sa, ca, sb, cb⟩ := angles_trig h₁ h₂
  have hS := hypSinh_pos (a₂ := a₂) h₁
  have hS2 := hypSinh_sq' a₁ a₂
  have s₁ := sinh_pos_iff.2 h₁
  have s₂ := sinh_pos_iff.2 h₂
  obtain ⟨d1, d2⟩ := Wigner.wigner_angle_is_defect (exp_pos a₁) (exp_pos a₂)
  have hor : Wigner.orientation (exp a₁) (exp a₂) = 1 := by
    rw [Wigner.orientation, Wigner.orientedArea_triangle, gammaBetaOf_exp, gammaBetaOf_exp,
      sign_pos (mul_pos s₁ s₂)]
    rfl
  simp only [Wigner.sinAlpha, Wigner.cosAlpha, Wigner.sinBeta, Wigner.cosBeta, Wigner.scaleSq,
    gammaOf_exp, gammaBetaOf_exp, abs_of_pos s₁, abs_of_pos s₂, hor, one_mul] at d1 d2
  rw [gauss_bonnet h₁ h₂, show π / 2 - restAngle a₁ a₂ - farAngle a₁ a₂ =
    π / 2 - (restAngle a₁ a₂ + farAngle a₁ a₂) by ring, cos_pi_div_two_sub, sin_pi_div_two_sub,
    sin_add, cos_add, sa, ca, sb, cb]
  have hne : (cosh a₁ * cosh a₂) ^ 2 - 1 ≠ 0 := by rw [mul_pow, ← hS2]; positivity
  have key : ∀ x y : ℝ, x / hypSinh a₁ a₂ * (y / hypSinh a₁ a₂) =
      x * y / ((cosh a₁ * cosh a₂) ^ 2 - 1) := by
    intro x y; rw [div_mul_div_comm, ← sq, hS2, mul_pow]
  rw [key, key, key, key]
  constructor
  · rw [← add_div, eq_div_iff hne]; linear_combination d1
  · rw [← sub_div, ← neg_div, eq_div_iff hne]; linear_combination d2

end GaussBonnet

end Holonics.Physics.Spacetime.WignerGeneral
