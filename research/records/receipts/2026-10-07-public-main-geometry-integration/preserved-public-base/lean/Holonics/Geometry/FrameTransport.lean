import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Tactic.Ext
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Proper normalized receiver-frame transport

[proved-derived; formal-checked] For real Euclidean three-vectors, two nonzero
Gram–Schmidt operands construct an orthonormal, positively oriented frame using
positive normalization roots. Transport conducts the source frame coordinates
through the target frame and preserves every inner product, labelled ambient
oriented volume and first-axis component. No auxiliary-angle equality is assumed.

[agent-inferred] The existing rational screw/affine owners cannot carry general
positive-root normalization. This owner therefore reuses Mathlib's EuclideanSpace,
OrthonormalBasis and cross product; it adds only the orientation condition. It is
a receiver-frame chart of helical pair placement, not a new dynamical law. Native
realizations still owe their declared operand/positive-root interpretation join.

Positive v ↦ a v + b u is redundant; negative a negates both transverse columns,
a proper half-turn. A distinct transverse axis can change the declared transverse
operand's placement; no assertion that every operand changes is made. Refs #62.
-/

open scoped Matrix InnerProductSpace

noncomputable section

namespace Holonics.Geometry.FrameTransport

abbrev Vec3 := EuclideanSpace ℝ (Fin 3)

def dot3 (x y : Vec3) : ℝ := ⟪x, y⟫_ℝ

def coords (x : Vec3) : Fin 3 → ℝ := WithLp.ofLp x

def ofCoords (x : Fin 3 → ℝ) : Vec3 := WithLp.toLp 2 x

def cross3 (x y : Vec3) : Vec3 := ofCoords (coords x ⨯₃ coords y)

lemma dot3_eq_dotProduct (x y : Vec3) : dot3 x y = coords y ⬝ᵥ coords x := by
  simp [dot3, coords, EuclideanSpace.inner_eq_star_dotProduct]

lemma dot3_comm (x y : Vec3) : dot3 x y = dot3 y x := by
  rw [dot3_eq_dotProduct, dot3_eq_dotProduct, dotProduct_comm]

lemma dot3_cross_left (x y : Vec3) : dot3 x (cross3 x y) = 0 := by
  rw [dot3_eq_dotProduct]
  simp only [coords, cross3, ofCoords, WithLp.ofLp_toLp]
  rw [dotProduct_comm]
  exact dot_self_cross _ _

lemma dot3_cross_right (x y : Vec3) : dot3 y (cross3 x y) = 0 := by
  rw [dot3_eq_dotProduct]
  simp only [coords, cross3, ofCoords, WithLp.ofLp_toLp]
  rw [dotProduct_comm]
  exact dot_cross_self _ _

lemma dot3_cross_sq (x y : Vec3) :
    dot3 (cross3 x y) (cross3 x y) = dot3 x x * dot3 y y - dot3 x y * dot3 y x := by
  calc
    dot3 (cross3 x y) (cross3 x y) =
        (coords x ⨯₃ coords y) ⬝ᵥ (coords x ⨯₃ coords y) := by
          rw [dot3_eq_dotProduct]
          simp only [coords, cross3, ofCoords, WithLp.ofLp_toLp]
    _ = coords x ⬝ᵥ coords x * (coords y ⬝ᵥ coords y) -
        coords x ⬝ᵥ coords y * (coords y ⬝ᵥ coords x) := by
      exact cross_dot_cross (coords x) (coords y) (coords x) (coords y)
    _ = dot3 x x * dot3 y y - dot3 x y * dot3 y x := by
      simp only [dot3_eq_dotProduct]
      ring

/-- The orthogonal component of `v` relative to the nonzero axis `u`. -/
def transverse (u v : Vec3) : Vec3 := v - (dot3 u v / dot3 u u) • u

/-- `‖x‖` is the positive square root of its exact squared Euclidean length. -/
lemma norm_eq_positive_root (x : Vec3) : ‖x‖ = Real.sqrt (dot3 x x) := by
  have hq : dot3 x x = ∑ i, x i ^ 2 := by
    rw [dot3_eq_dotProduct]
    change (∑ i, x i * x i) = ∑ i, x i ^ 2
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hs : ‖x‖ ^ 2 = dot3 x x := by
    rw [EuclideanSpace.real_norm_sq_eq]
    exact hq.symm
  calc
    ‖x‖ = Real.sqrt (‖x‖ ^ 2) := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg x)]
    _ = Real.sqrt (dot3 x x) := by rw [hs]

lemma dot3_transverse_axis (u v : Vec3) (hu : u ≠ 0) :
    dot3 u (transverse u v) = 0 := by
  have hq : dot3 u u ≠ 0 := by
    rw [dot3, real_inner_self_eq_norm_sq]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hu)
  have hq' : ⟪u, u⟫_ℝ ≠ 0 := by simpa [dot3] using hq
  change ⟪u, v - (⟪u, v⟫_ℝ / ⟪u, u⟫_ℝ) • u⟫_ℝ = 0
  rw [inner_sub_right, real_inner_smul_right]
  field_simp [hq']
  ring

def unit (x : Vec3) : Vec3 := (‖x‖⁻¹) • x

lemma dot3_unit (x : Vec3) (hx : x ≠ 0) : dot3 (unit x) (unit x) = 1 := by
  rw [dot3, unit, real_inner_smul_left, real_inner_smul_right,
    real_inner_self_eq_norm_sq]
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  field_simp [hn]

lemma unit_transverse_orthogonal (u v : Vec3) (hu : u ≠ 0) :
    dot3 (unit u) (unit (transverse u v)) = 0 := by
  have h : ⟪u, transverse u v⟫_ℝ = 0 := by
    simpa [dot3] using dot3_transverse_axis u v hu
  rw [dot3, unit, unit, real_inner_smul_left, real_inner_smul_right]
  rw [h]
  ring

lemma dot3_cross_unit_sq (x y : Vec3) (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : dot3 (unit x) (unit y) = 0) : dot3 (cross3 (unit x) (unit y))
      (cross3 (unit x) (unit y)) = 1 := by
  rw [dot3_cross_sq, dot3_unit x hx, dot3_unit y hy]
  simp [hxy, dot3_comm]

lemma unit_smul_positive (x : Vec3) (hx : x ≠ 0) (a : ℝ) (ha : 0 < a) :
    unit (a • x) = unit x := by
  unfold unit
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha, smul_smul]
  have hna : a ≠ 0 := ne_of_gt ha
  have hnx : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  congr 1
  field_simp [hna, hnx]

lemma unit_neg (x : Vec3) : unit (-x) = -unit x := by
  simp [unit]

lemma unit_smul_negative (x : Vec3) (hx : x ≠ 0) (a : ℝ) (ha : a < 0) :
    unit (a • x) = -unit x := by
  have hna : 0 < -a := neg_pos.mpr ha
  have hdecomp : a • x = (-a) • (-x) := by simp
  rw [hdecomp, unit_smul_positive (-x) (neg_ne_zero.mpr hx) (-a) hna, unit_neg]

structure Frame3 where
  basis : OrthonormalBasis (Fin 3) ℝ Vec3
  rightHanded : cross3 (basis 0) (basis 1) = basis 2

theorem cross_second_third (f : Frame3) :
    cross3 (f.basis 1) (f.basis 2) = f.basis 0 := by
  have h11 : dot3 (f.basis 1) (f.basis 1) = 1 := f.basis.inner_eq_one 1
  have h01 : dot3 (f.basis 0) (f.basis 1) = 0 := by
    rw [dot3]
    exact f.basis.inner_eq_zero (by decide)
  have hraw11 : coords (f.basis 1) ⬝ᵥ coords (f.basis 1) = 1 := by
    rw [← dot3_eq_dotProduct]
    exact h11
  have hraw01 : coords (f.basis 0) ⬝ᵥ coords (f.basis 1) = 0 := by
    rw [← dot3_eq_dotProduct, dot3_comm]
    exact h01
  have hcross := cross_cross_eq_smul_sub_smul' (coords (f.basis 1))
    (coords (f.basis 0)) (coords (f.basis 1))
  rw [hraw11, hraw01] at hcross
  simp only [one_smul, zero_smul, sub_zero] at hcross
  rw [← f.rightHanded]
  ext i
  simp only [coords, cross3, ofCoords, WithLp.ofLp_toLp]
  exact congrFun hcross i

/-! [proved-derived; formal-checked in isolated development] Proposed insertion immediately after
`cross_second_third` in Geometry/FrameTransport. The columns are the actual
u/v derivatives of the polynomial disk section in TUBE_GEOMETRY_DERIVATION.md.
No positivity is needed for this polynomial identity; invertibility, longitudinal derivative, 3D continuity and native physical joins are
separate; the transverse derivative is identified by the declarations below. -/

/-- Oriented section area for q₁=a*u*(1+ε*u), q₂=b*v*(1+ε*u). -/
theorem tube_section_area_vector (f : Frame3) (a b ε u v : ℝ) :
    cross3 ((a * (1 + 2 * ε * u)) • f.basis 1 +
        (b * ε * v) • f.basis 2) ((b * (1 + ε * u)) • f.basis 2) =
      (a * b * (1 + ε * u) * (1 + 2 * ε * u)) • f.basis 0 := by
  have hframe : coords (f.basis 1) ⨯₃ coords (f.basis 2) =
      coords (f.basis 0) := by
    have h := congrArg coords (cross_second_third f)
    simpa only [coords, cross3, ofCoords, WithLp.ofLp_toLp] using h
  have harea :
      ((a * (1 + 2 * ε * u)) • coords (f.basis 1) +
        (b * ε * v) • coords (f.basis 2)) ⨯₃
          ((b * (1 + ε * u)) • coords (f.basis 2)) =
      ((a * (1 + 2 * ε * u)) * (b * (1 + ε * u))) •
        coords (f.basis 0) := by
    rw [LinearMap.map_add₂, LinearMap.map_smul₂, LinearMap.map_smul₂]
    simp only [map_smul, cross_self, smul_zero, add_zero, smul_smul]
    rw [hframe]
  have hcoef : (a * (1 + 2 * ε * u)) * (b * (1 + ε * u)) =
      a * b * (1 + ε * u) * (1 + 2 * ε * u) := by ring
  ext i
  change (((a * (1 + 2 * ε * u)) • coords (f.basis 1) +
      (b * ε * v) • coords (f.basis 2)) ⨯₃
        ((b * (1 + ε * u)) • coords (f.basis 2))) i =
    ((a * b * (1 + ε * u) * (1 + 2 * ε * u)) • coords (f.basis 0)) i
  rw [harea, hcoef]

/-- The section reading of an actual relative current; its continuity law is owed. -/
theorem tube_section_flux (f : Frame3) (a b ε u v : ℝ) (j : Vec3) :
    dot3 j (cross3 ((a * (1 + 2 * ε * u)) • f.basis 1 +
        (b * ε * v) • f.basis 2) ((b * (1 + ε * u)) • f.basis 2)) =
      (a * b * (1 + ε * u) * (1 + 2 * ε * u)) * dot3 j (f.basis 0) := by
  rw [tube_section_area_vector]
  simp only [dot3, real_inner_smul_right]

/-! The actual fixed-spine-position polynomial section derivative. The complete
isolated module is accepted; full 3D moving continuity and native decoder remain
separate consumers. Refs #62, #73. -/

/-- The explicit transverse section of the asymmetric tube at a fixed spine point. -/
def tube_section_chart (f : Frame3) (c : Vec3) (a b ε : ℝ) (z : ℝ × ℝ) : Vec3 :=
  c + (a * z.1 * (1 + ε * z.1)) • f.basis 1 +
    (b * z.2 * (1 + ε * z.1)) • f.basis 2

/-- Its derivative, expressed as a continuous linear map on actual coordinate increments. -/
def tube_section_derivative (f : Frame3) (a b ε : ℝ) (z : ℝ × ℝ) :
    (ℝ × ℝ) →L[ℝ] Vec3 :=
  ((a * (1 + 2 * ε * z.1)) • ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight
      (f.basis 1) +
    ((b * ε * z.2) • ContinuousLinearMap.fst ℝ ℝ ℝ +
      (b * (1 + ε * z.1)) • ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight
      (f.basis 2)

/-- Identification of the displayed section columns with an actual Fréchet derivative. -/
theorem tube_section_hasFDerivAt (f : Frame3) (c : Vec3) (a b ε : ℝ) (z : ℝ × ℝ) :
    HasFDerivAt (tube_section_chart f c a b ε)
      (tube_section_derivative f a b ε z) z := by
  have hu : HasFDerivAt (fun y : ℝ × ℝ => y.1)
      (ContinuousLinearMap.fst ℝ ℝ ℝ) z := hasFDerivAt_fst
  have hv : HasFDerivAt (fun y : ℝ × ℝ => y.2)
      (ContinuousLinearMap.snd ℝ ℝ ℝ) z := hasFDerivAt_snd
  have hh := (hasFDerivAt_const (1 : ℝ) z).add (hu.const_smul ε)
  have hq1 := (hu.const_smul a).mul hh
  have hq2 := (hv.const_smul b).mul hh
  have hX := ((hasFDerivAt_const c z).add (hq1.smul_const (f.basis 1))).add
    (hq2.smul_const (f.basis 2))
  convert! hX using 1
  apply ContinuousLinearMap.ext
  intro δ
  ext i
  simp [tube_section_derivative, smul_eq_mul]
  ring

theorem tube_section_fderiv_first (f : Frame3) (c : Vec3) (a b ε u v : ℝ) :
    fderiv ℝ (tube_section_chart f c a b ε) (u, v) (1, 0) =
      (a * (1 + 2 * ε * u)) • f.basis 1 + (b * ε * v) • f.basis 2 := by
  rw [(tube_section_hasFDerivAt f c a b ε (u, v)).fderiv]
  simp [tube_section_derivative]

theorem tube_section_fderiv_second (f : Frame3) (c : Vec3) (a b ε u v : ℝ) :
    fderiv ℝ (tube_section_chart f c a b ε) (u, v) (0, 1) =
      (b * (1 + ε * u)) • f.basis 2 := by
  rw [(tube_section_hasFDerivAt f c a b ε (u, v)).fderiv]
  simp [tube_section_derivative]

/-- The oriented area is now a reading of the constructed chart's derivative. -/
theorem tube_section_actual_area (f : Frame3) (c : Vec3) (a b ε u v : ℝ) :
    cross3 (fderiv ℝ (tube_section_chart f c a b ε) (u, v) (1, 0))
      (fderiv ℝ (tube_section_chart f c a b ε) (u, v) (0, 1)) =
      (a * b * (1 + ε * u) * (1 + 2 * ε * u)) • f.basis 0 := by
  rw [tube_section_fderiv_first, tube_section_fderiv_second]
  exact tube_section_area_vector f a b ε u v

/-- The section pairs an actual current with the constructed chart's oriented area.
Supplying a continuity current, moving-relative current or balance is a separate consumer. -/
theorem tube_section_actual_flux (f : Frame3) (c : Vec3) (a b ε u v : ℝ) (j : Vec3) :
    dot3 j (cross3 (fderiv ℝ (tube_section_chart f c a b ε) (u, v) (1, 0))
      (fderiv ℝ (tube_section_chart f c a b ε) (u, v) (0, 1))) =
      (a * b * (1 + ε * u) * (1 + 2 * ε * u)) * dot3 j (f.basis 0) := by
  rw [tube_section_fderiv_first, tube_section_fderiv_second]
  exact tube_section_flux f a b ε u v j


theorem frame_standard_determinant (f : Frame3) :
    Matrix.det ![coords (f.basis 0), coords (f.basis 1), coords (f.basis 2)] = 1 := by
  rw [← triple_product_eq_det]
  have hcross := congrArg coords (cross_second_third f)
  change coords (f.basis 1) ⨯₃ coords (f.basis 2) = coords (f.basis 0) at hcross
  rw [hcross]
  rw [← dot3_eq_dotProduct]
  exact f.basis.inner_eq_one 0

/-- The three actual normalized Gram–Schmidt columns. -/
def gramSchmidtColumns (u v : Vec3) : Fin 3 → Vec3 :=
  ![unit u, unit (transverse u v), cross3 (unit u) (unit (transverse u v))]

lemma gramSchmidtColumns_orthonormal (u v : Vec3) (hu : u ≠ 0)
    (hw : transverse u v ≠ 0) : Orthonormal ℝ (gramSchmidtColumns u v) := by
  let e₁ := unit u
  let w := transverse u v
  let e₂ := unit w
  let e₃ := cross3 e₁ e₂
  have h₁ : dot3 e₁ e₁ = 1 := dot3_unit u hu
  have h₂ : dot3 e₂ e₂ = 1 := dot3_unit w hw
  have h₁₂ : dot3 e₁ e₂ = 0 := unit_transverse_orthogonal u v hu
  have h₃ : dot3 e₃ e₃ = 1 := by
    dsimp [e₃]
    exact dot3_cross_unit_sq u w hu hw h₁₂
  have h₁₃ : dot3 e₁ e₃ = 0 := dot3_cross_left e₁ e₂
  have h₂₃ : dot3 e₂ e₃ = 0 := dot3_cross_right e₁ e₂
  have h₁' : ⟪e₁, e₁⟫_ℝ = 1 := by simpa [dot3] using h₁
  have h₂' : ⟪e₂, e₂⟫_ℝ = 1 := by simpa [dot3] using h₂
  have h₃' : ⟪e₃, e₃⟫_ℝ = 1 := by simpa [dot3] using h₃
  have h₁₂' : ⟪e₁, e₂⟫_ℝ = 0 := by simpa [dot3] using h₁₂
  have h₁₃' : ⟪e₁, e₃⟫_ℝ = 0 := by simpa [dot3] using h₁₃
  have h₂₃' : ⟪e₂, e₃⟫_ℝ = 0 := by simpa [dot3] using h₂₃
  rw [orthonormal_iff_ite]
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp_all [gramSchmidtColumns, e₁, e₂, e₃, w, real_inner_comm]

/-- Reuse Mathlib's real orthonormal-basis carrier for these columns. -/
noncomputable def gramSchmidtBasis (u v : Vec3) (hu : u ≠ 0)
    (hw : transverse u v ≠ 0) : OrthonormalBasis (Fin 3) ℝ Vec3 := by
  let hon := gramSchmidtColumns_orthonormal u v hu hw
  have hsp : ⊤ ≤ Submodule.span ℝ (Set.range (gramSchmidtColumns u v)) :=
    ((Orthonormal.linearIndependent hon).span_eq_top_of_card_eq_finrank' (by simp [Vec3])).ge
  exact OrthonormalBasis.mk hon hsp

theorem gramSchmidtBasis_apply (u v : Vec3) (hu : u ≠ 0)
    (hw : transverse u v ≠ 0) (i : Fin 3) :
    gramSchmidtBasis u v hu hw i = gramSchmidtColumns u v i := by
  simp only [gramSchmidtBasis]
  exact congrFun (OrthonormalBasis.coe_mk _ _) i

/-- The exact right-handed Gram–Schmidt frame; normalization uses positive Euclidean norms. -/
noncomputable def gramSchmidtFrame (u v : Vec3) (hu : u ≠ 0)
    (hw : transverse u v ≠ 0) : Frame3 where
  basis := gramSchmidtBasis u v hu hw
  rightHanded := by
    rw [gramSchmidtBasis_apply, gramSchmidtBasis_apply,
      gramSchmidtBasis_apply]
    rfl

@[simp] theorem gramSchmidtFrame_first (u v : Vec3) (hu : u ≠ 0)
    (hw : transverse u v ≠ 0) : (gramSchmidtFrame u v hu hw).basis 0 = unit u := by
  rw [gramSchmidtFrame, gramSchmidtBasis_apply]
  rfl

@[simp] theorem gramSchmidtFrame_second (u v : Vec3) (hu : u ≠ 0)
    (hw : transverse u v ≠ 0) :
    (gramSchmidtFrame u v hu hw).basis 1 = unit (transverse u v) := by
  rw [gramSchmidtFrame, gramSchmidtBasis_apply]
  rfl

@[simp] theorem gramSchmidtFrame_third (u v : Vec3) (hu : u ≠ 0)
    (hw : transverse u v ≠ 0) :
    (gramSchmidtFrame u v hu hw).basis 2 =
      cross3 (unit u) (unit (transverse u v)) := by
  rw [gramSchmidtFrame, gramSchmidtBasis_apply]
  rfl

lemma transverse_affine (u v : Vec3) (hu : u ≠ 0) (a b : ℝ) :
    transverse u (a • v + b • u) = a • transverse u v := by
  have hq : dot3 u u ≠ 0 := by
    rw [dot3, real_inner_self_eq_norm_sq]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hu)
  have hdot : dot3 u (a • v + b • u) =
      a * dot3 u v + b * dot3 u u := by
    change ⟪u, a • v + b • u⟫_ℝ = a * ⟪u, v⟫_ℝ + b * ⟪u, u⟫_ℝ
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
  have hcoeff : (a * dot3 u v + b * dot3 u u) / dot3 u u =
      a * (dot3 u v / dot3 u u) + b := by
    field_simp [hq]
  rw [transverse, transverse, hdot]
  ext i
  simp only [PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply]
  rw [hcoeff]
  ring

theorem gramSchmidtFrame_positive_gauge_columns (u v : Vec3) (hu : u ≠ 0)
    (hw : transverse u v ≠ 0) (a b : ℝ) (ha : 0 < a) :
    ∀ i, (gramSchmidtFrame u (a • v + b • u) hu
        (by rw [transverse_affine u v hu a b]; exact smul_ne_zero (ne_of_gt ha) hw)).basis i =
      (gramSchmidtFrame u v hu hw).basis i := by
  have htrans := transverse_affine u v hu a b
  have hw' : transverse u (a • v + b • u) ≠ 0 := by
    rw [htrans]
    exact smul_ne_zero (ne_of_gt ha) hw
  intro i
  fin_cases i
  · simp [gramSchmidtFrame_first]
  · change (gramSchmidtFrame u (a • v + b • u) hu hw').basis 1 =
      (gramSchmidtFrame u v hu hw).basis 1
    rw [gramSchmidtFrame_second, gramSchmidtFrame_second, htrans,
      unit_smul_positive (transverse u v) hw a ha]
  · change (gramSchmidtFrame u (a • v + b • u) hu hw').basis 2 =
      (gramSchmidtFrame u v hu hw).basis 2
    rw [gramSchmidtFrame_third, gramSchmidtFrame_third, htrans,
      unit_smul_positive (transverse u v) hw a ha]

lemma cross3_neg_right (x y : Vec3) : cross3 x (-y) = -cross3 x y := by
  ext i
  fin_cases i <;> simp [cross3, coords, ofCoords, cross_apply, mul_neg] <;> ring

theorem gramSchmidtFrame_negative_gauge_columns (u v : Vec3) (hu : u ≠ 0)
    (hw : transverse u v ≠ 0) (a b : ℝ) (ha : a < 0) :
    let hneg : transverse u (a • v + b • u) ≠ 0 := by
      rw [transverse_affine u v hu a b]
      exact smul_ne_zero (ne_of_lt ha) hw
    (gramSchmidtFrame u (a • v + b • u) hu hneg).basis 0 =
        (gramSchmidtFrame u v hu hw).basis 0 ∧
      (gramSchmidtFrame u (a • v + b • u) hu hneg).basis 1 =
        -(gramSchmidtFrame u v hu hw).basis 1 ∧
      (gramSchmidtFrame u (a • v + b • u) hu hneg).basis 2 =
        -(gramSchmidtFrame u v hu hw).basis 2 := by
  have htrans := transverse_affine u v hu a b
  have hw' : transverse u (a • v + b • u) ≠ 0 := by
    rw [htrans]
    exact smul_ne_zero (ne_of_lt ha) hw
  change (gramSchmidtFrame u (a • v + b • u) hu hw').basis 0 =
      (gramSchmidtFrame u v hu hw).basis 0 ∧
    (gramSchmidtFrame u (a • v + b • u) hu hw').basis 1 =
      -(gramSchmidtFrame u v hu hw).basis 1 ∧
    (gramSchmidtFrame u (a • v + b • u) hu hw').basis 2 =
      -(gramSchmidtFrame u v hu hw).basis 2
  refine ⟨?_, ?_, ?_⟩
  · rw [gramSchmidtFrame_first, gramSchmidtFrame_first]
  · rw [gramSchmidtFrame_second, gramSchmidtFrame_second, htrans,
      unit_smul_negative (transverse u v) hw a ha]
  · rw [gramSchmidtFrame_third, gramSchmidtFrame_third, htrans,
      unit_smul_negative (transverse u v) hw a ha, cross3_neg_right]

def axisHalfTurnMatrix : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.diagonal ![(1 : ℝ), -1, -1]

theorem axisHalfTurnMatrix_det : Matrix.det axisHalfTurnMatrix = 1 := by
  rw [axisHalfTurnMatrix, Matrix.det_diagonal]
  norm_num [Fin.prod_univ_succ]

/-- The coordinate change `F_t F_sᵀ`, expressed through the two orthonormal bases. -/
def transport (source target : Frame3) (d : Vec3) : Vec3 :=
  target.basis.repr.symm (source.basis.repr d)

theorem transport_expansion (s t : Frame3) (d : Vec3) :
    transport s t d = ∑ i, dot3 (s.basis i) d • t.basis i := by
  rw [← t.basis.sum_repr' (transport s t d)]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  calc
    ⟪t.basis i, transport s t d⟫_ℝ =
        (t.basis.repr (transport s t d)) i :=
          (t.basis.repr_apply_apply (transport s t d) i).symm
    _ = (s.basis.repr d) i := by simp [transport]
    _ = dot3 (s.basis i) d := by
      simpa [dot3] using (s.basis.repr_apply_apply d i)

theorem transport_basis (s t : Frame3) (i : Fin 3) :
    transport s t (s.basis i) = t.basis i := by
  simp [transport]

theorem distinct_transverse_axis_changes_placement (s t : Frame3)
    (h : t.basis 1 ≠ s.basis 1) :
    transport s t (s.basis 1) ≠ s.basis 1 := by
  rw [transport_basis]
  exact h

def frameCoordinates (f : Frame3) (x : Vec3) : Fin 3 → ℝ :=
  fun i => f.basis.repr x i

def orientedVolume (f : Frame3) (x y z : Vec3) : ℝ :=
  Matrix.det ![frameCoordinates f x, frameCoordinates f y, frameCoordinates f z]

theorem transport_coordinates (s t : Frame3) (d : Vec3) :
    frameCoordinates t (transport s t d) = frameCoordinates s d := by
  funext i
  simp [frameCoordinates, transport]

theorem transport_inner (s t : Frame3) (x y : Vec3) :
    dot3 (transport s t x) (transport s t y) = dot3 x y := by
  unfold dot3 transport
  calc
    ⟪t.basis.repr.symm (s.basis.repr x), t.basis.repr.symm (s.basis.repr y)⟫_ℝ =
        ⟪s.basis.repr x, s.basis.repr y⟫_ℝ := (t.basis.repr.symm).inner_map_map _ _
    _ = ⟪x, y⟫_ℝ := s.basis.repr.inner_map_map _ _

theorem transport_first_axis (s t : Frame3) (d : Vec3) :
    dot3 (t.basis 0) (transport s t d) = dot3 (s.basis 0) d := by
  calc
    dot3 (t.basis 0) (transport s t d) = (t.basis.repr (transport s t d)) 0 := by
      simpa [dot3] using (t.basis.repr_apply_apply (transport s t d) 0).symm
    _ = (s.basis.repr d) 0 := by simp [transport]
    _ = dot3 (s.basis 0) d := by
      simpa [dot3] using (s.basis.repr_apply_apply d 0)

theorem transport_oriented_volume (s t : Frame3) (x y z : Vec3) :
    orientedVolume t (transport s t x) (transport s t y) (transport s t z) =
      orientedVolume s x y z := by
  unfold orientedVolume
  rw [transport_coordinates s t x, transport_coordinates s t y,
    transport_coordinates s t z]

/-- Rows in the one fixed ambient Cartesian carrier, independently of a frame. -/
def ambientRows (xs : Fin 3 → Vec3) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => coords (xs i) j

def coordinateRows (f : Frame3) (xs : Fin 3 → Vec3) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => frameCoordinates f (xs i) j

def frameRows (f : Frame3) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => coords (f.basis i) j

/-- Actual ambient rows factor through the frame coordinates and its ambient rows. -/
theorem ambientRows_factor (f : Frame3) (xs : Fin 3 → Vec3) :
    ambientRows xs = coordinateRows f xs * frameRows f := by
  ext i j
  have h := congrArg (fun v : Vec3 => coords v j) (f.basis.sum_repr (xs i))
  simpa only [ambientRows, coordinateRows, frameRows, Matrix.mul_apply,
    frameCoordinates, coords, WithLp.ofLp_sum, WithLp.ofLp_smul,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h.symm

theorem frameRows_det (f : Frame3) : Matrix.det (frameRows f) = 1 := by
  have h : frameRows f = ![coords (f.basis 0), coords (f.basis 1),
      coords (f.basis 2)] := by
    ext i j
    fin_cases i <;> rfl
  rw [h]
  exact frame_standard_determinant f

/-- Labelled oriented volume in the fixed ambient Cartesian coordinates. -/
def ambientOrientedVolume (x y z : Vec3) : ℝ :=
  Matrix.det ![coords x, coords y, coords z]

/-- The right-handed frame has determinant one, so its coordinate determinant is
the ambient oriented volume. This is the orientation join missing from a coordinate-only read. -/
theorem ambientOrientedVolume_eq_frame (f : Frame3) (x y z : Vec3) :
    ambientOrientedVolume x y z = orientedVolume f x y z := by
  have ha : ambientRows ![x, y, z] = ![coords x, coords y, coords z] := by
    ext i j
    fin_cases i <;> rfl
  have hc : coordinateRows f ![x, y, z] =
      ![frameCoordinates f x, frameCoordinates f y, frameCoordinates f z] := by
    ext i j
    fin_cases i <;> rfl
  calc
    ambientOrientedVolume x y z = Matrix.det (ambientRows ![x, y, z]) := by
      rw [ha]
      rfl
    _ = Matrix.det (coordinateRows f ![x, y, z] * frameRows f) := by
      rw [ambientRows_factor]
    _ = Matrix.det (coordinateRows f ![x, y, z]) * Matrix.det (frameRows f) :=
      Matrix.det_mul _ _
    _ = orientedVolume f x y z := by
      rw [frameRows_det, mul_one, hc]
      rfl

theorem transport_ambient_oriented_volume (s t : Frame3) (x y z : Vec3) :
    ambientOrientedVolume (transport s t x) (transport s t y) (transport s t z) =
      ambientOrientedVolume x y z := by
  calc
    ambientOrientedVolume (transport s t x) (transport s t y) (transport s t z) =
        orientedVolume t (transport s t x) (transport s t y) (transport s t z) :=
      ambientOrientedVolume_eq_frame t _ _ _
    _ = orientedVolume s x y z := transport_oriented_volume s t x y z
    _ = ambientOrientedVolume x y z := (ambientOrientedVolume_eq_frame s x y z).symm

/-- One ambient contract: all inner products, labelled ambient oriented volumes,
and the transported first-axis component. No auxiliary-angle equality is a hypothesis. -/
theorem transport_ambient_contract (s t : Frame3) (x y z d : Vec3) :
    dot3 (transport s t x) (transport s t y) = dot3 x y ∧
      ambientOrientedVolume (transport s t x) (transport s t y) (transport s t z) =
        ambientOrientedVolume x y z ∧
      dot3 (t.basis 0) (transport s t d) = dot3 (s.basis 0) d :=
  ⟨transport_inner s t x y, transport_ambient_oriented_volume s t x y z,
    transport_first_axis s t d⟩

end Holonics.Geometry.FrameTransport

#print axioms Holonics.Geometry.FrameTransport.tube_section_area_vector
#print axioms Holonics.Geometry.FrameTransport.tube_section_flux
