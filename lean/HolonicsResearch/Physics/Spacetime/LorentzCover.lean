import Mathlib
import HolonicsResearch.Physics.TwoWayField

/-!
# A move of a complex pair is a Lorentz map of its Hermitian forms, read twice: the cover and its Doppler ratio

The Einstein record of November 11
(`research/records/2026-11-11_EINSTEINS_FIELD_PROGRAM_ON_THE_COMPLEX_THE_UNIFIED_FIELD_IS_A_TWO_WAY_FLOW_A_GRAIN_GIVES_THE_MASS_AND_A_PROBABILITY_IS_ITS_FLAT_PART.md`,
§11; atlas `lorentz.pair-hermitian-signature`) reads the Hermitian forms of an undivided complex pair as a three and
one, and `Physics/TwoWayField` §6 proves that a move `X ↦ Aᴴ X A` of determinant one keeps the form's determinant. #410
owes the map itself: `PSL(2, ℂ) ≅ SO⁺(1, 3)`, with the representation that reads a multiplier as a Doppler ratio. This
file builds the map on the chart of `TwoWayField.hermitian_det_interval` and proves its kernel, its orientation in time
and its two readings on one axis.

[proved-standard; formal-checked] What is proved.

1. **The chart** (§1). `herm (t, x, y, z) = [[t + z, x − iy], [x + iy, t − z]]` is a real-linear equivalence between
   `ℝ⁴` and the Hermitian 2 × 2 complex matrices (`herm_isHermitian`, `coords_herm`, `herm_coords`, `chart`), with
   determinant the interval `t² − x² − y² − z²` (`det_herm`) and its polarization the Minkowski pairing
   (`polarized_det`).
2. **The representation** (§2). `lorentz A` is the real-linear map of `ℝ⁴` that the move `X ↦ Aᴴ X A` induces through
   the chart (`herm_lorentz`). With the move written as in `TwoWayField`, it is a right action: `lorentz 1 = id`
   (`lorentz_one`) and `lorentz (A * B) = lorentz B ∘ lorentz A` (`lorentz_mul`). It scales the pairing by `|det A|²`
   (`mink_lorentz`), so a move with `|det A| = 1` is a Lorentz map (`lorentz_keeps_form`, `lorentz_keeps_form_of_det`),
   with inverse the inverse move's (`lorentz_inv_comp`, `lorentz_comp_inv`).
3. **The kernel** (§3). `lorentz A = id` if and only if `A = c • 1` with `|c| = 1` (`lorentz_eq_id_iff`); at determinant
   one that is `A = 1 ∨ A = −1` (`lorentz_eq_id_iff_of_det`), and two moves of determinant one give one Lorentz map
   if and only if they agree up to sign (`lorentz_eq_iff`). So the map from `SL(2, ℂ)` descends to the quotient by `±1`
   and is injective there.
4. **Orientation in time and in space** (§4). The time-time entry is half the sum of the squared moduli of the
   move's entries (`lorentz_time_time`), at least `|det A|` (`norm_det_le_time_time`), so at least one for a move with
   `|det A| = 1` (`one_le_time_time`); and such a move keeps the future cone: a displacement with positive time and
   nonnegative interval has positive time after it (`future_kept`, from `lorentz_time` and `future_pairing_pos`). The
   determinant of the map on `ℝ⁴` is `|det A|⁴` (`det_lorentz`), so it is one for such a move (`det_lorentz_eq_one`):
   a move of determinant one gives a proper map that keeps the form and the direction of time
   (`lorentz_proper_orthochronous`).
5. **The multiplier, read twice** (§5). For the diagonal move `diag(λ, λ⁻¹)`, whose multiplier is `K = λ²`
   (`multiplier_eq_modulus_mul_phase`: `K = |λ|² · λ/λ̄`), the two null coordinates scale by `|λ|²` and its inverse and
   the transverse plane `x + iy` turns by the phase `λ/λ̄` (`lorentz_diag_light`): the modulus of the multiplier is the
   Doppler ratio and its argument the turn. The boost `boostZ η = diag(e^(η/2), e^(−η/2))` scales the null directions
   `(1, 0, 0, ±1)` by `e^(±η)` (`boostZ_null_forward`, `boostZ_null_backward`) and is the hyperbolic turn of `(t, z)`
   (`lorentz_boostZ`); its two null multipliers are the two one-way counts of `TwoWayField`, with
   `β = tanh η` (`boostZ_beta`), `(1 + β)/(1 − β) = (e^η)²` (`boostZ_doppler`) and `e^η = √((1 + β)/(1 − β))`
   (`exp_eq_sqrt_doppler`); and `K + K⁻¹ + 2 = tr²/det` at `K = e^η` (`boostZ_multiplier_trace`,
   `diag_multiplier_trace` for any diagonal move), the law of `Geometry/Motion.multiplier_trace_det`. The turn
   `turnZ θ = diag(e^(iθ/2), e^(−iθ/2))` turns the `(x, y)` plane by `θ` and fixes `t` and `z` (`lorentz_turnZ`), and a
   whole turn of the plane is the move `−1` (`turnZ_two_pi`, `turnZ_add_two_pi`, `lorentz_turnZ_add_two_pi`): the half
   angle is the two-to-one cover seen on one axis.
6. **A null form is a pair** (§5). The form `w wᴴ` of a pair `w` has determinant zero (`det_dyad`), a move carries it to
   the form of the moved pair (`move_dyad`), and a pair that the move scales by `μ` has its null form scaled by `|μ|²`
   (`move_dyad_eigen`).

Existing owners, cited and not repeated: `Physics/TwoWayField` (`det_conj_form`, `det_kept`, `form_stays_hermitian`,
`hermitian_det_interval`, `doppler_ratio`, `beta_eq_tanh`), imported and used; `Physics/Spacetime/Boost` (the Doppler
pair `(u, v) ↦ (ku, k⁻¹v)` in the light-cone chart, of which `lorentz_diag_light` is the reading at `k = |λ|²` on the
axis of the move) and `Geometry/Motion` (`multiplier_trace_det` on the Möbius navigator), neither imported.

Limits. The module proves that `A ↦ lorentz A` is a map from the moves of determinant one into the proper maps of
`ℝ⁴` that keep the Minkowski pairing and the future cone, injective on the quotient by `±1`. That every such map is
reached (surjectivity, the other half of `PSL(2, ℂ) ≅ SO⁺(1, 3)`) is not proved here. The construction that closes it:
a proper map keeping the form and the future cone is a turn followed by a boost (its polar decomposition), and
`boostZ` and `turnZ` with their conjugates by turns reach every boost and every turn. The boost and the turn are shown
on the `z` axis only. With the move written `Aᴴ X A` the map reverses products, so the homomorphism of groups is
`A ↦ lorentz A⁻¹` or the map into the opposite group; neither is packaged as a `MonoidHom`. The reading of a receiver's
four dimensions from a complex pair is the record's and is not a statement of this file.

The computational object is the helical pair interaction: the pair `(ξ : η)` is the contact's undivided complex ratio,
its Hermitian forms the contact material, and a move's multiplier carries the boost in its modulus and the turn in its
argument. Of the winding guide's six general objects this touches the pair (the move and its forms), the helix (the
turn about an axis, a circle with the half-angle carry `turnZ (θ + 2π) = −turnZ θ`) and faces and placement (the chart
of a form as a three and one); cell holonomy, the tube and the tower thread stay attached.

Consumers: #410's box for `PSL(2, ℂ) ≅ SO⁺(1, 3)` and the representation that reads a multiplier as a Doppler ratio;
atlas `lorentz.pair-hermitian-signature`, `lorentz.doppler-ratio-chart`, `trace.site-classification`.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.Physics.Spacetime.LorentzCover

open Matrix Complex

/-! ## 1. The chart of a Hermitian form as a three and one -/

/-- [definition] **The chart**: the Hermitian form of the displacement `(t, x, y, z) = (v 0, v 1, v 2, v 3)`. -/
def herm (v : Fin 4 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(v 0 + v 3 : ℂ), v 1 - I * v 2; v 1 + I * v 2, v 0 - v 3]

/-- [definition] The chart read back: time and the three spatial faces of a 2 × 2 complex matrix. -/
def coords (X : Matrix (Fin 2) (Fin 2) ℂ) : Fin 4 → ℝ :=
  ![((X 0 0).re + (X 1 1).re) / 2, (X 1 0).re, (X 1 0).im, ((X 0 0).re - (X 1 1).re) / 2]

/-- [definition] **The Minkowski pairing** `⟨v, w⟩ = v₀w₀ − v₁w₁ − v₂w₂ − v₃w₃`; `mink v v` is the interval. -/
def mink (v w : Fin 4 → ℝ) : ℝ := v 0 * w 0 - v 1 * w 1 - v 2 * w 2 - v 3 * w 3

/-- [definition] The chart's entry at the first end: `t + z`. -/
@[simp] theorem herm_apply_zero_zero (v : Fin 4 → ℝ) : herm v 0 0 = (v 0 + v 3 : ℂ) := rfl

/-- [definition] The chart's entry from the second end to the first: `x − iy`. -/
@[simp] theorem herm_apply_zero_one (v : Fin 4 → ℝ) : herm v 0 1 = (v 1 - I * v 2 : ℂ) := rfl

/-- [definition] The chart's entry from the first end to the second: `x + iy`. -/
@[simp] theorem herm_apply_one_zero (v : Fin 4 → ℝ) : herm v 1 0 = (v 1 + I * v 2 : ℂ) := rfl

/-- [definition] The chart's entry at the second end: `t − z`. -/
@[simp] theorem herm_apply_one_one (v : Fin 4 → ℝ) : herm v 1 1 = (v 0 - v 3 : ℂ) := rfl

/-- [proved-standard] The chart's forms are Hermitian. -/
theorem herm_isHermitian (v : Fin 4 → ℝ) : (herm v).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [conjTranspose_apply]
  ring

/-- [proved-standard] Reading the chart back returns the displacement. -/
theorem coords_herm (v : Fin 4 → ℝ) : coords (herm v) = v := by
  ext i
  fin_cases i <;> simp [coords]

/-- [proved-standard] The chart is one to one. -/
theorem herm_injective : Function.Injective herm :=
  Function.LeftInverse.injective coords_herm

/-- [proved-standard] **Every Hermitian form is in the chart**, at the displacement read back from it. -/
theorem herm_coords {X : Matrix (Fin 2) (Fin 2) ℂ} (hX : X.IsHermitian) : herm (coords X) = X := by
  have h00 := hX.apply 0 0
  have h11 := hX.apply 1 1
  have h01 := hX.apply 0 1
  have e00 : (X 0 0).im = 0 := by
    have := congrArg Complex.im h00
    simp at this
    linarith
  have e11 : (X 1 1).im = 0 := by
    have := congrArg Complex.im h11
    simp at this
    linarith
  have ere : (X 0 1).re = (X 1 0).re := by
    have := congrArg Complex.re h01
    simpa using this.symm
  have eim : (X 0 1).im = -(X 1 0).im := by
    have := congrArg Complex.im h01
    simp at this
    linarith
  ext i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp [coords, e00, e11, ere, eim] <;> ring

/-- [proved-standard] The chart adds. -/
theorem herm_add (v w : Fin 4 → ℝ) : herm (v + w) = herm v + herm w := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

/-- [proved-standard] The chart scales by a real. -/
theorem herm_smul (c : ℝ) (v : Fin 4 → ℝ) : herm (c • v) = c • herm v := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

/-- [proved-standard] The reading adds. -/
theorem coords_add (X Y : Matrix (Fin 2) (Fin 2) ℂ) : coords (X + Y) = coords X + coords Y := by
  ext i
  fin_cases i <;> simp [coords] <;> ring

/-- [proved-standard] The reading scales by a real. -/
theorem coords_smul (c : ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ) : coords (c • X) = c • coords X := by
  ext i
  fin_cases i <;> simp [coords] <;> ring

/-- [proved-standard] **The chart is a real-linear equivalence** between `ℝ⁴` and the Hermitian 2 × 2 complex
matrices. -/
def chart : (Fin 4 → ℝ) ≃ₗ[ℝ] selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ) where
  toFun v := ⟨herm v, herm_isHermitian v⟩
  map_add' v w := Subtype.ext (herm_add v w)
  map_smul' c v := Subtype.ext (herm_smul c v)
  invFun X := coords X.1
  left_inv v := coords_herm v
  right_inv X := Subtype.ext (herm_coords X.2)

/-- [proved-standard] **The determinant of the form is the interval** `t² − x² − y² − z²`. -/
theorem det_herm (v : Fin 4 → ℝ) : (herm v).det = ((mink v v : ℝ) : ℂ) := by
  have h := TwoWayField.hermitian_det_interval (v 0) (v 1) (v 2) (v 3)
  have e : mink v v = v 0 ^ 2 - v 1 ^ 2 - v 2 ^ 2 - v 3 ^ 2 := by unfold mink; ring
  rw [e]
  exact h

/-- [proved-standard] The interval of a sum. -/
theorem mink_add_self (v w : Fin 4 → ℝ) : mink (v + w) (v + w) = mink v v + 2 * mink v w + mink w w := by
  unfold mink
  simp only [Pi.add_apply]
  ring

/-- [proved-standard] **The polarized determinant is the Minkowski pairing**:
`det(X + Y) − det X − det Y = 2⟨v, w⟩`. -/
theorem polarized_det (v w : Fin 4 → ℝ) :
    (herm v + herm w).det - (herm v).det - (herm w).det = ((2 * mink v w : ℝ) : ℂ) := by
  rw [← herm_add, det_herm, det_herm, det_herm, mink_add_self]
  push_cast
  ring

/-! ## 2. The representation -/

/-- [definition] **The Lorentz map of a move**: the real-linear map of `ℝ⁴` that `X ↦ Aᴴ X A` induces through the
chart. -/
def lorentz (A : Matrix (Fin 2) (Fin 2) ℂ) : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ) where
  toFun v := coords (Aᴴ * herm v * A)
  map_add' v w := by rw [herm_add, Matrix.mul_add, Matrix.add_mul, coords_add]
  map_smul' c v := by
    rw [herm_smul, Matrix.mul_smul, Matrix.smul_mul, coords_smul]
    rfl

/-- [proved-standard] **The chart carries the move**: the form of the moved displacement is the moved form. -/
theorem herm_lorentz (A : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 4 → ℝ) :
    herm (lorentz A v) = Aᴴ * herm v * A :=
  herm_coords (TwoWayField.form_stays_hermitian A (herm v) (herm_isHermitian v))

/-- [proved-standard] The identity move is the identity map. -/
theorem lorentz_one : lorentz 1 = LinearMap.id := by
  refine LinearMap.ext fun v => herm_injective ?_
  rw [herm_lorentz]
  simp

/-- [proved-standard] **Moves compose as a right action**: with the move written `Aᴴ X A`,
`lorentz (A * B) = lorentz B ∘ lorentz A`. -/
theorem lorentz_mul (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    lorentz (A * B) = lorentz B ∘ₗ lorentz A := by
  refine LinearMap.ext fun v => herm_injective ?_
  rw [LinearMap.comp_apply, herm_lorentz, herm_lorentz, herm_lorentz, conjTranspose_mul]
  simp only [Matrix.mul_assoc]

/-- [proved-standard] The interval scales by `|det A|²`. -/
theorem mink_self_lorentz (A : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 4 → ℝ) :
    mink (lorentz A v) (lorentz A v) = Complex.normSq A.det * mink v v := by
  have h := det_herm (lorentz A v)
  rw [herm_lorentz, TwoWayField.det_conj_form, det_herm] at h
  have h2 : ((Complex.normSq A.det * mink v v : ℝ) : ℂ) = ((mink (lorentz A v) (lorentz A v) : ℝ) : ℂ) := by
    rw [← h, Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self]
    simp only [Complex.star_def]
    ring
  exact_mod_cast h2.symm

/-- [proved-standard] **The pairing scales by `|det A|²`.** -/
theorem mink_lorentz (A : Matrix (Fin 2) (Fin 2) ℂ) (v w : Fin 4 → ℝ) :
    mink (lorentz A v) (lorentz A w) = Complex.normSq A.det * mink v w := by
  have hs := mink_self_lorentz A (v + w)
  rw [map_add, mink_add_self, mink_add_self, mink_self_lorentz, mink_self_lorentz] at hs
  linarith

/-- [proved-standard] **A move with `|det A| = 1` is a Lorentz map.** -/
theorem lorentz_keeps_form {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : ‖A.det‖ = 1) (v w : Fin 4 → ℝ) :
    mink (lorentz A v) (lorentz A w) = mink v w := by
  rw [mink_lorentz, Complex.normSq_eq_norm_sq, hA]
  ring

/-- [proved-standard] A move of determinant one is a Lorentz map. -/
theorem lorentz_keeps_form_of_det {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.det = 1) (v w : Fin 4 → ℝ) :
    mink (lorentz A v) (lorentz A w) = mink v w :=
  lorentz_keeps_form (by rw [hA, norm_one]) v w

/-- [proved-standard] The inverse move undoes the map, on one side. -/
theorem lorentz_inv_comp {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : IsUnit A.det) :
    lorentz A⁻¹ ∘ₗ lorentz A = LinearMap.id := by
  rw [← lorentz_mul, Matrix.mul_nonsing_inv A hA, lorentz_one]

/-- [proved-standard] The inverse move undoes the map, on the other side. -/
theorem lorentz_comp_inv {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : IsUnit A.det) :
    lorentz A ∘ₗ lorentz A⁻¹ = LinearMap.id := by
  rw [← lorentz_mul, Matrix.nonsing_inv_mul A hA, lorentz_one]

/-! ## 3. The kernel: a move and its negative give one Lorentz map, and no other pair does -/

/-- [definition] The unit of time `(1, 0, 0, 0)`. -/
def e0 : Fin 4 → ℝ := ![1, 0, 0, 0]

/-- [definition] The unit of the `x` axis. -/
def e1 : Fin 4 → ℝ := ![0, 1, 0, 0]

/-- [definition] The unit of the `z` axis. -/
def e3 : Fin 4 → ℝ := ![0, 0, 0, 1]

/-- [proved-standard] The unit of time is the identity form. -/
theorem herm_e0 : herm e0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e0]

/-- [proved-standard] The unit of `x` is the exchange of the pair's two ends. -/
theorem herm_e1 : herm e1 = !![0, 1; 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e1]

/-- [proved-standard] The unit of `z` is the difference of the pair's two ends. -/
theorem herm_e3 : herm e3 = !![1, 0; 0, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e3]

/-- [proved-standard] A move and its negative give one Lorentz map. -/
theorem lorentz_neg (A : Matrix (Fin 2) (Fin 2) ℂ) : lorentz (-A) = lorentz A := by
  refine LinearMap.ext fun v => herm_injective ?_
  rw [herm_lorentz, herm_lorentz]
  simp

/-- [proved-standard] A phase times the identity moves no form. -/
theorem lorentz_smul_one {c : ℂ} (hc : ‖c‖ = 1) :
    lorentz (c • (1 : Matrix (Fin 2) (Fin 2) ℂ)) = LinearMap.id := by
  refine LinearMap.ext fun v => herm_injective ?_
  have h : star c * c = 1 := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hc]
    simp
  rw [herm_lorentz, conjTranspose_smul, conjTranspose_one, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul,
    Matrix.mul_one, smul_smul, mul_comm, h, one_smul]
  rfl

/-- [proved-standard] **The kernel**: a move gives the identity map if and only if it is a phase times the
identity. -/
theorem lorentz_eq_id_iff (A : Matrix (Fin 2) (Fin 2) ℂ) :
    lorentz A = LinearMap.id ↔ ∃ c : ℂ, ‖c‖ = 1 ∧ A = c • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  constructor
  · intro h
    have hv : ∀ v, Aᴴ * herm v * A = herm v := fun v => by
      rw [← herm_lorentz, h]
      rfl
    have h0 : Aᴴ * A = 1 := by
      have := hv e0
      rwa [herm_e0, Matrix.mul_one] at this
    have h0' : A * Aᴴ = 1 := mul_eq_one_comm.mp h0
    have comm : ∀ v, herm v * A = A * herm v := fun v => by
      have : A * (Aᴴ * herm v * A) = A * herm v := by rw [hv v]
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h0', Matrix.one_mul] at this
      exact this
    have c3 := comm e3
    have c1 := comm e1
    rw [herm_e3] at c3
    rw [herm_e1] at c1
    have a01 : A 0 1 = 0 := by
      have := congrFun (congrFun c3 0) 1
      simp [Matrix.mul_apply, Fin.sum_univ_two] at this
      linear_combination (1 / 2) * this
    have a10 : A 1 0 = 0 := by
      have := congrFun (congrFun c3 1) 0
      simp [Matrix.mul_apply, Fin.sum_univ_two] at this
      linear_combination (-1 / 2) * this
    have a11 : A 1 1 = A 0 0 := by
      have := congrFun (congrFun c1 0) 1
      simp [Matrix.mul_apply, Fin.sum_univ_two] at this
      exact this
    refine ⟨A 0 0, ?_, ?_⟩
    · have := congrFun (congrFun h0 0) 0
      simp [Matrix.mul_apply, Fin.sum_univ_two, a10] at this
      have hn : Complex.normSq (A 0 0) = 1 := by
        have h2 : ((Complex.normSq (A 0 0) : ℝ) : ℂ) = 1 := by
          rw [Complex.normSq_eq_conj_mul_self]
          exact this
        exact_mod_cast h2
      rw [Complex.normSq_eq_norm_sq] at hn
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).mp hn
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [a01, a10, a11]
  · rintro ⟨c, hc, rfl⟩
    exact lorentz_smul_one hc

/-- [proved-standard] **At determinant one the kernel is `±1`.** -/
theorem lorentz_eq_id_iff_of_det {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.det = 1) :
    lorentz A = LinearMap.id ↔ A = 1 ∨ A = -1 := by
  constructor
  · intro h
    obtain ⟨c, -, rfl⟩ := (lorentz_eq_id_iff A).mp h
    have hc : c * c = 1 := by
      simpa [Matrix.det_smul, pow_two] using hA
    rcases mul_self_eq_one_iff.mp hc with rfl | rfl
    · left
      simp
    · right
      simp
  · rintro (rfl | rfl)
    · exact lorentz_one
    · rw [lorentz_neg, lorentz_one]

/-- [proved-standard] **The cover is two to one**: two moves of determinant one give one Lorentz map if and only if
they agree up to sign, so the map from the moves of determinant one is injective on the quotient by `±1`. -/
theorem lorentz_eq_iff {A B : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.det = 1) (hB : B.det = 1) :
    lorentz A = lorentz B ↔ A = B ∨ A = -B := by
  have hBu : IsUnit B.det := by
    rw [hB]
    exact isUnit_one
  constructor
  · intro h
    have hid : lorentz (A * B⁻¹) = LinearMap.id := by
      rw [lorentz_mul, h, ← lorentz_mul, Matrix.mul_nonsing_inv B hBu, lorentz_one]
    have hdet : (A * B⁻¹).det = 1 := by
      rw [det_mul, hA, Matrix.det_nonsing_inv, hB]
      simp
    have hcancel : A * B⁻¹ * B = A := Matrix.nonsing_inv_mul_cancel_right B A hBu
    rcases (lorentz_eq_id_iff_of_det hdet).mp hid with h1 | h1
    · left
      rw [h1, Matrix.one_mul] at hcancel
      exact hcancel.symm
    · right
      rw [h1, neg_mul, Matrix.one_mul] at hcancel
      exact hcancel.symm
  · rintro (rfl | rfl)
    · rfl
    · exact lorentz_neg B

/-! ## 4. Orientation in time -/

/-- [proved-standard] **The time-time entry** is half the sum of the squared moduli of the move's entries,
`½ tr(Aᴴ A)`. -/
theorem lorentz_time_time (A : Matrix (Fin 2) (Fin 2) ℂ) :
    lorentz A e0 0 = (∑ i, ∑ j, Complex.normSq (A i j)) / 2 := by
  show coords (Aᴴ * herm e0 * A) 0 = _
  rw [herm_e0, Matrix.mul_one]
  simp [coords, Matrix.mul_apply, Fin.sum_univ_two, Complex.normSq_apply]
  ring

/-- [proved-standard] The time-time entry is at least `|det A|`. -/
theorem norm_det_le_time_time (A : Matrix (Fin 2) (Fin 2) ℂ) : ‖A.det‖ ≤ lorentz A e0 0 := by
  rw [lorentz_time_time, Matrix.det_fin_two]
  simp only [Fin.sum_univ_two, Complex.normSq_eq_norm_sq]
  have h1 : ‖A 0 0 * A 1 1 - A 0 1 * A 1 0‖ ≤ ‖A 0 0‖ * ‖A 1 1‖ + ‖A 0 1‖ * ‖A 1 0‖ := by
    calc ‖A 0 0 * A 1 1 - A 0 1 * A 1 0‖ ≤ ‖A 0 0 * A 1 1‖ + ‖A 0 1 * A 1 0‖ := norm_sub_le _ _
      _ = ‖A 0 0‖ * ‖A 1 1‖ + ‖A 0 1‖ * ‖A 1 0‖ := by rw [norm_mul, norm_mul]
  nlinarith [sq_nonneg (‖A 0 0‖ - ‖A 1 1‖), sq_nonneg (‖A 0 1‖ - ‖A 1 0‖)]

/-- [proved-standard] **A move with `|det A| = 1` has time-time entry at least one.** -/
theorem one_le_time_time {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : ‖A.det‖ = 1) : 1 ≤ lorentz A e0 0 := by
  rw [← hA]
  exact norm_det_le_time_time A

/-- [proved-standard] The time of a moved displacement is its Euclidean pairing with the displacement
`lorentz Aᴴ e0`, the form `A Aᴴ` read in the chart. -/
theorem lorentz_time (A : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 4 → ℝ) :
    lorentz A v 0 = v 0 * lorentz Aᴴ e0 0 + v 1 * lorentz Aᴴ e0 1 + v 2 * lorentz Aᴴ e0 2 +
      v 3 * lorentz Aᴴ e0 3 := by
  show coords (Aᴴ * herm v * A) 0 = v 0 * coords (Aᴴᴴ * herm e0 * Aᴴ) 0 + v 1 * coords (Aᴴᴴ * herm e0 * Aᴴ) 1 +
    v 2 * coords (Aᴴᴴ * herm e0 * Aᴴ) 2 + v 3 * coords (Aᴴᴴ * herm e0 * Aᴴ) 3
  rw [herm_e0, Matrix.mul_one, conjTranspose_conjTranspose]
  simp [coords, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- [proved-standard] Two displacements in the future cone, one of them inside it, pair positively in the
Euclidean pairing: the reverse Cauchy–Schwarz step. -/
theorem future_pairing_pos {v p : Fin 4 → ℝ} (hv0 : 0 < v 0) (hv : 0 ≤ mink v v) (hp0 : 0 < p 0)
    (hp : 0 < mink p p) : 0 < v 0 * p 0 + v 1 * p 1 + v 2 * p 2 + v 3 * p 3 := by
  unfold mink at hv hp
  have hcs : (v 1 * p 1 + v 2 * p 2 + v 3 * p 3) ^ 2 ≤
      (v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2) * (p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2) := by
    nlinarith [sq_nonneg (v 1 * p 2 - v 2 * p 1), sq_nonneg (v 1 * p 3 - v 3 * p 1),
      sq_nonneg (v 2 * p 3 - v 3 * p 2)]
  have hV : v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2 ≤ v 0 ^ 2 := by nlinarith
  have hP : p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2 < p 0 ^ 2 := by nlinarith
  have hP0 : 0 ≤ p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2 := by positivity
  have hv0sq : 0 < v 0 ^ 2 := by positivity
  have hlt : (v 1 * p 1 + v 2 * p 2 + v 3 * p 3) ^ 2 < (v 0 * p 0) ^ 2 := by
    calc (v 1 * p 1 + v 2 * p 2 + v 3 * p 3) ^ 2
        ≤ (v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2) * (p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2) := hcs
      _ ≤ v 0 ^ 2 * (p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2) := mul_le_mul_of_nonneg_right hV hP0
      _ < v 0 ^ 2 * p 0 ^ 2 := mul_lt_mul_of_pos_left hP hv0sq
      _ = (v 0 * p 0) ^ 2 := by ring
  have h := abs_lt_of_sq_lt_sq' hlt (by positivity)
  linarith [h.1]

/-- [proved-standard] **A move with `|det A| = 1` keeps the future cone**: a displacement with positive time and
nonnegative interval has positive time after the move. -/
theorem future_kept {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : ‖A.det‖ = 1) {v : Fin 4 → ℝ} (hv0 : 0 < v 0)
    (hv : 0 ≤ mink v v) : 0 < lorentz A v 0 := by
  have hA' : ‖Aᴴ.det‖ = 1 := by
    rw [det_conjTranspose, norm_star, hA]
  rw [lorentz_time]
  refine future_pairing_pos hv0 hv (lt_of_lt_of_le one_pos (one_le_time_time hA')) ?_
  rw [mink_self_lorentz, Complex.normSq_eq_norm_sq, hA']
  simp [mink, e0]

/-- [proved-standard] **The determinant of the Lorentz map is `|det A|⁴`**, by expanding the four by four
determinant in the real and imaginary parts of the move's entries. -/
theorem det_lorentz (A : Matrix (Fin 2) (Fin 2) ℂ) :
    LinearMap.det (lorentz A) = Complex.normSq A.det ^ 2 := by
  have happ : ∀ (v : Fin 4 → ℝ) (i : Fin 4), lorentz A v i = coords (Aᴴ * herm v * A) i := fun _ _ => rfl
  rw [← LinearMap.det_toMatrix']
  simp [-LinearMap.det_toMatrix', Matrix.det_succ_row_zero, Fin.sum_univ_succ, LinearMap.toMatrix'_apply, happ,
    coords, Matrix.mul_apply, Pi.single_apply, Complex.normSq_apply, Fin.succAbove]
  ring

/-- [proved-standard] **A move with `|det A| = 1` gives a proper map**: its determinant on `ℝ⁴` is one. -/
theorem det_lorentz_eq_one {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : ‖A.det‖ = 1) : LinearMap.det (lorentz A) = 1 := by
  rw [det_lorentz, Complex.normSq_eq_norm_sq, hA]
  norm_num

/-- [proved-standard] **A move of determinant one gives a proper map that keeps the form and the direction of
time**: the three conditions of `SO⁺(1, 3)`. -/
theorem lorentz_proper_orthochronous {A : Matrix (Fin 2) (Fin 2) ℂ} (hA : A.det = 1) :
    (∀ v w, mink (lorentz A v) (lorentz A w) = mink v w) ∧ LinearMap.det (lorentz A) = 1 ∧
      1 ≤ lorentz A e0 0 := by
  have h : ‖A.det‖ = 1 := by rw [hA, norm_one]
  exact ⟨lorentz_keeps_form h, det_lorentz_eq_one h, one_le_time_time h⟩

/-! ## 5. The multiplier, read twice: its modulus is the Doppler ratio and its argument the turn -/

open scoped ComplexConjugate

/-- [proved-standard] A diagonal move scales each entry of a form by its two ends' factors. -/
theorem diag_move (a d : ℂ) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    (!![a, 0; 0, d])ᴴ * X * !![a, 0; 0, d] =
      !![conj a * X 0 0 * a, conj a * X 0 1 * d; conj d * X 1 0 * a, conj d * X 1 1 * d] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- [proved-standard] **The multiplier of `diag(λ, λ⁻¹)` is its modulus times its phase**:
`K = λ/λ⁻¹ = |λ|² · λ/λ̄`. -/
theorem multiplier_eq_modulus_mul_phase {l : ℂ} (hl : l ≠ 0) :
    l / l⁻¹ = (Complex.normSq l : ℂ) * (l / conj l) := by
  have hc : conj l ≠ 0 := by simpa using hl
  rw [Complex.normSq_eq_conj_mul_self]
  field_simp

/-- [proved-standard] The phase `λ/λ̄` has modulus one. -/
theorem phase_norm {l : ℂ} (hl : l ≠ 0) : ‖l / conj l‖ = 1 := by
  rw [norm_div, RCLike.norm_conj, div_self (norm_ne_zero_iff.mpr hl)]

/-- [proved-standard] **The representation reads the multiplier twice.** Under `diag(λ, λ⁻¹)` the null coordinate
`t + z` scales by `|λ|²`, the null coordinate `t − z` by its inverse, and the transverse plane `x + iy` turns by
the phase `λ/λ̄`. -/
theorem lorentz_diag_light {l : ℂ} (hl : l ≠ 0) (v : Fin 4 → ℝ) :
    lorentz !![l, 0; 0, l⁻¹] v 0 + lorentz !![l, 0; 0, l⁻¹] v 3 = Complex.normSq l * (v 0 + v 3) ∧
    lorentz !![l, 0; 0, l⁻¹] v 0 - lorentz !![l, 0; 0, l⁻¹] v 3 = (Complex.normSq l)⁻¹ * (v 0 - v 3) ∧
    ((lorentz !![l, 0; 0, l⁻¹] v 1 : ℝ) : ℂ) + I * ((lorentz !![l, 0; 0, l⁻¹] v 2 : ℝ) : ℂ) =
      l / conj l * (v 1 + I * v 2) := by
  have hc : conj l ≠ 0 := by simpa using hl
  have h := herm_lorentz !![l, 0; 0, l⁻¹] v
  rw [diag_move] at h
  set w := lorentz !![l, 0; 0, l⁻¹] v with hw
  have h00 := congrFun (congrFun h 0) 0
  have h11 := congrFun (congrFun h 1) 1
  have h10 := congrFun (congrFun h 1) 0
  simp at h00 h11 h10
  refine ⟨?_, ?_, ?_⟩
  · have h2 : ((w 0 + w 3 : ℝ) : ℂ) = ((Complex.normSq l * (v 0 + v 3) : ℝ) : ℂ) := by
      push_cast
      rw [h00, Complex.normSq_eq_conj_mul_self]
      ring
    exact_mod_cast h2
  · have h2 : ((w 0 - w 3 : ℝ) : ℂ) = (((Complex.normSq l)⁻¹ * (v 0 - v 3) : ℝ) : ℂ) := by
      push_cast
      rw [h11, Complex.normSq_eq_conj_mul_self]
      field_simp
    exact_mod_cast h2
  · rw [h10]
    field_simp

/-- [proved-standard] **`K + K⁻¹ + 2 = tr²/det` on a diagonal move**, `K = a/d`: the law of
`Geometry/Motion.multiplier_trace_det` read on the matrix of the move. -/
theorem diag_multiplier_trace {a d : ℂ} (ha : a ≠ 0) (hd : d ≠ 0) :
    a / d + d / a + 2 = (!![a, 0; 0, d]).trace ^ 2 / (!![a, 0; 0, d]).det := by
  rw [Matrix.trace_fin_two_of, Matrix.det_fin_two_of]
  field_simp
  ring

/-- [definition] **The boost along `z`** at rapidity `η`: the move `diag(e^(η/2), e^(−η/2))`. -/
def boostZ (η : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![((Real.exp (η / 2) : ℝ) : ℂ), 0; 0, ((Real.exp (η / 2) : ℝ) : ℂ)⁻¹]

/-- [proved-standard] The boost's factor is not zero. -/
private theorem exp_half_ne (η : ℝ) : ((Real.exp (η / 2) : ℝ) : ℂ) ≠ 0 := by
  exact_mod_cast (Real.exp_pos (η / 2)).ne'

/-- [proved-standard] The boost's factor squares to `e^η`. -/
private theorem exp_half_mul (η : ℝ) : Real.exp (η / 2) * Real.exp (η / 2) = Real.exp η := by
  rw [← Real.exp_add]
  congr 1
  ring

/-- [proved-standard] The boost has determinant one. -/
theorem det_boostZ (η : ℝ) : (boostZ η).det = 1 := by
  unfold boostZ
  rw [Matrix.det_fin_two_of]
  simp

/-- [proved-standard] **The boost is the Doppler pair on its axis**: `t + z` scales by `e^η`, `t − z` by `e^(−η)`,
and the transverse plane is fixed. -/
theorem lorentz_boostZ_light (η : ℝ) (v : Fin 4 → ℝ) :
    lorentz (boostZ η) v 0 + lorentz (boostZ η) v 3 = Real.exp η * (v 0 + v 3) ∧
    lorentz (boostZ η) v 0 - lorentz (boostZ η) v 3 = Real.exp (-η) * (v 0 - v 3) ∧
    lorentz (boostZ η) v 1 = v 1 ∧ lorentz (boostZ η) v 2 = v 2 := by
  have key := lorentz_diag_light (exp_half_ne η) v
  have hw : lorentz !![((Real.exp (η / 2) : ℝ) : ℂ), 0; 0, ((Real.exp (η / 2) : ℝ) : ℂ)⁻¹] v =
      lorentz (boostZ η) v := rfl
  rw [hw] at key
  generalize lorentz (boostZ η) v = w at key ⊢
  obtain ⟨h1, h2, h3⟩ := key
  have hn : Complex.normSq ((Real.exp (η / 2) : ℝ) : ℂ) = Real.exp η := by
    rw [Complex.normSq_ofReal, exp_half_mul]
  rw [hn] at h1 h2
  have hph : ((Real.exp (η / 2) : ℝ) : ℂ) / conj ((Real.exp (η / 2) : ℝ) : ℂ) = 1 := by
    rw [Complex.conj_ofReal, div_self (exp_half_ne η)]
  rw [hph, one_mul] at h3
  refine ⟨h1, ?_, ?_, ?_⟩
  · rw [Real.exp_neg]
    exact h2
  · have := congrArg Complex.re h3
    simpa using this
  · have := congrArg Complex.im h3
    simpa using this

/-- [proved-standard] **The boost is the hyperbolic turn of `(t, z)`.** -/
theorem lorentz_boostZ (η : ℝ) (v : Fin 4 → ℝ) :
    lorentz (boostZ η) v =
      ![Real.cosh η * v 0 + Real.sinh η * v 3, v 1, v 2, Real.sinh η * v 0 + Real.cosh η * v 3] := by
  obtain ⟨h1, h2, h3, h4⟩ := lorentz_boostZ_light η v
  ext i
  fin_cases i
  · show lorentz (boostZ η) v 0 = Real.cosh η * v 0 + Real.sinh η * v 3
    rw [Real.cosh_eq, Real.sinh_eq]
    linear_combination (1 / 2) * h1 + (1 / 2) * h2
  · exact h3
  · exact h4
  · show lorentz (boostZ η) v 3 = Real.sinh η * v 0 + Real.cosh η * v 3
    rw [Real.cosh_eq, Real.sinh_eq]
    linear_combination (1 / 2) * h1 - (1 / 2) * h2

/-- [proved-standard] **The forward null direction scales by the Doppler ratio `e^η`.** -/
theorem boostZ_null_forward (η : ℝ) :
    lorentz (boostZ η) ![1, 0, 0, 1] = Real.exp η • ![1, 0, 0, 1] := by
  rw [lorentz_boostZ]
  ext i
  fin_cases i <;> simp [Real.cosh_add_sinh, Real.sinh_add_cosh]

/-- [proved-standard] **The backward null direction scales by `e^(−η)`.** -/
theorem boostZ_null_backward (η : ℝ) :
    lorentz (boostZ η) ![1, 0, 0, -1] = Real.exp (-η) • ![1, 0, 0, -1] := by
  rw [lorentz_boostZ]
  ext i
  fin_cases i <;> simp [Real.cosh_eq, Real.sinh_eq] <;> ring

/-- [proved-standard] The boost's two null multipliers are a contact's two one-way counts, and their `β` is
`tanh η`. -/
theorem boostZ_beta (η : ℝ) : TwoWayField.beta (Real.exp η) (Real.exp (-η)) = Real.tanh η := by
  have h := TwoWayField.beta_eq_tanh (Real.exp_pos η) (Real.exp_pos (-η))
  have hl : TwoWayField.logOdd (Real.exp η) (Real.exp (-η)) = η := by
    unfold TwoWayField.logOdd
    rw [← Real.exp_sub, Real.log_exp]
    ring
  rw [h, hl]

/-- [proved-standard] **The Doppler factor of the boost's velocity is the square of its null multiplier**:
`(1 + β)/(1 − β) = (e^η)²` at `β = tanh η`. -/
theorem boostZ_doppler (η : ℝ) : (1 + Real.tanh η) / (1 - Real.tanh η) = Real.exp η ^ 2 := by
  have h := TwoWayField.doppler_ratio (Real.exp_pos η) (Real.exp_pos (-η))
  rw [boostZ_beta] at h
  rw [h, Real.exp_neg, div_inv_eq_mul, sq]

/-- [proved-standard] **The null multiplier is the Doppler ratio** `e^η = √((1 + β)/(1 − β))`. -/
theorem exp_eq_sqrt_doppler (η : ℝ) :
    Real.exp η = Real.sqrt ((1 + Real.tanh η) / (1 - Real.tanh η)) := by
  rw [boostZ_doppler, Real.sqrt_sq (Real.exp_pos η).le]

/-- [proved-standard] **`K + K⁻¹ + 2 = tr²/det` at the boost**, `K = e^η` its null multiplier. -/
theorem boostZ_multiplier_trace (η : ℝ) :
    ((Real.exp η : ℝ) : ℂ) + ((Real.exp η : ℝ) : ℂ)⁻¹ + 2 = (boostZ η).trace ^ 2 / (boostZ η).det := by
  have hl := exp_half_ne η
  have he : ((Real.exp η : ℝ) : ℂ) = ((Real.exp (η / 2) : ℝ) : ℂ) * ((Real.exp (η / 2) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, exp_half_mul]
  unfold boostZ
  rw [← diag_multiplier_trace hl (inv_ne_zero hl), he]
  field_simp

/-- [definition] **The turn about `z`** by `θ`: the move `diag(e^(iθ/2), e^(−iθ/2))`. -/
def turnZ (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.exp ((θ / 2 : ℝ) * I), 0; 0, (Complex.exp ((θ / 2 : ℝ) * I))⁻¹]

/-- [proved-standard] The turn has determinant one. -/
theorem det_turnZ (θ : ℝ) : (turnZ θ).det = 1 := by
  unfold turnZ
  rw [Matrix.det_fin_two_of]
  simp [Complex.exp_ne_zero]

/-- [proved-standard] **The turn turns the `(x, y)` plane by `θ` and fixes `t` and `z`**: the move's half angle
is the plane's whole angle. -/
theorem lorentz_turnZ (θ : ℝ) (v : Fin 4 → ℝ) :
    lorentz (turnZ θ) v =
      ![v 0, Real.cos θ * v 1 - Real.sin θ * v 2, Real.sin θ * v 1 + Real.cos θ * v 2, v 3] := by
  have key := lorentz_diag_light (Complex.exp_ne_zero ((θ / 2 : ℝ) * I)) v
  have hw : lorentz !![Complex.exp ((θ / 2 : ℝ) * I), 0; 0, (Complex.exp ((θ / 2 : ℝ) * I))⁻¹] v =
      lorentz (turnZ θ) v := rfl
  rw [hw] at key
  generalize lorentz (turnZ θ) v = w at key ⊢
  obtain ⟨h1, h2, h3⟩ := key
  have hn : Complex.normSq (Complex.exp ((θ / 2 : ℝ) * I)) = 1 := by
    rw [Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]
    norm_num
  rw [hn, one_mul] at h1
  rw [hn, inv_one, one_mul] at h2
  have hcj : conj (((θ / 2 : ℝ) : ℂ) * I) = -(((θ / 2 : ℝ) : ℂ) * I) := by
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  have hph : Complex.exp ((θ / 2 : ℝ) * I) / conj (Complex.exp ((θ / 2 : ℝ) * I)) =
      Complex.exp ((θ : ℝ) * I) := by
    rw [← Complex.exp_conj, hcj, ← Complex.exp_sub]
    congr 1
    push_cast
    ring
  rw [hph] at h3
  have hre := congrArg Complex.re h3
  have him := congrArg Complex.im h3
  simp [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im] at hre him
  ext i
  fin_cases i
  · show w 0 = v 0
    linarith
  · show w 1 = Real.cos θ * v 1 - Real.sin θ * v 2
    linarith
  · show w 2 = Real.sin θ * v 1 + Real.cos θ * v 2
    linarith
  · show w 3 = v 3
    linarith

/-- [proved-standard] **A whole turn of the plane is the negative of the move.** -/
theorem turnZ_add_two_pi (θ : ℝ) : turnZ (θ + 2 * Real.pi) = -turnZ θ := by
  have h : Complex.exp (((θ + 2 * Real.pi) / 2 : ℝ) * I) = -Complex.exp ((θ / 2 : ℝ) * I) := by
    have : (((θ + 2 * Real.pi) / 2 : ℝ) : ℂ) * I = (θ / 2 : ℝ) * I + Real.pi * I := by
      push_cast
      ring
    rw [this, Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  unfold turnZ
  rw [h]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [inv_neg]

/-- [proved-standard] The turn by `2π` is the move `−1`. -/
theorem turnZ_two_pi : turnZ (2 * Real.pi) = -1 := by
  have h := turnZ_add_two_pi 0
  rw [zero_add] at h
  rw [h]
  unfold turnZ
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- [proved-standard] **The cover on one axis**: the turns by `θ` and by `θ + 2π` are two moves and one Lorentz
map. -/
theorem lorentz_turnZ_add_two_pi (θ : ℝ) : lorentz (turnZ (θ + 2 * Real.pi)) = lorentz (turnZ θ) := by
  rw [turnZ_add_two_pi, lorentz_neg]

/-- [proved-standard] **A pair's form is null**: `det (w wᴴ) = 0`. -/
theorem det_dyad (w : Fin 2 → ℂ) : (vecMulVec w (star w)).det = 0 := by
  rw [Matrix.det_fin_two]
  simp [vecMulVec_apply]
  ring

/-- [proved-standard] **A move carries a pair's form to the moved pair's form.** -/
theorem move_dyad (A : Matrix (Fin 2) (Fin 2) ℂ) (w : Fin 2 → ℂ) :
    Aᴴ * vecMulVec w (star w) * A = vecMulVec (Aᴴ *ᵥ w) (star (Aᴴ *ᵥ w)) := by
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, star_mulVec, conjTranspose_conjTranspose]

/-- [proved-standard] **A pair the move scales by `μ` has its null form scaled by `|μ|²`**: the modulus of a
multiplier read as a Doppler ratio, on any axis. -/
theorem move_dyad_eigen {A : Matrix (Fin 2) (Fin 2) ℂ} {w : Fin 2 → ℂ} {μ : ℂ} (h : Aᴴ *ᵥ w = μ • w) :
    Aᴴ * vecMulVec w (star w) * A = (Complex.normSq μ : ℂ) • vecMulVec w (star w) := by
  rw [move_dyad, h]
  ext i j
  simp [vecMulVec_apply, Complex.normSq_eq_conj_mul_self]
  ring

end Holonics.Physics.Spacetime.LorentzCover
