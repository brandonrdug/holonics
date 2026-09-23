import ElementaryHolonics.Holon.Reaction
import ElementaryHolonics.Holon.Deposition
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Holon.Cayley: the implicit reaction step, its isometry, and certified shifts

[definition] The native finding: a reaction with zero continuous work still runs away when the
discrete word applies it explicitly — the gain grows at second order with `‖J(c)‖ ∝ |Δ|`. The
incident word is therefore an implicit-midpoint (Cayley) step.

[proved-derived; formal-checked]

1. **The Cayley step is an isometry.** For skew-Hermitian `J` and real `h`, `I − ½hJ` is invertible
   (`cayley_denominator_det`) and `C = (I − ½hJ)⁻¹(I + ½hJ)` preserves `⟨s, s⟩` for every `s`
   (`cayley_isometry`, from `cayley_isometry_rel`): the reaction step has gain exactly `1` whatever
   the contrast. The realified form holds for every real skew `J` (`cayley_isometry_real`).
2. **Midpoint with resistance.** For `ẋ = (J − R)x`, the implicit midpoint step gives
   `½|x⁺|² − ½|x|² = −h⟨x̄, R x̄⟩ ≤ 0` (`midpoint_reaction_balance`, composing `midpoint_balance`).
3. **The explicit step grows.** `x⁺ = (I + hJ)x` with skew-Hermitian `J` has
   `|x⁺|² = |x|² + h²|Jx|²` (`explicit_step_growth`); with `J` proportional to the state the gain
   `1 + h²s²` grows with the energy (`explicit_growth_witness`).
4. **The minimal certified shift** (realified real form). `⟨v, W v⟩ ≤ λ_max(sym W)|v|²`
   (`rayleigh_le`), and `W − τI` is passive exactly when `τ ≥ λ_max(sym W)` (`shift_passive_iff`);
   the shifted blocks restore the committed-energy bound (`shifted_committed_energy_bound`).
5. **Chart containment.** Re-centring `(c, r) → (c', r')` with `‖c − c'‖ ≤ r' − r` keeps the exact
   state contained (`recentre_contains`); along device steps with `‖L_k‖ ≤ K_k` and
   `‖L_k c_k − c_(k+1)‖ ≤ r_(k+1) − K_k r_k`, containment propagates (`device_containment`,
   composing `ball_image`).
-/

noncomputable section

namespace Soma.Holonics.HolonCore

open Matrix ComplexConjugate

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## 0. The Hermitian norm -/

omit [DecidableEq n] in
theorem herm_self_re (v : n → ℂ) : (herm v v).re = ∑ i, Complex.normSq (v i) := by
  simp [herm, dotProduct, Complex.re_sum, Complex.normSq_apply, Complex.mul_re]

omit [DecidableEq n] in
theorem eq_zero_of_herm_self_re {v : n → ℂ} (h : (herm v v).re = 0) : v = 0 := by
  rw [herm_self_re] at h
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Complex.normSq_nonneg (v i))).mp h
  funext i
  exact Complex.normSq_eq_zero.mp (this i (Finset.mem_univ i))

omit [DecidableEq n] in
theorem re_herm_swap (s y : n → ℂ) : (herm s y).re = (herm y s).re := by
  simp only [herm, dotProduct, Complex.re_sum, Pi.star_apply, Complex.star_def, Complex.mul_re,
    Complex.conj_re, Complex.conj_im]
  refine Finset.sum_congr rfl fun i _ => by ring

omit [DecidableEq n] in
theorem herm_add_left (a b v : n → ℂ) : herm (a + b) v = herm a v + herm b v := by
  simp [herm, star_add, add_dotProduct]

omit [DecidableEq n] in
theorem herm_sub_right (a v w : n → ℂ) : herm a (v - w) = herm a v - herm a w := by
  simp [herm, dotProduct_sub]

omit [DecidableEq n] in
theorem herm_smul_right (a v : n → ℂ) (z : ℂ) : herm a (z • v) = z * herm a v := by
  simp [herm, dotProduct_smul]

/-! ## 1. The Cayley step is an isometry -/

/-- [proved-derived; formal-checked] For skew-Hermitian `J` and real `a`, `I − aJ` is invertible. -/
theorem cayley_denominator_det {J : Matrix n n ℂ} (hJ : Jᴴ = -J) (a : ℝ) :
    (1 - (a : ℂ) • J).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hker⟩ := (Matrix.exists_mulVec_eq_zero_iff).mpr hdet
  have hvJ : v = (a : ℂ) • (J *ᵥ v) := by
    rw [sub_mulVec, one_mulVec, smul_mulVec, sub_eq_zero] at hker; exact hker
  have h1 : (herm v v).re = a * (herm v (J *ᵥ v)).re := by
    conv_lhs => rw [show herm v v = herm v ((a : ℂ) • (J *ᵥ v)) by rw [← hvJ]]
    rw [herm_smul_right, Complex.re_ofReal_mul]
  rw [re_herm_skew hJ, mul_zero] at h1
  exact hv (eq_zero_of_herm_self_re h1)

/-- [proved-derived; formal-checked] **The Cayley relation preserves the norm.** If
`(I − aJ) y = (I + aJ) s` with `J` skew-Hermitian and `a` real, then `|y|² = |s|²`. -/
theorem cayley_isometry_rel {J : Matrix n n ℂ} (hJ : Jᴴ = -J) (a : ℝ) {s y : n → ℂ}
    (h : (1 - (a : ℂ) • J) *ᵥ y = (1 + (a : ℂ) • J) *ᵥ s) :
    (herm y y).re = (herm s s).re := by
  have hd : y - s = (a : ℂ) • (J *ᵥ (y + s)) := by
    rw [sub_mulVec, add_mulVec, one_mulVec, one_mulVec, smul_mulVec, smul_mulVec] at h
    rw [mulVec_add, smul_add]
    calc y - s = (y - (a : ℂ) • (J *ᵥ y)) + (a : ℂ) • (J *ᵥ y) - s := by abel
      _ = (s + (a : ℂ) • (J *ᵥ s)) + (a : ℂ) • (J *ᵥ y) - s := by rw [h]
      _ = _ := by abel
  have hkey : (herm (y + s) (y - s)).re = 0 := by
    rw [hd, herm_smul_right, Complex.re_ofReal_mul, re_herm_skew hJ, mul_zero]
  rw [herm_add_left, herm_sub_right, herm_sub_right, Complex.add_re, Complex.sub_re,
    Complex.sub_re, re_herm_swap y s] at hkey
  linarith

/-- [definition] **The Cayley (implicit-midpoint) step** `C = (I − ½hJ)⁻¹ (I + ½hJ)`. -/
def cayley (J : Matrix n n ℂ) (h : ℝ) : Matrix n n ℂ :=
  (1 - ((h / 2 : ℝ) : ℂ) • J)⁻¹ * (1 + ((h / 2 : ℝ) : ℂ) • J)

/-- [proved-derived; formal-checked] **The reaction step has gain exactly one.** For every
skew-Hermitian `J` — however large, whatever the contrast that produced it — and every real `h`,
`|C s|² = |s|²`. -/
theorem cayley_isometry {J : Matrix n n ℂ} (hJ : Jᴴ = -J) (h : ℝ) (s : n → ℂ) :
    (herm (cayley J h *ᵥ s) (cayley J h *ᵥ s)).re = (herm s s).re := by
  apply cayley_isometry_rel hJ (h / 2)
  rw [cayley, mulVec_mulVec, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp
      (Matrix.isUnit_iff_isUnit_det _ |>.mpr (isUnit_iff_ne_zero.mpr
        (cayley_denominator_det hJ (h / 2))))), Matrix.one_mul]

/-- [proved-derived; formal-checked] **The realified Cayley relation preserves the norm**: for real
skew `J` (e.g. `realify` of a skew-Hermitian reaction) and real `a`, `(I − aJ)y = (I + aJ)s`
implies `|y|² = |s|²`. -/
theorem cayley_isometry_real {m : Type*} [Fintype m] [DecidableEq m] {J : Matrix m m ℝ}
    (hJ : Jᵀ = -J) (a : ℝ) {s y : m → ℝ} (h : (1 - a • J) *ᵥ y = (1 + a • J) *ᵥ s) :
    y ⬝ᵥ y = s ⬝ᵥ s := by
  have hd : y - s = a • (J *ᵥ (y + s)) := by
    rw [sub_mulVec, add_mulVec, one_mulVec, one_mulVec, smul_mulVec, smul_mulVec] at h
    rw [mulVec_add, smul_add]
    calc y - s = (y - a • (J *ᵥ y)) + a • (J *ᵥ y) - s := by abel
      _ = (s + a • (J *ᵥ s)) + a • (J *ᵥ y) - s := by rw [h]
      _ = _ := by abel
  have hskew : (y + s) ⬝ᵥ (J *ᵥ (y + s)) = 0 := by
    have := skew_dot hJ (y + s) (y + s); linarith
  have hkey : (y + s) ⬝ᵥ (y - s) = 0 := by
    rw [hd, dotProduct_smul, hskew, smul_zero]
  rw [add_dotProduct, dotProduct_sub, dotProduct_sub, dotProduct_comm s y] at hkey
  linarith

/-! ## 2. The implicit midpoint with resistance -/

/-- [proved-derived; formal-checked] **Midpoint with resistance** (real form, composing
`midpoint_balance` at `Q = 1`, no input): `½|x⁺|² − ½|x|² = −h⟨x̄, R x̄⟩`, which is `≤ 0` for
`R ⪰ 0`, `h ≥ 0`, whatever the skew part. -/
theorem midpoint_reaction_balance {m : Type*} [Fintype m] [DecidableEq m] {J R : Matrix m m ℝ} (hJ : Jᵀ = -J)
    (h : ℝ) (hh : 0 ≤ h) (hR : ∀ e, 0 ≤ e ⬝ᵥ (R *ᵥ e)) (x x' : m → ℝ)
    (hstep : x' - x = h • ((J - R) *ᵥ ((1 / 2 : ℝ) • (x + x')))) :
    storageEnergy 1 x' - storageEnergy 1 x =
        -(h * (((1 / 2 : ℝ) • (x + x')) ⬝ᵥ (R *ᵥ ((1 / 2 : ℝ) • (x + x'))))) ∧
      storageEnergy 1 x' - storageEnergy 1 x ≤ 0 := by
  have hstep' : x' - x = h • ((J - R) *ᵥ ((1 : Matrix m m ℝ) *ᵥ ((1 / 2 : ℝ) • (x + x'))) +
      (0 : Matrix m (Fin 0) ℝ) *ᵥ 0) := by
    rw [hstep]; simp
  have hb := midpoint_balance Matrix.transpose_one hJ 0 h x x' 0 hstep'
  simp only [one_mulVec, zero_mulVec, dotProduct_zero, mul_zero, add_zero] at hb
  refine ⟨hb, ?_⟩
  rw [hb]
  have := mul_nonneg hh (hR ((1 / 2 : ℝ) • (x + x')))
  linarith

/-! ## 3. The explicit step grows at second order -/

omit [DecidableEq n] in
/-- [proved-derived; formal-checked] **The explicit reaction step is not an isometry.** For
skew-Hermitian `J`, `x⁺ = (I + hJ) x` has `|x⁺|² = |x|² + h²|Jx|²`. -/
theorem explicit_step_growth {J : Matrix n n ℂ} (hJ : Jᴴ = -J) (h : ℝ) (x : n → ℂ) :
    (herm (x + (h : ℂ) • (J *ᵥ x)) (x + (h : ℂ) • (J *ᵥ x))).re =
      (herm x x).re + h ^ 2 * (herm (J *ᵥ x) (J *ᵥ x)).re := by
  have e : herm (x + (h : ℂ) • (J *ᵥ x)) (x + (h : ℂ) • (J *ᵥ x)) =
      herm x x + (h : ℂ) * herm x (J *ᵥ x) + (h : ℂ) * herm (J *ᵥ x) x +
        (h : ℂ) * (h : ℂ) * herm (J *ᵥ x) (J *ᵥ x) := by
    simp only [herm, star_add, star_smul, add_dotProduct, dotProduct_add, smul_dotProduct,
      dotProduct_smul, Complex.star_def, Complex.conj_ofReal, smul_eq_mul]
    ring
  rw [e]
  simp only [Complex.add_re, Complex.re_ofReal_mul, ← Complex.ofReal_mul]
  rw [re_herm_swap (J *ᵥ x) x, re_herm_skew hJ]
  ring

/-- [counterexample; formal-checked] **Witness: the gain grows with the state.** With the contrast
equal to the amplitude, `J = s·[[0, −1], [1, 0]]` at the state `(s, 0)`: the explicit step returns
`(s, h s²)` of squared norm `s² (1 + h² s²)`, so the per-step gain `1 + h²s²` exceeds `1` and grows
with the energy, while the Cayley step keeps the norm. -/
theorem explicit_growth_witness (h s : ℝ) :
    (![s, 0] + h • ((s • (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ)) *ᵥ ![s, 0])) = ![s, h * s ^ 2] ∧
      (![s, h * s ^ 2] : Fin 2 → ℝ) ⬝ᵥ ![s, h * s ^ 2] = s ^ 2 * (1 + h ^ 2 * s ^ 2) := by
  constructor
  · ext i; fin_cases i
    · simp
    · simp [pow_two]
  · simp [dotProduct, Fin.sum_univ_two]; ring

/-! ## 4. The minimal certified shift -/

section Shift

variable {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m]

/-- [definition] The largest eigenvalue of the symmetric part. -/
def lamMax (W : Matrix m m ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (symPart_isHermitian W).eigenvalues

omit [Nonempty m] in
theorem eigvec_orth {S : Matrix m m ℝ} (hS : S.IsHermitian) :
    (hS.eigenvectorUnitary : Matrix m m ℝ) * (hS.eigenvectorUnitary : Matrix m m ℝ)ᵀ = 1 := by
  have := Unitary.coe_mul_star_self hS.eigenvectorUnitary
  rwa [Unitary.coe_star, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial] at this

omit [Nonempty m] in
theorem eigvec_orth' {S : Matrix m m ℝ} (hS : S.IsHermitian) :
    (hS.eigenvectorUnitary : Matrix m m ℝ)ᵀ * (hS.eigenvectorUnitary : Matrix m m ℝ) = 1 := by
  have := Unitary.coe_star_mul_self hS.eigenvectorUnitary
  rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at this

/-- [proved-derived; formal-checked] **Rayleigh bound**: `⟨v, W v⟩ ≤ λ_max(sym W) |v|²`. -/
theorem rayleigh_le (W : Matrix m m ℝ) (v : m → ℝ) : v ⬝ᵥ (W *ᵥ v) ≤ lamMax W * (v ⬝ᵥ v) := by
  set hS := symPart_isHermitian W
  set U := (hS.eigenvectorUnitary : Matrix m m ℝ)
  rw [← quad_symPart, spectral_real hS, quad_conj]
  have hnorm : (Uᵀ *ᵥ v) ⬝ᵥ (Uᵀ *ᵥ v) = v ⬝ᵥ v := by
    rw [dotProduct_mulVec, ← mulVec_transpose, Matrix.transpose_transpose, mulVec_mulVec,
      eigvec_orth hS, one_mulVec, dotProduct_comm]
  rw [← hnorm]
  simp only [dotProduct, mulVec_diagonal, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hle : hS.eigenvalues i ≤ lamMax W := Finset.le_sup' _ (Finset.mem_univ i)
  nlinarith [mul_self_nonneg ((Uᵀ *ᵥ v) i)]

/-- [proved-derived; formal-checked] **The minimal certified shift.** `W − τI` is passive
(`⟨v, (W − τI) v⟩ ≤ 0` for all `v`) exactly when `τ ≥ λ_max(sym W)`. -/
theorem shift_passive_iff (W : Matrix m m ℝ) (τ : ℝ) :
    (∀ v, v ⬝ᵥ ((W - τ • 1) *ᵥ v) ≤ 0) ↔ lamMax W ≤ τ := by
  have hq : ∀ v, v ⬝ᵥ ((W - τ • 1) *ᵥ v) = v ⬝ᵥ (W *ᵥ v) - τ * (v ⬝ᵥ v) := fun v => by
    rw [sub_mulVec, dotProduct_sub, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul]
  constructor
  · intro h
    set hS := symPart_isHermitian W
    obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty hS.eigenvalues
    set U := (hS.eigenvectorUnitary : Matrix m m ℝ)
    set v := U *ᵥ Pi.single i 1
    have hUv : Uᵀ *ᵥ v = Pi.single i 1 := by
      rw [mulVec_mulVec, eigvec_orth' hS, one_mulVec]
    have hvv : v ⬝ᵥ v = 1 := by
      rw [dotProduct_mulVec, ← mulVec_transpose, hUv]; simp
    have hWv : v ⬝ᵥ (W *ᵥ v) = hS.eigenvalues i := by
      rw [← quad_symPart]
      conv_lhs => rw [spectral_real hS]
      rw [quad_conj, hUv]
      simp
    have := h v
    rw [hq, hvv, hWv] at this
    show Finset.univ.sup' _ hS.eigenvalues ≤ τ
    rw [hi]; linarith
  · intro hτ v
    rw [hq]
    have := rayleigh_le W v
    have hvv : 0 ≤ v ⬝ᵥ v := by
      simp only [dotProduct]; exact Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)
    nlinarith

/-- [proved-derived; formal-checked] **The shifted block preserves passivity**, composing
`committed_energy_bound`: with each learned block shifted by `τ_k ≥ λ_max(sym W_k)`, the committed
energy obeys `E_N ≤ ∏ (1 + ε_k) E_0`. -/
theorem shifted_committed_energy_bound (x : ℕ → m → ℝ) (Q J R W : ℕ → Matrix m m ℝ)
    (τ ε : ℕ → ℝ) (h : ℝ) (hh : 0 ≤ h) (hQ : ∀ k, (Q k)ᵀ = Q k) (hJ : ∀ k, (J k)ᵀ = -J k)
    (hR : ∀ k e, 0 ≤ e ⬝ᵥ (R k *ᵥ e)) (hτ : ∀ k, lamMax (W k) ≤ τ k)
    (hstep : ∀ k, x (k + 1) - x k =
      h • ((J k - R k + (W k - τ k • 1)) *ᵥ (Q k *ᵥ ((1 / 2 : ℝ) • (x k + x (k + 1))))))
    (hdep : ∀ k y, storageEnergy (Q (k + 1)) y ≤ (1 + ε k) * storageEnergy (Q k) y)
    (hε : ∀ k, 0 ≤ 1 + ε k) (N : ℕ) :
    storageEnergy (Q N) (x N) ≤
      (∏ k ∈ Finset.range N, (1 + ε k)) * storageEnergy (Q 0) (x 0) :=
  committed_energy_bound x Q J R (fun k => W k - τ k • 1) ε h hh hQ hJ hR
    (fun k => (shift_passive_iff (W k) (τ k)).mpr (hτ k)) hstep hdep hε N

end Shift

/-! ## 5. Chart containment for device steps -/

section Containment

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
/-- [proved-derived; formal-checked] **Re-centring keeps containment.** If the exact state lies in
`B(c, r)` and the device returns `(c', r')` with `‖c − c'‖ ≤ r' − r`, it lies in `B(c', r')`. -/
theorem recentre_contains {x c c' : E} {r r' : ℝ} (hx : ‖x - c‖ ≤ r) (hc : ‖c - c'‖ ≤ r' - r) :
    ‖x - c'‖ ≤ r' := by
  calc ‖x - c'‖ = ‖(x - c) + (c - c')‖ := by congr 1; abel
    _ ≤ ‖x - c‖ + ‖c - c'‖ := norm_add_le _ _
    _ ≤ r' := by linarith

/-- [proved-derived; formal-checked] **Containment propagates along device steps.** Exact states
`x_(k+1) = L_k x_k` with `‖L_k‖ ≤ K_k`; the device returns balls `(c_(k+1), r_(k+1))` with
`‖L_k c_k − c_(k+1)‖ ≤ r_(k+1) − K_k r_k`. Then `x_k ∈ B(c_k, r_k)` for every `k`, composing
`ball_image` and `recentre_contains`. -/
theorem device_containment (L : ℕ → E →L[ℝ] E) (K r : ℕ → ℝ) (x c : ℕ → E)
    (hL : ∀ k, ‖L k‖ ≤ K k) (hx : ∀ k, x (k + 1) = L k (x k))
    (hdev : ∀ k, ‖L k (c k) - c (k + 1)‖ ≤ r (k + 1) - K k * r k)
    (h0 : ‖x 0 - c 0‖ ≤ r 0) : ∀ k, ‖x k - c k‖ ≤ r k := by
  intro k
  induction k with
  | zero => exact h0
  | succ k ih =>
      rw [hx]
      exact recentre_contains (ball_image (L k) (hL k) ih) (hdev k)

end Containment

end Soma.Holonics.HolonCore
