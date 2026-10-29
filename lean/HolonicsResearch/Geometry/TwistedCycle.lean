import Holonics.Physics.Fluid.ComplexFluid
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# The twisted cycle: its eigenvectors, its least eigenvalue, the contact every section breaks, and the Fejér factor

The record `research/records/2026-10-26_INFORMATION_DIFFUSES_IN_THE_POTENTIAL_TRAVELS_IN_THE_TURN_AND_A_KEY_IS_READ_FROM_DIFFUSION_ONLY_TO_ITS_SQUARE_ROOT.md`
(§0 statement 7; atlas `key.twisted-cycle-square-root`) reads the extreme case of the connection
Cheeger bound on the `n`-cycle carrying a `ℤ_k` turn `c ≢ 0` on one contact. #410 owes its
eigenvectors, its least eigenvalue and its limit, the contact every section breaks, the Fejér
identity, and a labelling's Rayleigh quotient. This file proves those laws on the universal cover of
the cycle, where a section of the twisted cycle is a function on `ℤ` that returns multiplied by the
holonomy after one lap. The turn is written `θ = 2πc/k`, read at its nearest representative
`|θ| ≤ π` (`2|c| ≤ k`), and then `e^(iθ/n) = ζ_N^c`.

[proved-standard; formal-checked] What is proved.

1. **The powers are the eigenvectors** (`power_twisted`, `power_eigen`): for `z ≠ 0`, `u(x) = z^x`
   returns multiplied by `w = z^n` after a lap, and the connection Laplacian
   `(Lu)(x) = 2u(x) − u(x + 1) − u(x − 1)` reads `Lu = (1 − z)(1 − z⁻¹) u`. With `z = ζ_N^a`,
   `N = nk`, `a ≡ −c (mod k)`, the lap returns the turn and `u_a` is a section of the twisted cycle.
2. **On the unit circle the eigenvalue is `|1 − z|²`** (`eigenvalue_of_unit`).
3. **Every section of a frustrated cycle breaks a contact** (`defects_sum`,
   `frustrated_section_breaks`, `const_section_breaks_iff`): the defects
   `σ(x + 1) − σ(x) − c(x)` of a section sum to `−Σ c` round the cycle, so when `Σ c ≠ 0` some
   contact breaks; the constant section breaks exactly the turned contacts, so one turned contact
   gives `h₁ = 1/n` of the contacts.
4. **The Fejér identity** (`fejer_identity`): `|1 − z^n|² = |1 − z|² |Σ_(j<n) z^j|²`.
5. **`λ₁ = |1 − e^(iθ/n)|²` is the least eigenvalue** (`least_energy`, `power_energy`,
   `form_eq_energy`, `least_eigenvalue`): for `|θ| ≤ π` every section has
   `λ₁ · mass ≤ energy` over a lap, the power section `z^x` attains it, the Laplacian's form on a
   section is its energy, so every eigenvalue on a nonzero section is real and at least `λ₁`. The
   proof gauges the section to `ℤ/n`, where the twisted difference is the multiplier `z χ(k) − 1`
   on the modes (`dft_twist`), reads the energy mode by mode with the Hermitian Plancherel identity
   of `Physics/Fluid/ComplexFluid`, and places every turned mode no nearer the identity than `z`
   (`cos_shift_le`).
6. **`n² λ₁ → θ²`** (`least_rate`, `tendsto_least`): `|n² λ₁ − θ²| ≤ 5θ⁴/(48 n²)` once
   `|θ| ≤ n`, so a violated fraction `1/n` shows in the spectrum as `θ²/n²`.
7. **The labelling's Rayleigh quotient** (`labelling`, `labelling_section`, `labelling_lap`,
   `lap_section_energy`, `lap_section_rayleigh`): a section that is `1` on the lap breaks only the
   turned contact, energy `|1 − w|²` over mass `n`, so its quotient is
   `λ₁ |Σ_(j<n) z^j|²/n`.
8. **The Fejér factor grows like `n`** (`tendsto_fejer`): for `0 < |θ| ≤ π`,
   `|Σ_(j<n) z^j|²/n² → |1 − e^(iθ)|²/θ²`; at `k = 4`, `c = 1` the limit is `8/π²`, and the record's
   factors `1.71, 3.28, 6.51, 12.98` at `n = 2, 4, 8, 16` are `n` times `0.854, 0.821, 0.813,
   0.811`.
9. **The record's turn** (`root_eq_zeta`, `turn_le_pi_iff`): `e^(i(2πc/k)/n) = ζ_N^c` with
   `N = nk`, and `|2πc/k| ≤ π` exactly when `2|c| ≤ k`.

Not proved here: the general connection Cheeger bound `½λ₁ ≤ h₁ ≤ C√λ₁` of which the cycle is the
extreme case; the record's receipt counts (`nk` optimal sections) stay measured.

The computational object is the helical pair interaction: the turn is carried by one pair contact,
and a section is a reading of the strand that must slip at some contact. Of the winding guide's six
general objects this touches the cell holonomy (the lap's turn) and the helix (the cover); the pair,
faces and placement, the tube and the tower thread stay attached.

Consumers: the atlas row `key.twisted-cycle-square-root`.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Geometry.TwistedCycle

open Finset

/-! ## 1. The powers are the eigenvectors of the twisted cycle -/

section Eigen

variable {𝕜 : Type*} [Field 𝕜]

/-- [definition] The connection Laplacian on the cover of the cycle,
`(Lu)(x) = 2u(x) − u(x + 1) − u(x − 1)`. -/
def laplacian (u : ℤ → 𝕜) (x : ℤ) : 𝕜 := 2 * u x - u (x + 1) - u (x - 1)

/-- [proved-standard; formal-checked] **A power returns multiplied by its lap:**
`z^(x + n) = z^n z^x`, so `u(x) = z^x` is a section of the cycle twisted by `w = z^n`. -/
theorem power_twisted (z : 𝕜) (hz : z ≠ 0) (n : ℕ) (x : ℤ) :
    z ^ (x + (n : ℤ)) = z ^ n * z ^ x := by
  rw [zpow_add₀ hz, zpow_natCast, mul_comm]

/-- [proved-standard; formal-checked] **The powers are eigenvectors:**
`L(z^x) = (1 − z)(1 − z⁻¹) z^x`. -/
theorem power_eigen (z : 𝕜) (hz : z ≠ 0) (x : ℤ) :
    laplacian (fun y : ℤ => z ^ y) x = (1 - z) * (1 - z⁻¹) * z ^ x := by
  simp only [laplacian]
  rw [zpow_add₀ hz, zpow_sub₀ hz, zpow_one]
  have h1 : z * z⁻¹ = 1 := mul_inv_cancel₀ hz
  linear_combination (-(z ^ x)) * h1

end Eigen

/-- [proved-standard; formal-checked] **On the unit circle the eigenvalue is `|1 − z|²`.** -/
theorem eigenvalue_of_unit {z : ℂ} (hz : ‖z‖ = 1) :
    (1 - z) * (1 - z⁻¹) = ((‖1 - z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.inv_eq_conj hz, ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, map_sub, map_one]

/-! ## 2. Every section of a frustrated cycle breaks a contact -/

section Sections

variable {G : Type*} [AddCommGroup G] {n : ℕ} [NeZero n]

/-- [definition] The defect of a section `σ` on the contact `x → x + 1` carrying the turn `c x`. -/
def defect (c σ : ZMod n → G) (x : ZMod n) : G := σ (x + 1) - σ x - c x

/-- [proved-standard; formal-checked] **The defects sum to the turn round the cycle:**
`Σ_x (σ(x + 1) − σ(x) − c(x)) = −Σ_x c(x)`. -/
theorem defects_sum (c σ : ZMod n → G) : ∑ x, defect c σ x = -∑ x, c x := by
  have h : ∑ x, σ (x + 1) = ∑ x, σ x :=
    Fintype.sum_equiv (Equiv.addRight (1 : ZMod n)) (fun x => σ (x + 1)) σ fun x => by simp
  simp only [defect, Finset.sum_sub_distrib]
  rw [h]
  abel

/-- [proved-standard; formal-checked] **Every section of a frustrated cycle breaks a contact:** if
the turns do not sum to zero round the cycle, no section closes every contact. -/
theorem frustrated_section_breaks (c σ : ZMod n → G) (hc : ∑ x, c x ≠ 0) :
    ∃ x, σ (x + 1) ≠ σ x + c x := by
  by_contra h
  push Not at h
  apply hc
  have hd : ∀ x, defect c σ x = 0 := fun x => by
    simp only [defect, h x]
    abel
  have hs := defects_sum c σ
  simp only [hd, Finset.sum_const_zero] at hs
  exact neg_eq_zero.mp hs.symm

omit [NeZero n] in
/-- [proved-standard; formal-checked] **The constant section breaks exactly the turned contacts**,
so a cycle with one turned contact has a section breaking one contact of `n`. -/
theorem const_section_breaks_iff (c : ZMod n → G) (g : G) (x : ZMod n) :
    g ≠ g + c x ↔ c x ≠ 0 := by
  simp

end Sections

/-! ## 3. The Fejér identity -/

/-- [proved-standard; formal-checked] **The Fejér identity:**
`|1 − z^n|² = |1 − z|² |Σ_(j<n) z^j|²`. -/
theorem fejer_identity {𝕜 : Type*} [NormedDivisionRing 𝕜] (z : 𝕜) (n : ℕ) :
    ‖1 - z ^ n‖ ^ 2 = ‖1 - z‖ ^ 2 * ‖∑ j ∈ range n, z ^ j‖ ^ 2 := by
  rw [← mul_neg_geom_sum, norm_mul, mul_pow]

open Complex ZMod Filter Topology

/-! ## 4. `λ₁` is the least eigenvalue

A section `u(x + n) = e^(iθ) u(x)` is gauged by `z^x`, `z = e^(iθ/n)`, to a function `V` on `ℤ/n`;
the twisted difference becomes the multiplier `z χ(k) − 1` on the modes of `V`, and the Hermitian
Plancherel identity (`Physics/Fluid/ComplexFluid.hermitian_plancherel`) reads the energy mode by
mode. For `|θ| ≤ π` no turned mode lies nearer the identity than `z`. -/

section Least

variable {n : ℕ} [NeZero n]

/-- [definition] The energy of a function on the cover over one lap. -/
noncomputable def energy (n : ℕ) (u : ℤ → ℂ) : ℝ := ∑ x ∈ range n, ‖u ((x : ℤ) + 1) - u x‖ ^ 2

/-- [definition] The mass of a function on the cover over one lap. -/
noncomputable def mass (n : ℕ) (u : ℤ → ℂ) : ℝ := ∑ x ∈ range n, ‖u x‖ ^ 2

/-- [proved-standard; formal-checked] **A twisted difference is a multiplier on the modes:**
`𝓕(z V(· + 1) − V)(k) = (z χ(k) − 1) 𝓕V(k)`. -/
theorem dft_twist (z : ℂ) (V : ZMod n → ℂ) (k : ZMod n) :
    𝓕 (fun j => z * V (j + 1) - V j) k = (z * stdAddChar k - 1) * 𝓕 V k := by
  have hshift : ∑ j : ZMod n, stdAddChar (-(j * k)) * V (j + 1) =
      stdAddChar k * ∑ j : ZMod n, stdAddChar (-(j * k)) * V j := by
    rw [Finset.mul_sum]
    have := Equiv.sum_comp (Equiv.addRight (1 : ZMod n))
      (fun i => stdAddChar (-((i - 1) * k)) * V i)
    simp only [Equiv.coe_addRight, add_sub_cancel_right] at this
    rw [this]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← mul_assoc, ← AddChar.map_add_eq_mul]
    congr 2
    ring
  simp only [dft_apply, smul_eq_mul, mul_sub, Finset.sum_sub_distrib]
  rw [show (∑ j : ZMod n, stdAddChar (-(j * k)) * (z * V (j + 1))) =
      z * ∑ j : ZMod n, stdAddChar (-(j * k)) * V (j + 1) by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_; ring, hshift]
  ring

/-- [proved-standard; formal-checked] `‖e^(iα) − 1‖² = 2 − 2 cos α`. -/
theorem norm_turn_sub_one_sq (α : ℝ) : ‖exp (↑α * I) - 1‖ ^ 2 = 2 - 2 * Real.cos α := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [sub_re, sub_im, exp_ofReal_mul_I_re, exp_ofReal_mul_I_im, one_re, one_im, sub_zero]
  nlinarith [Real.sin_sq_add_cos_sq α]

/-- [proved-standard; formal-checked] **The turned modes lie no nearer the identity:** for
`|θ| ≤ π` and `m < n`, `cos((θ + 2πm)/n) ≤ cos(θ/n)`. -/
theorem cos_shift_le (θ : ℝ) (hθ : |θ| ≤ Real.pi) (m : ℕ) (hm : m < n) :
    Real.cos ((θ + 2 * Real.pi * m) / n) ≤ Real.cos (θ / n) := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  set p := 2 * Real.pi / n with hp
  set g := θ / n with hg
  have hpi := Real.pi_pos
  have hp0 : 0 < p := by positivity
  have hnp : (n : ℝ) * p = 2 * Real.pi := by rw [hp]; field_simp
  have hgp : |g| ≤ p / 2 := by
    rw [hg, abs_div, abs_of_pos hn, hp, div_le_iff₀ hn]
    field_simp
    linarith
  have hα : (θ + 2 * Real.pi * m) / n = g + m * p := by
    rw [hg, hp]; field_simp
  rw [hα, ← Real.cos_abs g]
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · simp [h0, Real.cos_abs]
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hpos
  have hmn : (m : ℝ) + 1 ≤ n := by exact_mod_cast hm
  have hmp1 : p ≤ m * p := by nlinarith
  have hmp2 : m * p ≤ 2 * Real.pi - p := by nlinarith
  have hga := abs_nonneg g
  obtain ⟨hg1, hg2⟩ := abs_le.mp hgp
  have hlo : |g| ≤ g + m * p := by
    rcases le_total 0 g with h | h
    · rw [abs_of_nonneg h]; nlinarith
    · rw [abs_of_nonpos h]; linarith
  have hhi : g + m * p ≤ 2 * Real.pi - |g| := by
    rcases le_total 0 g with h | h
    · rw [abs_of_nonneg h]; linarith
    · rw [abs_of_nonpos h]; linarith
  rcases le_total (g + m * p) Real.pi with h | h
  · exact Real.cos_le_cos_of_nonneg_of_le_pi hga h hlo
  · rw [← Real.cos_two_pi_sub (g + m * p)]
    exact Real.cos_le_cos_of_nonneg_of_le_pi hga (by linarith) (by linarith)

/-- [proved-standard; formal-checked] The sum over one lap of the cover is the sum over `ℤ/n`. -/
theorem sum_range_cast (F : ZMod n → ℝ) : ∑ x ∈ range n, F (x : ZMod n) = ∑ j, F j := by
  refine Finset.sum_nbij' (fun x => (x : ZMod n)) (fun j => j.val) ?_ ?_ ?_ ?_ ?_
  · intro x _; exact Finset.mem_univ _
  · intro j _; exact Finset.mem_range.mpr (ZMod.val_lt j)
  · intro x hx; exact ZMod.val_cast_of_lt (Finset.mem_range.mp hx)
  · intro j _; exact ZMod.natCast_zmod_val j
  · intro x _; rfl

/-- [proved-standard; formal-checked] **`λ₁ = ‖1 − e^(iθ/n)‖²` is the least energy of a section:**
for `|θ| ≤ π`, every section `u(x + n) = e^(iθ) u(x)` of the twisted `n`-cycle has
`‖1 − e^(iθ/n)‖² · mass ≤ energy`. -/
theorem least_energy (θ : ℝ) (hθ : |θ| ≤ Real.pi) (u : ℤ → ℂ)
    (hu : ∀ x : ℤ, u (x + n) = exp (↑θ * I) * u x) :
    ‖1 - exp (↑(θ / n) * I)‖ ^ 2 * mass n u ≤ energy n u := by
  set z := exp (↑(θ / n) * I) with hz
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hnr : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  have hz0 : z ≠ 0 := Complex.exp_ne_zero _
  have hz1 : ‖z‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hzn : z ^ n = exp (↑θ * I) := by
    rw [hz, ← Complex.exp_nat_mul]; congr 1; push_cast; field_simp
  -- the gauge to a periodic function
  set v : ℤ → ℂ := fun x => z ^ (-x) * u x with hv
  have hper : Function.Periodic v (n : ℤ) := by
    intro x
    simp only [hv, hu, ← hzn]
    rw [neg_add, zpow_add₀ hz0, zpow_neg z (n : ℤ), zpow_natCast]
    field_simp
  set V : ZMod n → ℂ := fun j => v (j.val : ℤ) with hV
  have hvV : ∀ x : ℤ, v x = V (x : ZMod n) := by
    intro x
    simp only [hV, ZMod.val_intCast, Int.emod_def]
    have h := hper.sub_int_mul_eq (x := x) (x / (n : ℤ))
    simp only [Int.cast_id] at h
    rw [mul_comm, h]
  have huV : ∀ x : ℤ, u x = z ^ x * V (x : ZMod n) := by
    intro x
    rw [← hvV, hv]; simp only
    rw [← mul_assoc, ← zpow_add₀ hz0, add_neg_cancel, zpow_zero, one_mul]
  set D : ZMod n → ℂ := fun j => z * V (j + 1) - V j with hD
  have hE : energy n u = ∑ j, ‖D j‖ ^ 2 := by
    rw [energy, ← sum_range_cast (fun j => ‖D j‖ ^ 2)]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [huV, huV, zpow_add₀ hz0, zpow_one]
    simp only [hD]
    push_cast
    rw [show z ^ (x : ℤ) * z * V ((x : ZMod n) + 1) - z ^ (x : ℤ) * V (x : ZMod n) =
      z ^ (x : ℤ) * (z * V ((x : ZMod n) + 1) - V (x : ZMod n)) by ring, norm_mul, norm_zpow,
      hz1, one_zpow, one_mul]
  have hM : mass n u = ∑ j, ‖V j‖ ^ 2 := by
    rw [mass, ← sum_range_cast (fun j => ‖V j‖ ^ 2)]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [huV, norm_mul, norm_zpow, hz1, one_zpow, one_mul]
    push_cast; rfl
  have hmode : ∀ k : ZMod n, ‖1 - z‖ ^ 2 ≤ ‖z * stdAddChar k - 1‖ ^ 2 := by
    intro k
    have hχ : z * stdAddChar k = exp (↑((θ + 2 * Real.pi * k.val) / n) * I) := by
      rw [stdAddChar_apply, toCircle_apply, hz, ← Complex.exp_add]
      congr 1; push_cast; ring
    rw [hχ, norm_sub_rev, hz, norm_turn_sub_one_sq, norm_turn_sub_one_sq]
    have := cos_shift_le (n := n) θ hθ k.val (ZMod.val_lt k)
    linarith
  have hmain : (n : ℝ) * (‖1 - z‖ ^ 2 * mass n u) ≤ n * energy n u := by
    have hP : ∀ W : ZMod n → ℂ, ∑ k, ‖𝓕 W k‖ ^ 2 = n * ∑ j, ‖W j‖ ^ 2 := fun W => by
      simpa only [Complex.normSq_eq_norm_sq] using
        Holonics.Physics.Fluid.ComplexFluid.hermitian_plancherel W
    rw [hE, hM, mul_left_comm, ← hP, ← hP, Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [show 𝓕 D k = (z * stdAddChar k - 1) * 𝓕 V k from dft_twist z V k, norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right (hmode k) (by positivity)
  exact le_of_mul_le_mul_left hmain hnr

omit [NeZero n] in
/-- [proved-standard; formal-checked] **The least energy is attained by the power section:** with
`z = e^(iθ/n)`, `u(x) = z^x` is a section and its energy is `‖1 − z‖²` times its mass `n`. -/
theorem power_energy (θ : ℝ) :
    energy n (fun x : ℤ => exp (↑(θ / n) * I) ^ x) =
      ‖1 - exp (↑(θ / n) * I)‖ ^ 2 * mass n (fun x : ℤ => exp (↑(θ / n) * I) ^ x) := by
  set z := exp (↑(θ / n) * I) with hz
  have hz0 : z ≠ 0 := Complex.exp_ne_zero _
  have hz1 : ‖z‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  simp only [energy, mass, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [zpow_add₀ hz0, zpow_one, show z ^ (x : ℤ) * z - z ^ (x : ℤ) = z ^ (x : ℤ) * (z - 1) by ring,
    norm_mul, norm_zpow, hz1, one_zpow, one_mul, one_pow, mul_one, norm_sub_rev]

omit [NeZero n] in
/-- [proved-standard; formal-checked] The telescoping of one lap: if `f n = f 0` then `Σ_(x<n) f(x + 1) = Σ_(x<n) f(x)`. -/
theorem lap_shift (f : ℤ → ℂ) (h : f n = f 0) :
    ∑ x ∈ range n, f ((x : ℤ) + 1) = ∑ x ∈ range n, f x := by
  have h1 := Finset.sum_range_succ (fun x : ℕ => f x) n
  have h2 := Finset.sum_range_succ' (fun x : ℕ => f x) n
  push_cast at h1 h2
  rw [h] at h1
  linear_combination h1.symm.trans h2 |>.symm

omit [NeZero n] in
/-- [proved-standard; formal-checked] **The Laplacian's form is the energy:** on a section of a
cycle twisted by a unit `w`, `Σ_(x<n) conj(u x) (Lu)(x) = Σ_(x<n) ‖u(x + 1) − u(x)‖²`. -/
theorem form_eq_energy (w : ℂ) (hw : ‖w‖ = 1) (u : ℤ → ℂ) (hu : ∀ x : ℤ, u (x + n) = w * u x) :
    ∑ x ∈ range n, (starRingEnd ℂ) (u x) * laplacian u x = (energy n u : ℂ) := by
  have hww : (starRingEnd ℂ) w * w = 1 := by
    rw [Complex.conj_mul', hw]; norm_num
  have hB : ∑ x ∈ range n, u ((x : ℤ) + 1) * (starRingEnd ℂ) (u ((x : ℤ) + 1)) =
      ∑ x ∈ range n, u x * (starRingEnd ℂ) (u x) := by
    refine lap_shift (fun x => u x * (starRingEnd ℂ) (u x)) ?_
    have := hu 0
    simp only [zero_add] at this
    simp only [this, map_mul]
    linear_combination (u 0 * (starRingEnd ℂ) (u 0)) * hww
  have hD : ∑ x ∈ range n, (starRingEnd ℂ) (u x) * u (x - 1) =
      ∑ x ∈ range n, u x * (starRingEnd ℂ) (u ((x : ℤ) + 1)) := by
    rw [← lap_shift (fun x => (starRingEnd ℂ) (u x) * u (x - 1))]
    · refine Finset.sum_congr rfl fun x _ => ?_
      simp only [add_sub_cancel_right]; ring
    · have h0 := hu 0
      have h1 := hu (-1)
      simp only [zero_add] at h0
      simp only [h0, map_mul, show (-1 : ℤ) + n = (n : ℤ) - 1 by ring] at h1 ⊢
      rw [h1, zero_sub]
      linear_combination ((starRingEnd ℂ) (u 0) * u (-1)) * hww
  simp only [energy, laplacian]
  push_cast
  simp_rw [← Complex.mul_conj', map_sub]
  have e1 : ∀ x : ℕ, (starRingEnd ℂ) (u x) * (2 * u x - u ((x : ℤ) + 1) - u (x - 1)) =
      2 * (u x * (starRingEnd ℂ) (u x)) - (starRingEnd ℂ) (u x) * u ((x : ℤ) + 1) -
        (starRingEnd ℂ) (u x) * u (x - 1) := fun x => by ring
  have e2 : ∀ x : ℕ, (u ((x : ℤ) + 1) - u x) * ((starRingEnd ℂ) (u ((x : ℤ) + 1)) -
      (starRingEnd ℂ) (u x)) = u ((x : ℤ) + 1) * (starRingEnd ℂ) (u ((x : ℤ) + 1)) -
        (starRingEnd ℂ) (u x) * u ((x : ℤ) + 1) - u x * (starRingEnd ℂ) (u ((x : ℤ) + 1)) +
          u x * (starRingEnd ℂ) (u x) := fun x => by ring
  simp_rw [e1, e2, Finset.sum_add_distrib, Finset.sum_sub_distrib, hB, hD, ← Finset.mul_sum]
  ring

/-- [proved-standard; formal-checked] **`λ₁` is the least eigenvalue:** every eigenvalue of the
Laplacian on a nonzero section of the cycle twisted by `e^(iθ)`, `|θ| ≤ π`, is real and at least
`‖1 − e^(iθ/n)‖²`; the power section attains it. -/
theorem least_eigenvalue (θ : ℝ) (hθ : |θ| ≤ Real.pi) (u : ℤ → ℂ)
    (hu : ∀ x : ℤ, u (x + n) = exp (↑θ * I) * u x) (hne : mass n u ≠ 0) (μ : ℂ)
    (heig : ∀ x, laplacian u x = μ * u x) :
    μ.im = 0 ∧ ‖1 - exp (↑(θ / n) * I)‖ ^ 2 ≤ μ.re := by
  have hform := form_eq_energy (exp (↑θ * I)) (Complex.norm_exp_ofReal_mul_I θ) u hu
  simp_rw [heig] at hform
  have hmu : μ * (mass n u : ℂ) = (energy n u : ℂ) := by
    rw [← hform, mass]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Complex.conj_mul']; ring
  have hm0 : (mass n u : ℂ) ≠ 0 := by exact_mod_cast hne
  have hmu' : μ = ((energy n u / mass n u : ℝ) : ℂ) := by
    push_cast; field_simp; exact hmu
  have hpos : 0 < mass n u :=
    lt_of_le_of_ne (Finset.sum_nonneg fun x _ => by positivity) (Ne.symm hne)
  refine ⟨by rw [hmu', Complex.ofReal_im], ?_⟩
  rw [hmu', Complex.ofReal_re, le_div_iff₀ hpos]
  exact least_energy θ hθ u hu

/-! ## 5. `n² λ₁ → θ²`: diffusion needs `~n²` passes to feel the turn -/

/-- [proved-standard; formal-checked] **The rate:** for `|θ| ≤ n`,
`|n² ‖1 − e^(iθ/n)‖² − θ²| ≤ 5θ⁴/(48 n²)`. -/
theorem least_rate (θ : ℝ) (hθn : |θ| ≤ n) :
    |(n : ℝ) ^ 2 * ‖1 - exp (↑(θ / n) * I)‖ ^ 2 - θ ^ 2| ≤ 5 * θ ^ 4 / (48 * (n : ℝ) ^ 2) := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne n))
  have hx : |θ / n| ≤ 1 := by rw [abs_div, abs_of_pos hn, div_le_one hn]; exact hθn
  have hb := Real.cos_bound hx
  rw [norm_sub_rev, norm_turn_sub_one_sq]
  have key : (n : ℝ) ^ 2 * (2 - 2 * Real.cos (θ / n)) - θ ^ 2 =
      -(2 * (n : ℝ) ^ 2) * (Real.cos (θ / n) - (1 - (θ / n) ^ 2 / 2)) := by
    field_simp; ring
  rw [key, abs_mul, abs_neg, abs_of_pos (by positivity)]
  calc 2 * (n : ℝ) ^ 2 * |Real.cos (θ / n) - (1 - (θ / n) ^ 2 / 2)|
      ≤ 2 * (n : ℝ) ^ 2 * (|θ / n| ^ 4 * (5 / 96)) := by gcongr
    _ = 5 * θ ^ 4 / (48 * (n : ℝ) ^ 2) := by
      rw [abs_div, abs_of_pos hn, div_pow, pow_abs,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ θ ^ 4)]
      field_simp; ring

end Least

/-- [proved-standard; formal-checked] **`n² λ₁ → θ²`:** diffusion needs `~n²` passes to feel the
turn. -/
theorem tendsto_least (θ : ℝ) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ 2 * ‖1 - exp (↑(θ / n) * I)‖ ^ 2) atTop (𝓝 (θ ^ 2)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_
    (tendsto_const_div_atTop_nhds_zero_nat (5 * θ ^ 4 / 48))
  filter_upwards [eventually_ge_atTop (⌈|θ|⌉₊ + 1)] with n hn
  have : NeZero n := ⟨by omega⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hθn : |θ| ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast (show ⌈|θ|⌉₊ ≤ n by omega))
  rw [Real.norm_eq_abs]
  refine (least_rate θ hθn).trans ?_
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h2 : 5 * θ ^ 4 * (n : ℝ) ≤ 5 * θ ^ 4 * (n : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
  have h3 : 5 * θ ^ 4 / 48 * (48 * (n : ℝ) ^ 2) = 5 * θ ^ 4 * (n : ℝ) ^ 2 := by ring
  linarith

/-! ## 6. The labelling's Rayleigh quotient and the Fejér factor

The constant labelling breaks only the turned contact, so its Rayleigh quotient is `‖1 − w‖²/n`;
by the Fejér identity that is `λ₁` times the Fejér factor `‖Σ_(j<n) z^j‖²/n`, which grows like
`n`. -/

section Labelling

variable {n : ℕ} [NeZero n]

/-- [definition] The labelling of the twisted cycle: `1` on the lap `0 ≤ x < n`, multiplied by the
holonomy each lap, `u(x) = w^⌊x/n⌋`. -/
noncomputable def labelling (n : ℕ) (w : ℂ) (x : ℤ) : ℂ := w ^ (x / (n : ℤ))

/-- [proved-standard; formal-checked] The labelling is a section. -/
theorem labelling_section {w : ℂ} (hw : w ≠ 0) (x : ℤ) :
    labelling n w (x + n) = w * labelling n w x := by
  simp only [labelling]
  rw [Int.add_ediv_of_dvd_right (dvd_refl _),
    Int.ediv_self (by exact_mod_cast NeZero.ne n), zpow_add_one₀ hw, mul_comm]

omit [NeZero n] in
/-- [proved-standard; formal-checked] The labelling is `1` on the lap. -/
theorem labelling_lap (w : ℂ) (x : ℕ) (hx : x < n) : labelling n w x = 1 := by
  simp only [labelling]
  rw [Int.ediv_eq_zero_of_lt (by positivity) (by exact_mod_cast hx), zpow_zero]

/-- [proved-standard; formal-checked] **A section that is `1` on the lap breaks only the turned
contact:** its energy is `‖1 − w‖²` and its mass is `n`. -/
theorem lap_section_energy (w : ℂ) (u : ℤ → ℂ) (hu : ∀ x : ℤ, u (x + n) = w * u x)
    (hl : ∀ x : ℕ, x < n → u x = 1) : energy n u = ‖1 - w‖ ^ 2 ∧ mass n u = n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := NeZero.ne n; omega⟩
  constructor
  · rw [energy, Finset.sum_range_succ, Finset.sum_eq_zero, zero_add]
    · have h0 := hu 0
      simp only [zero_add] at h0
      push_cast at h0
      have h00 := hl 0 (by omega)
      simp only [Nat.cast_zero] at h00
      rw [h0, h00, hl m (by omega), mul_one, norm_sub_rev]
    · intro x hx
      have hx' := Finset.mem_range.mp hx
      rw [show ((x : ℤ) + 1) = ((x + 1 : ℕ) : ℤ) by push_cast; ring, hl (x + 1) (by omega),
        hl x (by omega), sub_self, norm_zero]
      norm_num
  · rw [mass, Finset.sum_congr rfl fun x hx => by rw [hl x (Finset.mem_range.mp hx)]]
    simp

/-- [proved-standard; formal-checked] `e^(iθ/n)` is an `n`-th root of the holonomy `e^(iθ)`. -/
theorem root_pow (θ : ℝ) : exp (↑(θ / n) * I) ^ n = exp (↑θ * I) := by
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  rw [← Complex.exp_nat_mul]; congr 1; push_cast; field_simp

/-- [proved-standard; formal-checked] **The labelling's Rayleigh quotient** is the diffusion's
least energy times the Fejér factor: `energy/mass = λ₁ ‖Σ_(j<n) z^j‖²/n`, `z = e^(iθ/n)`. -/
theorem lap_section_rayleigh (θ : ℝ) (u : ℤ → ℂ) (hu : ∀ x : ℤ, u (x + n) = exp (↑θ * I) * u x)
    (hl : ∀ x : ℕ, x < n → u x = 1) :
    energy n u / mass n u =
      ‖1 - exp (↑(θ / n) * I)‖ ^ 2 * (‖∑ j ∈ range n, exp (↑(θ / n) * I) ^ j‖ ^ 2 / n) := by
  obtain ⟨hE, hM⟩ := lap_section_energy _ u hu hl
  rw [hE, hM, ← root_pow (n := n) θ, fejer_identity, mul_div_assoc]

/-- [proved-standard; formal-checked] **The Fejér factor grows like `n`:** for `0 < |θ| ≤ π`,
`‖Σ_(j<n) e^(ijθ/n)‖²/n² → ‖1 − e^(iθ)‖²/θ²`. -/
theorem tendsto_fejer (θ : ℝ) (h0 : θ ≠ 0) (hθ : |θ| ≤ Real.pi) :
    Tendsto (fun n : ℕ => ‖∑ j ∈ range n, exp (↑(θ / n) * I) ^ j‖ ^ 2 / (n : ℝ) ^ 2) atTop
      (𝓝 (‖1 - exp (↑θ * I)‖ ^ 2 / θ ^ 2)) := by
  have h := (tendsto_const_nhds (x := ‖1 - exp (↑θ * I)‖ ^ 2)).div (tendsto_least θ)
    (pow_ne_zero 2 h0)
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have : NeZero n := ⟨by omega⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hl : ‖1 - exp (↑(θ / n) * I)‖ ^ 2 ≠ 0 := by
    rw [norm_sub_rev, norm_turn_sub_one_sq]
    intro hc
    have hcos : Real.cos (θ / n) = 1 := by linarith
    have hpi := Real.pi_pos
    have hlt : |θ / n| < 2 * Real.pi := by
      rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < n)]
      rw [div_lt_iff₀ (by linarith)]; nlinarith [abs_nonneg θ]
    obtain ⟨ha, hb⟩ := abs_lt.mp hlt
    rw [Real.cos_eq_one_iff_of_lt_of_lt (by linarith) hb] at hcos
    exact h0 (by simpa [div_eq_zero_iff, show (n : ℝ) ≠ 0 by linarith] using hcos)
  have hl' : ‖1 - exp (↑(θ / n) * I)‖ ≠ 0 := fun h => hl (by rw [h]; ring)
  simp only [Pi.div_apply]
  rw [← root_pow (n := n) θ, fejer_identity]
  field_simp

end Labelling

/-! ## 7. The record's turn `θ = 2πc/k` -/

/-- [proved-standard; formal-checked] **The record's turn:** with `θ = 2πc/k`,
`e^(iθ/n) = ζ_N^c` for `N = nk`, `ζ_N = e^(2πi/N)`. -/
theorem root_eq_zeta (c : ℤ) (k n : ℕ) (hk : k ≠ 0) (hn : n ≠ 0) :
    exp (↑(2 * Real.pi * c / k / n) * I) = exp (2 * Real.pi * I / (n * k : ℕ)) ^ c := by
  rw [← Complex.exp_int_mul]; congr 1; push_cast; field_simp

/-- [proved-standard; formal-checked] `|2πc/k| ≤ π` exactly when `2|c| ≤ k`: the turn is read at
its nearest representative. -/
theorem turn_le_pi_iff (c : ℤ) (k : ℕ) (hk : k ≠ 0) :
    |2 * Real.pi * c / k| ≤ Real.pi ↔ 2 * |c| ≤ (k : ℤ) := by
  have hk' : (0 : ℝ) < k := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)
  rw [show 2 * Real.pi * c / k = Real.pi * (2 * c / k) by ring, abs_mul,
    abs_of_pos Real.pi_pos, mul_le_iff_le_one_right Real.pi_pos, abs_div, abs_mul, abs_two,
    Nat.abs_cast, div_le_one hk']
  constructor
  · intro h; exact_mod_cast (show ((2 * |c| : ℤ) : ℝ) ≤ (k : ℤ) by push_cast; exact h)
  · intro h; have : ((2 * |c| : ℤ) : ℝ) ≤ ((k : ℤ) : ℝ) := by exact_mod_cast h
    push_cast at this; exact this


end Holonics.Geometry.TwistedCycle
