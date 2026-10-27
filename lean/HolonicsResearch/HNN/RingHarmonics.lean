import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic

/-!
# The ring's harmonics: `⌊n/2⌋` harmonics read every function of a residue, and their covector

The record `research/records/2026-10-24_THE_TOWER_HEARS_THE_HOLONICS_TEXT_AND_EVERY_LOOK_IS_READ_BY_ITS_LOCK.md`
("The readout at every harmonic of the key", atlas `hnn.tower-ring-face`) reads a ring keyed modulo
`n` at `H = ⌊n/2⌋` harmonics of its face `ρ`, `q_1 = ρ` and `q_h = q_(h−1) ρ / |ρ|`
(`hnn::tower::RingFace::with_harmonics`), and carries each harmonic's covector back to `ρ` on the
turn only (`hnn::tower::harmonics_adjoint`). #410 owes both statements; this file proves them in
exact arithmetic (the owner rounds each harmonic to the face's grain).

[proved-derived; formal-checked] What is proved.

1. **`⌊n/2⌋` harmonics read every function of a residue** (`harmonic_expansion_eq`,
   `harmonic_expansion`): every real function on `ℤ/n` is `a + Σ_(1≤h≤⌊n/2⌋) (b_h cos(2πhk/n) +
   c_h sin(2πhk/n))`. The proof inverts the discrete Fourier transform (`inversion`, through
   Mathlib's `ZMod.dft`) and folds each frequency `j > ⌊n/2⌋` onto `n − j`, where its cosine is the
   same and its sine reversed (`cos_fold`, `sin_fold`).
2. **On the ring** (`harmonic_residueFace`, `ring_read_at_harmonics`): on the face
   `r e^(2πik/n)` of residue `k` the harmonic `q_h` is `r e^(2πihk/n)`, so a readout affine in the
   harmonics' two parts reads every function of the residue.
3. **The harmonics** (`harmonic_one`, `harmonic_succ_succ`, `norm_harmonic`, `harmonic_turn`,
   `harmonic_scale`): `q_h = ρ^h / |ρ|^(h−1)` is the owner's recurrence, has the face's length, turns
   `h` times as fast as the face and scales with it.
4. **The covector on the turn** (`hasDerivAt_reading_turn`, `turn_covector_eq`,
   `hasDerivAt_reading_turn_adjoint`): along the turn `ρ e^(is)` the reading `Σ_h ⟪G_h, q_h⟫` moves at
   `Σ_h h (G_h,im q_h,re − G_h,re q_h,im)`, which is `⟪∂ρ, iρ⟫` for the owner's covector
   `∂ρ = G_1 + t (−ρ_im, ρ_re)/|ρ|²`, `t = Σ_(h≥2) h (G_h,im q_h,re − G_h,re q_h,im)`
   (`harmonicsAdjoint`, `harmonicsAdjoint_re`, `harmonicsAdjoint_im`).
5. **The radial part dropped is invisible** (`hasDerivAt_reading_radial_split`,
   `hasDerivAt_ratio_turn`, `hasDerivAt_ratio_radial`): along the radius the reading moves by
   `⟪∂ρ, ρ⟫` plus the harmonics' radial part `Σ_(h≥2) ⟪G_h, q_h⟫`, which `∂ρ` omits; but the face is a
   ratio to its own length, `ρ = r q/|q|`, so through it the radius does not move the reading at all,
   and the turn moves it by `⟪∂ρ, iρ⟫`. The omitted part costs nothing.

The computational object is the helical pair interaction's ring: a parametron ring keyed modulo
`n`, read through the characters of its turn. Of the winding guide's six general objects this
touches the helix (the turn taken `h` times) and faces and placement (the residue's face); the
pair, the cell holonomy, the tube and the tower thread stay attached.

Consumers: the atlas row `hnn.tower-ring-face` and #410.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.HNN.RingHarmonics

open Finset
open scoped Real

/-! ## 1. The fold of a frequency -/

/-- [definition] The fold of a frequency `j < n` onto `0, …, ⌊n/2⌋`: `j` itself up to `⌊n/2⌋`,
else `n − j`. -/
def fold (n j : ℕ) : ℕ := if j ≤ n / 2 then j else n - j

/-- [definition] The fold's hand: `+1` where the frequency is kept, `−1` where it is reflected. -/
def foldSign (n j : ℕ) : ℝ := if j ≤ n / 2 then 1 else -1

theorem fold_le (n j : ℕ) (hj : j < n) : fold n j ≤ n / 2 := by
  unfold fold
  split_ifs with h <;> omega

/-- [proved-derived; formal-checked] A reflected frequency has the same cosine. -/
theorem cos_fold (n j k : ℕ) (hj : j < n) :
    Real.cos (2 * π * j * k / n) = Real.cos (2 * π * fold n j * k / n) := by
  unfold fold
  split_ifs with h
  · rfl
  · have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    have e : 2 * π * ((n - j : ℕ) : ℝ) * k / n = k * (2 * π) - 2 * π * j * k / n := by
      rw [Nat.cast_sub hj.le, div_eq_iff hn, sub_mul, div_mul_cancel₀ _ hn]
      ring
    rw [e, Real.cos_nat_mul_two_pi_sub]

/-- [proved-derived; formal-checked] A reflected frequency has the reversed sine. -/
theorem sin_fold (n j k : ℕ) (hj : j < n) :
    Real.sin (2 * π * j * k / n) = foldSign n j * Real.sin (2 * π * fold n j * k / n) := by
  unfold fold foldSign
  split_ifs with h
  · rw [one_mul]
  · have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    have e : 2 * π * ((n - j : ℕ) : ℝ) * k / n = k * (2 * π) - 2 * π * j * k / n := by
      rw [Nat.cast_sub hj.le, div_eq_iff hn, sub_mul, div_mul_cancel₀ _ hn]
      ring
    rw [e, Real.sin_nat_mul_two_pi_sub]
    ring

theorem range_fold (n : ℕ) : range (n / 2 + 1) = insert 0 (Icc 1 (n / 2)) := by
  ext h
  simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
  omega

/-! ## 2. Every function of a residue is read at `⌊n/2⌋` harmonics -/

section Expansion

variable (n : ℕ) [NeZero n]

/-- [definition] The discrete Fourier spectrum of a real function on `ℤ/n`. -/
noncomputable def spectrum (f : ZMod n → ℝ) : ZMod n → ℂ := ZMod.dft (fun i => (f i : ℂ))

/-- [proved-derived; formal-checked] **The inversion**:
`f(k) = (1/n) Σ_j (F_j,re cos(2πjk/n) − F_j,im sin(2πjk/n))`. -/
theorem inversion (f : ZMod n → ℝ) (k : ZMod n) :
    f k = (n : ℝ)⁻¹ * ∑ j : ZMod n,
      ((spectrum n f j).re * Real.cos (2 * π * j.val * k.val / n) -
        (spectrum n f j).im * Real.sin (2 * π * j.val * k.val / n)) := by
  have h0 : ZMod.dft.symm (spectrum n f) = fun i => (f i : ℂ) :=
    LinearEquiv.symm_apply_apply _ _
  have h := ZMod.invDFT_apply (spectrum n f) k
  rw [h0] at h
  have h1 : (f k : ℂ) = (n : ℂ)⁻¹ * ∑ j : ZMod n, ZMod.stdAddChar (j * k) * spectrum n f j := by
    simpa only [smul_eq_mul] using h
  have hchar : ∀ j : ZMod n, ZMod.stdAddChar (j * k) =
      Complex.exp (((2 * π * j.val * k.val / n : ℝ) : ℂ) * Complex.I) := by
    intro j
    have e : j * k = ((j.val * k.val : ℕ) : ZMod n) := by
      rw [Nat.cast_mul, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    rw [e, ZMod.stdAddChar_apply, ZMod.toCircle_natCast]
    congr 1
    push_cast
    ring
  have h2 := congrArg Complex.re h1
  rw [Complex.ofReal_re] at h2
  rw [h2]
  have hn : ((n : ℂ))⁻¹ = (((n : ℝ)⁻¹ : ℝ) : ℂ) := by
    rw [Complex.ofReal_inv, Complex.ofReal_natCast]
  rw [hn, Complex.re_ofReal_mul, Complex.re_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hchar j, Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  ring

/-- [definition] The residues whose frequency folds onto `h`. -/
def fibre (h : ℕ) : Finset (ZMod n) := univ.filter fun j => fold n j.val = h

/-- [definition] The cosine coefficient of the folded harmonic `h`. -/
noncomputable def cosCoeff (f : ZMod n → ℝ) (h : ℕ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ j ∈ fibre n h, (spectrum n f j).re

/-- [definition] The sine coefficient of the folded harmonic `h`. -/
noncomputable def sinCoeff (f : ZMod n → ℝ) (h : ℕ) : ℝ :=
  -((n : ℝ)⁻¹ * ∑ j ∈ fibre n h, foldSign n j.val * (spectrum n f j).im)

/-- [definition] The term of frequency `j` at residue `k`, folded onto `0, …, ⌊n/2⌋`. -/
noncomputable def foldedTerm (f : ZMod n → ℝ) (k j : ZMod n) : ℝ :=
  (spectrum n f j).re * Real.cos (2 * π * fold n j.val * k.val / n) -
    foldSign n j.val * (spectrum n f j).im * Real.sin (2 * π * fold n j.val * k.val / n)

/-- [proved-derived; formal-checked] **`⌊n/2⌋` harmonics read every function of a residue**:
`f(k) = a + Σ_(1≤h≤⌊n/2⌋) (b_h cos(2πhk/n) + c_h sin(2πhk/n))`, with the coefficients of the folded
spectrum. -/
theorem harmonic_expansion_eq (f : ZMod n → ℝ) (k : ZMod n) :
    f k = cosCoeff n f 0 + ∑ h ∈ Icc 1 (n / 2),
      (cosCoeff n f h * Real.cos (2 * π * h * k.val / n) +
        sinCoeff n f h * Real.sin (2 * π * h * k.val / n)) := by
  have hterm : ∀ j : ZMod n,
      (spectrum n f j).re * Real.cos (2 * π * j.val * k.val / n) -
          (spectrum n f j).im * Real.sin (2 * π * j.val * k.val / n) = foldedTerm n f k j := by
    intro j
    rw [foldedTerm, cos_fold n j.val k.val (ZMod.val_lt j), sin_fold n j.val k.val (ZMod.val_lt j)]
    ring
  have hmaps : ∀ j ∈ (univ : Finset (ZMod n)),
      (fun j : ZMod n => fold n j.val) j ∈ range (n / 2 + 1) :=
    fun j _ => Finset.mem_range.2 (Nat.lt_succ_of_le (fold_le n j.val (ZMod.val_lt j)))
  have hfib : ∑ j : ZMod n, foldedTerm n f k j =
      ∑ h ∈ range (n / 2 + 1), ∑ j ∈ fibre n h, foldedTerm n f k j :=
    (Finset.sum_fiberwise_of_maps_to hmaps (foldedTerm n f k)).symm
  have hinner : ∀ h ∈ range (n / 2 + 1), ∑ j ∈ fibre n h, foldedTerm n f k j =
      (∑ j ∈ fibre n h, (spectrum n f j).re) * Real.cos (2 * π * h * k.val / n) -
        (∑ j ∈ fibre n h, foldSign n j.val * (spectrum n f j).im) *
          Real.sin (2 * π * h * k.val / n) := by
    intro h _
    rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : fold n j.val = h := (Finset.mem_filter.1 hj).2
    rw [foldedTerm, hj']
  have h0 : (0 : ℕ) ∉ Icc 1 (n / 2) := by simp
  rw [inversion n f k, Finset.sum_congr rfl fun j _ => hterm j, hfib,
    Finset.sum_congr rfl hinner, range_fold n, Finset.sum_insert h0, mul_add, Finset.mul_sum]
  simp only [Nat.cast_zero, mul_zero, zero_mul, zero_div, Real.cos_zero, Real.sin_zero, mul_one,
    sub_zero, cosCoeff, sinCoeff]
  congr 1
  refine Finset.sum_congr rfl fun h _ => ?_
  ring

/-- [proved-derived; formal-checked] **`⌊n/2⌋` harmonics read every function of a residue**, as an
existence statement. -/
theorem harmonic_expansion (f : ZMod n → ℝ) :
    ∃ (a : ℝ) (b c : ℕ → ℝ), ∀ k : ZMod n,
      f k = a + ∑ h ∈ Icc 1 (n / 2),
        (b h * Real.cos (2 * π * h * k.val / n) + c h * Real.sin (2 * π * h * k.val / n)) :=
  ⟨cosCoeff n f 0, cosCoeff n f, sinCoeff n f, harmonic_expansion_eq n f⟩

end Expansion

/-! ## 3. The harmonics of a face -/

/-- [definition] The ring's harmonic `h` of a face `ρ`, `q_h = ρ^h / |ρ|^(h−1)`: the turn taken `h`
times at the face's length. -/
noncomputable def harmonic (h : ℕ) (ρ : ℂ) : ℂ := ρ ^ h / (‖ρ‖ : ℂ) ^ (h - 1)

theorem harmonic_one (ρ : ℂ) : harmonic 1 ρ = ρ := by
  simp [harmonic]

/-- [proved-derived; formal-checked] The owner's recurrence, `q_h = q_(h−1) ρ / |ρ|`. -/
theorem harmonic_succ_succ (m : ℕ) (ρ : ℂ) :
    harmonic (m + 1 + 1) ρ = harmonic (m + 1) ρ * ρ / (‖ρ‖ : ℂ) := by
  simp only [harmonic, Nat.add_sub_cancel]
  rw [pow_succ ρ (m + 1), pow_succ (‖ρ‖ : ℂ) m, mul_div_mul_comm, mul_div_assoc]

/-- [proved-derived; formal-checked] A harmonic has the face's length. -/
theorem norm_harmonic (m : ℕ) (ρ : ℂ) : ‖harmonic (m + 1) ρ‖ = ‖ρ‖ := by
  rw [harmonic, Nat.add_sub_cancel, norm_div, norm_pow, norm_pow, Complex.norm_real, norm_norm]
  rcases eq_or_ne ‖ρ‖ 0 with h | h
  · rw [h]
    simp
  · rw [pow_succ, mul_div_cancel_left₀ _ (pow_ne_zero m h)]

/-- [proved-derived; formal-checked] A harmonic turns `h` times as fast as its face. -/
theorem harmonic_turn (h : ℕ) (ρ : ℂ) (s : ℝ) :
    harmonic h (ρ * Complex.exp (↑s * Complex.I)) =
      harmonic h ρ * Complex.exp (↑s * Complex.I) ^ h := by
  simp only [harmonic]
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, mul_pow]
  ring

/-- [proved-derived; formal-checked] A harmonic scales with its face. -/
theorem harmonic_scale (m : ℕ) (ρ : ℂ) {c : ℝ} (hc : 0 < c) :
    harmonic (m + 1) (ρ * c) = harmonic (m + 1) ρ * c := by
  simp only [harmonic, Nat.add_sub_cancel]
  have hc' : (c : ℂ) ^ m ≠ 0 := pow_ne_zero m (Complex.ofReal_ne_zero.2 hc.ne')
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc.le, Complex.ofReal_mul, mul_pow, mul_pow,
    pow_succ (c : ℂ) m, mul_div_mul_comm, mul_div_cancel_left₀ _ hc']

/-- [definition] The ring's face on residue `k` of `ℤ/n` at length `r`, `r e^(2πik/n)`. -/
noncomputable def residueFace (n : ℕ) (r : ℝ) (k : ZMod n) : ℂ :=
  (r : ℂ) * Complex.exp (((2 * π * k.val / n : ℝ) : ℂ) * Complex.I)

/-- [proved-derived; formal-checked] On a residue's face the harmonic `h` is the character
`r e^(2πihk/n)`. -/
theorem harmonic_residueFace (n : ℕ) {r : ℝ} (hr : 0 < r) (k : ZMod n) (m : ℕ) :
    harmonic (m + 1) (residueFace n r k) =
      (r : ℂ) * Complex.exp (((2 * π * (m + 1 : ℕ) * k.val / n : ℝ) : ℂ) * Complex.I) := by
  have hnorm : ‖residueFace n r k‖ = r := by
    rw [residueFace, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg hr.le]
  have hr' : (r : ℂ) ^ m ≠ 0 := pow_ne_zero m (Complex.ofReal_ne_zero.2 hr.ne')
  rw [harmonic, Nat.add_sub_cancel, hnorm, residueFace, mul_pow, ← Complex.exp_nat_mul, pow_succ,
    mul_assoc, mul_div_cancel_left₀ _ hr']
  congr 2
  push_cast
  ring

/-- [proved-derived; formal-checked] **A ring keyed modulo `n` is read completely at `⌊n/2⌋`
harmonics**: every function of the residue is affine in the two parts of the harmonics
`1, …, ⌊n/2⌋` of the residue's face. -/
theorem ring_read_at_harmonics (n : ℕ) [NeZero n] {r : ℝ} (hr : 0 < r) (f : ZMod n → ℝ) :
    ∃ (a : ℝ) (b c : ℕ → ℝ), ∀ k : ZMod n,
      f k = a + ∑ h ∈ Icc 1 (n / 2),
        (b h * (harmonic h (residueFace n r k)).re + c h * (harmonic h (residueFace n r k)).im) := by
  obtain ⟨a, b, c, hf⟩ := harmonic_expansion n f
  refine ⟨a, fun h => b h / r, fun h => c h / r, fun k => ?_⟩
  rw [hf k]
  congr 1
  refine Finset.sum_congr rfl fun h hh => ?_
  obtain ⟨m, rfl⟩ : ∃ m, h = m + 1 := ⟨h - 1, by have := (Finset.mem_Icc.1 hh).1; omega⟩
  simp only [harmonic_residueFace n hr k m, Complex.re_ofReal_mul, Complex.im_ofReal_mul,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  rw [← mul_assoc, ← mul_assoc, div_mul_cancel₀ _ hr.ne', div_mul_cancel₀ _ hr.ne']

/-! ## 4. The covector carried back to the face -/

/-- [definition] The real pairing of a covector `G` with a face `z`, `⟪G, z⟫ = G_re z_re + G_im z_im`. -/
noncomputable def pair (G : ℂ) : ℂ →L[ℝ] ℝ := G.re • Complex.reCLM + G.im • Complex.imCLM

theorem pair_apply (G z : ℂ) : pair G z = G.re * z.re + G.im * z.im := by
  simp [pair]

/-- [definition] The readout's reading of the harmonics `1, …, H` of a face, `Σ_h ⟪G_h, q_h⟫`. -/
noncomputable def reading (H : ℕ) (G : ℕ → ℂ) (ρ : ℂ) : ℝ :=
  ∑ h ∈ Icc 1 H, pair (G h) (harmonic h ρ)

/-- [definition] The turn covector of the harmonics past the first,
`t = Σ_(h≥2) h (G_h,im q_h,re − G_h,re q_h,im)`. -/
noncomputable def turnCovector (H : ℕ) (G : ℕ → ℂ) (ρ : ℂ) : ℝ :=
  ∑ h ∈ Icc 2 H, (h : ℝ) * ((G h).im * (harmonic h ρ).re - (G h).re * (harmonic h ρ).im)

/-- [definition] The covector carried back to the face (`harmonics_adjoint`),
`∂ρ = G_1 + t (−ρ_im, ρ_re)/|ρ|²`. -/
noncomputable def harmonicsAdjoint (H : ℕ) (G : ℕ → ℂ) (ρ : ℂ) : ℂ :=
  G 1 + ((turnCovector H G ρ / ‖ρ‖ ^ 2 : ℝ) : ℂ) * (Complex.I * ρ)

theorem harmonicsAdjoint_re (H : ℕ) (G : ℕ → ℂ) (ρ : ℂ) :
    (harmonicsAdjoint H G ρ).re = (G 1).re + turnCovector H G ρ * -ρ.im / ‖ρ‖ ^ 2 := by
  rw [harmonicsAdjoint, Complex.add_re, Complex.re_ofReal_mul, Complex.I_mul_re]
  ring

theorem harmonicsAdjoint_im (H : ℕ) (G : ℕ → ℂ) (ρ : ℂ) :
    (harmonicsAdjoint H G ρ).im = (G 1).im + turnCovector H G ρ * ρ.re / ‖ρ‖ ^ 2 := by
  rw [harmonicsAdjoint, Complex.add_im, Complex.im_ofReal_mul, Complex.I_mul_im]
  ring

theorem Icc_one_eq_insert {H : ℕ} (hH : 1 ≤ H) : Icc 1 H = insert 1 (Icc 2 H) := by
  ext h
  simp only [Finset.mem_Icc, Finset.mem_insert]
  omega

theorem hasDerivAt_exp_turn :
    HasDerivAt (fun s : ℝ => Complex.exp (↑s * Complex.I)) Complex.I 0 := by
  have h := ((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const Complex.I).cexp
  simpa using h

/-- [proved-derived; formal-checked] One harmonic along the turn moves at
`h (G_im q_re − G_re q_im)`. -/
theorem hasDerivAt_harmonic_turn (G : ℂ) (h : ℕ) (ρ : ℂ) :
    HasDerivAt (fun s : ℝ => pair G (harmonic h (ρ * Complex.exp (↑s * Complex.I))))
      ((h : ℝ) * (G.im * (harmonic h ρ).re - G.re * (harmonic h ρ).im)) 0 := by
  have hd := (hasDerivAt_exp_turn.fun_pow h).const_mul (harmonic h ρ)
  have hp := (pair G).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd
  have hfun : (fun s : ℝ => pair G (harmonic h (ρ * Complex.exp (↑s * Complex.I)))) =
      (pair G) ∘ fun s : ℝ => harmonic h ρ * Complex.exp (↑s * Complex.I) ^ h := by
    funext s
    simp only [Function.comp_apply, harmonic_turn]
  rw [hfun]
  refine hp.congr_deriv ?_
  simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_pow, mul_one, pair_apply,
    Complex.mul_re, Complex.mul_im, Complex.natCast_re, Complex.natCast_im, Complex.I_re,
    Complex.I_im, mul_zero, sub_zero, zero_add, add_zero]
  ring

/-- [proved-derived; formal-checked] **The reading along the turn** moves at
`Σ_h h (G_h,im q_h,re − G_h,re q_h,im)`. -/
theorem hasDerivAt_reading_turn (H : ℕ) (G : ℕ → ℂ) (ρ : ℂ) :
    HasDerivAt (fun s : ℝ => reading H G (ρ * Complex.exp (↑s * Complex.I)))
      (∑ h ∈ Icc 1 H, (h : ℝ) * ((G h).im * (harmonic h ρ).re - (G h).re * (harmonic h ρ).im))
      0 := by
  unfold reading
  exact HasDerivAt.fun_sum fun h _ => hasDerivAt_harmonic_turn (G h) h ρ

/-- [proved-derived; formal-checked] **The owner's covector reads the turn exactly**: the rate along
the turn is `⟪∂ρ, iρ⟫` for `∂ρ = G_1 + t (−ρ_im, ρ_re)/|ρ|²`. -/
theorem turn_covector_eq (H : ℕ) (hH : 1 ≤ H) (G : ℕ → ℂ) {ρ : ℂ} (hρ : ρ ≠ 0) :
    ∑ h ∈ Icc 1 H, (h : ℝ) * ((G h).im * (harmonic h ρ).re - (G h).re * (harmonic h ρ).im) =
      pair (harmonicsAdjoint H G ρ) (Complex.I * ρ) := by
  have h1 : (1 : ℕ) ∉ Icc 2 H := by simp
  rw [Icc_one_eq_insert hH, Finset.sum_insert h1, harmonic_one, Nat.cast_one, one_mul]
  change _ + turnCovector H G ρ = _
  have hn0 : ‖ρ‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 hρ)
  have key : turnCovector H G ρ * -ρ.im / ‖ρ‖ ^ 2 * -ρ.im +
      turnCovector H G ρ * ρ.re / ‖ρ‖ ^ 2 * ρ.re = turnCovector H G ρ := by
    have e : turnCovector H G ρ * -ρ.im / ‖ρ‖ ^ 2 * -ρ.im +
        turnCovector H G ρ * ρ.re / ‖ρ‖ ^ 2 * ρ.re =
          turnCovector H G ρ * ((ρ.re * ρ.re + ρ.im * ρ.im) / ‖ρ‖ ^ 2) := by
      ring
    rw [e, ← Complex.normSq_apply, ← Complex.sq_norm, div_self hn0, mul_one]
  rw [pair_apply, harmonicsAdjoint_re, harmonicsAdjoint_im, Complex.I_mul_re, Complex.I_mul_im]
  linear_combination (-1 : ℝ) * key

/-- [proved-derived; formal-checked] **The covector on the turn**: along `ρ e^(is)` the reading has
derivative `⟪∂ρ, iρ⟫`. -/
theorem hasDerivAt_reading_turn_adjoint (H : ℕ) (hH : 1 ≤ H) (G : ℕ → ℂ) {ρ : ℂ} (hρ : ρ ≠ 0) :
    HasDerivAt (fun s : ℝ => reading H G (ρ * Complex.exp (↑s * Complex.I)))
      (pair (harmonicsAdjoint H G ρ) (Complex.I * ρ)) 0 := by
  rw [← turn_covector_eq H hH G hρ]
  exact hasDerivAt_reading_turn H G ρ

/-! ## 5. The radial part, and the ratio face that hides it -/

/-- [proved-derived; formal-checked] Along the radius the reading scales with the face. -/
theorem reading_radial (H : ℕ) (G : ℕ → ℂ) (ρ : ℂ) (s : ℝ) :
    reading H G (ρ * ((Real.exp s : ℝ) : ℂ)) = Real.exp s * reading H G ρ := by
  unfold reading
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun h hh => ?_
  obtain ⟨m, rfl⟩ : ∃ m, h = m + 1 := ⟨h - 1, by have := (Finset.mem_Icc.1 hh).1; omega⟩
  rw [harmonic_scale m ρ (Real.exp_pos s)]
  simp only [pair_apply, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero, zero_add, add_zero]
  ring

theorem hasDerivAt_reading_radial (H : ℕ) (G : ℕ → ℂ) (ρ : ℂ) :
    HasDerivAt (fun s : ℝ => reading H G (ρ * ((Real.exp s : ℝ) : ℂ))) (reading H G ρ) 0 := by
  have h := (Real.hasDerivAt_exp 0).mul_const (reading H G ρ)
  rw [Real.exp_zero, one_mul] at h
  have hfun : (fun s : ℝ => reading H G (ρ * ((Real.exp s : ℝ) : ℂ))) =
      fun s => Real.exp s * reading H G ρ := funext fun s => reading_radial H G ρ s
  rw [hfun]
  exact h

/-- [proved-derived; formal-checked] The reading is the owner's covector paired with the face, plus
the harmonics' radial part `Σ_(h≥2) ⟪G_h, q_h⟫`. -/
theorem reading_eq_radial_split (H : ℕ) (hH : 1 ≤ H) (G : ℕ → ℂ) (ρ : ℂ) :
    reading H G ρ = pair (harmonicsAdjoint H G ρ) ρ + ∑ h ∈ Icc 2 H, pair (G h) (harmonic h ρ) := by
  have h1 : (1 : ℕ) ∉ Icc 2 H := by simp
  rw [reading, Icc_one_eq_insert hH, Finset.sum_insert h1, harmonic_one]
  congr 1
  rw [pair_apply, pair_apply, harmonicsAdjoint_re, harmonicsAdjoint_im]
  ring

/-- [proved-derived; formal-checked] **The radial part the owner drops**: along the radius the
reading moves by `⟪∂ρ, ρ⟫ + Σ_(h≥2) ⟪G_h, q_h⟫`. -/
theorem hasDerivAt_reading_radial_split (H : ℕ) (hH : 1 ≤ H) (G : ℕ → ℂ) (ρ : ℂ) :
    HasDerivAt (fun s : ℝ => reading H G (ρ * ((Real.exp s : ℝ) : ℂ)))
      (pair (harmonicsAdjoint H G ρ) ρ + ∑ h ∈ Icc 2 H, pair (G h) (harmonic h ρ)) 0 := by
  rw [← reading_eq_radial_split H hH G ρ]
  exact hasDerivAt_reading_radial H G ρ

/-- [definition] The ring's face as a ratio to its own length, `ρ = r q / |q|` (`r` the declared
scale, `2^16` in the owner). -/
noncomputable def ratioFace (r : ℝ) (q : ℂ) : ℂ := ((r / ‖q‖ : ℝ) : ℂ) * q

theorem ratioFace_turn (r : ℝ) (q : ℂ) (s : ℝ) :
    ratioFace r (q * Complex.exp (↑s * Complex.I)) = ratioFace r q * Complex.exp (↑s * Complex.I) := by
  rw [ratioFace, ratioFace, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, mul_assoc]

theorem ratioFace_radial (r : ℝ) (q : ℂ) (s : ℝ) :
    ratioFace r (q * ((Real.exp s : ℝ) : ℂ)) = ratioFace r q := by
  rcases eq_or_ne q 0 with hq | hq
  · simp [ratioFace, hq]
  · have he : Real.exp s ≠ 0 := (Real.exp_pos s).ne'
    rw [ratioFace, ratioFace, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos s).le,
      mul_comm q, ← mul_assoc, ← Complex.ofReal_mul, div_mul_eq_mul_div, mul_div_mul_right _ _ he]

/-- [proved-derived; formal-checked] **Through the ratio face the turn reads `⟪∂ρ, iρ⟫`.** -/
theorem hasDerivAt_ratio_turn (H : ℕ) (hH : 1 ≤ H) (G : ℕ → ℂ) {r : ℝ} (hr : r ≠ 0) {q : ℂ}
    (hq : q ≠ 0) :
    HasDerivAt (fun s : ℝ => reading H G (ratioFace r (q * Complex.exp (↑s * Complex.I))))
      (pair (harmonicsAdjoint H G (ratioFace r q)) (Complex.I * ratioFace r q)) 0 := by
  have hρ : ratioFace r q ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.2 (div_ne_zero hr (norm_ne_zero_iff.2 hq))) hq
  simp only [ratioFace_turn]
  exact hasDerivAt_reading_turn_adjoint H hH G hρ

/-- [proved-derived; formal-checked] **Through the ratio face the radius is invisible**: the reading
does not move, so the radial part the owner drops costs nothing. -/
theorem hasDerivAt_ratio_radial (H : ℕ) (G : ℕ → ℂ) (r : ℝ) (q : ℂ) :
    HasDerivAt (fun s : ℝ => reading H G (ratioFace r (q * ((Real.exp s : ℝ) : ℂ)))) 0 0 := by
  simp only [ratioFace_radial]
  exact hasDerivAt_const _ _

end Holonics.HNN.RingHarmonics
