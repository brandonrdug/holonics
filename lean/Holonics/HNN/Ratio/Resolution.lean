import Holonics.HNN.Ratio
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# HNN.Ratio.Resolution: what the receiver's own statistics can tell apart

[definition] The derivation of the contact-loop record (October 2, §11) asks whether a change of
the medium that moves the receiver's exponents by `δ_c` bits can be read by the receiver at all.
A receiving phase reads `p̂_c = 2^(v_c)/Z` (`HNN/Ratio.codeLength_eq_face`, the owner's
`NormalizedExponential.face` at the potentials `v ln 2`). Everything here is in bits of the
exponent `v`. No temperature enters: the receiving map's gain, which plays the role of
`1/(k_B T ln 2)`, is a learned state of the receiver, and a change of that gain is part of `δ`.

[proved-derived; formal-checked] What is proved.

1. **One reading carries at most `(ln 2/8)·(max δ − min δ)²` bits about the change, exactly, for
   every `δ`** (`klBits_face_shift_le`, both directions; `klDivergence_face_shift_le`,
   `klDivergence_face_shift_le'` in nats). The divergence of a shifted face is
   `log Σ_c p_c e^(ψ_c) − Σ_c p_c ψ_c` (`klDivergence_face_shift`), and Hoeffding's lemma bounds
   it (`log_mean_exp_sub_mean_le`, from the two-point bound `two_point_log_le`). With
   `|δ_c| ≤ M` this gives the record's `(ln 2/2)·M²` as an exact bound, not only to second order
   (`klBits_face_shift_le_abs`). The face depends only on differences of exponents, so the range
   `max δ − min δ`, not `max |δ|`, is what a reading can see.
2. **Independent readings add their divergences** (`klDivergence_joint`): `N` readings, each
   within the bound, carry at most `N` times it (`klDivergence_joint_le`).
3. **What a divergence allows a test.** For any test of the two media from the readings, the two
   error probabilities sum to at least `1 − √D_nats` (`test_error_ge`, through the Bhattacharyya
   coefficient `exp_neg_half_kl_le`, Cauchy–Schwarz and `1 − e^(−D) ≤ D`). Joined with 1 and 2,
   `receiver_cannot_tell`: over `N` independent readings with `|δ| ≤ M` bits, every test errs with
   `α + β ≥ 1 − √(N (ln 2)² M²/2)`.
4. **On data no face produced, the code moves at first order.** The difference of the two media's
   code lengths at any target is within `max δ − min δ` bits (`codeLength_shift_abs_le`), so over
   `N` readings the code moves by at most `N·(max δ − min δ)` (`codeLength_shift_sum_le`). This
   bound is linear in `δ`: the quadratic bounds 1–3 hold only when the readings' outcomes are drawn
   from one of the two faces.
5. **The station score's curvature is `ln 2/2`** (the constants record of October 2, owed item 1).
   The base-two score obeys `ℓ_t(f + δ) ≤ ℓ_t(f) + Σ (p − e_t)·δ + ½ (ln 2/2) Σ δ²`
   (`codeLength_quadratic_upper`): its remainder over the first-order term is the face's
   divergence in bits, which item 1 bounds by `(ln 2/8)(max δ − min δ)² ≤ (ln 2/4) Σ δ²`. The
   phase part `½ Σ q_c Δ_c²` is exactly quadratic with curvature `q_c/4` (`alignCost_quadratic`),
   so with `q_c ≤ 1` the whole score has the one curvature `ln 2/2`
   (`station_score_quadratic_upper`). This is the model `Holon/Deposition.quadratic_upper_model`
   and `certified_step_descends` consume, with `s` of `gauss_newton_curvature` now a theorem:
   `s = ln 2/2`. The code's `s = ½` is sound and loose by `1/ln 2 ∈ (36/25, 13/9)`; `26/75` and
   `3/8` are rational enclosures above `ln 2/2` (`station_curvature_constant`).
6. **The grain lemma** (owed item 2). Two media whose exponents share every cell of the grain
   `1/L` carry less than `(ln 2/2)/L²` bits a reading, in both directions (`grain_lemma`), and two
   equal classes shifted by `±t` carry at least `(ln 2/2) t² − (ln 2)³ t⁴/4` (`grain_lemma_tight`,
   through `log cosh s ≥ s²/2 − s⁴/4`), so the bound is reached to second order as `t → 1/L`.
   Over `N` independent readings same-cell media carry less than one bit whenever
   `2L² ≥ N ln 2` (`grain_unconfirmable`, `grain_criterion_iff`). The least such `L` is `47` at
   `N = 6148` and `244` at `N = 171754` (`derived_grains`).
7. **Campaign 1's numbers** (`resolution_aeon_bounds`, `declared_grain_vs_resolution`,
   `measured_change_ratio`, `measured_change_readings`, `measured_aeon_test_bound`,
   `measured_aeon_code_bound`).

[definition] **The record's steps, checked.**

* Step 1 (`p_c = 2^(v_c)/Z`) is the owner's face.
* Step 2 holds: the leading term `(ln 2/2)·Var_p(δ)` is right, and item 1 is an exact bound with the
  same leading coefficient in the worst case (two equal classes, `Var = (max δ − min δ)²/4`).
* Step 3 needs two corrections. Stein's lemma is asymptotic and gives no "exactly when"; the
  threshold `N·D ≥ 1` bit is a declared error level, not derived (at `N·D = 1` bit the best test
  still has `α + β ≥ 1 − √(ln 2) > 1/7`). And the readings' outcomes must be drawn from one of the
  two faces, independently (item 2; sequential readings need the chain rule, not formalized here).
  The inequality the finding uses, unreadable whenever `max|δ| < √(2/(N ln 2))`, holds exactly under
  that criterion (`klBits_face_shift_le_abs`).
* Step 4 holds: `√(2/(1190 ln 2)) ∈ (1/21, 1/20)`, and the declared `1/16` lies above it by less
  than `4/3`. `N = 1190` is the exposure's declared aeon, itself a declared constant.

[definition] **The finding's margins, corrected.** With the measured `max|δ| = 7/2^18` bits:
* it lies between `2^10` and `2^11` times below the resolution, not more than `2^12` times
  (`measured_change_ratio`);
* telling the media apart at one bit needs more than `2^21` aeons (`2^31` readings), not about
  `2^19` (`measured_change_readings`);
* over one aeon every test errs with `α + β ≥ 1 − 2^(−11)` (`measured_aeon_test_bound`);
* on real text, which no face produced, the two media's code over one aeon differs by less than
  `1/15` bit, and a coherent change would reach one bit after about 16 aeons
  (`measured_aeon_code_bound`). The statistical margin is very large; the margin of the code on
  real text is not.

No `axiom`, no `sorry`, no `native_decide`.
-/

noncomputable section

namespace Holonics.HNN.Ratio.Resolution

open Holonics.Computation.HolonicInformationTheory
open Holonics.Computation.HolonicAdjointNormalization
open Holonics.Computation.HolonicAdjointNormalization.NormalizedExponential
open Holonics.HNN.Ratio (codeLength two_rpow_eq_exp grainRead face_constant_on_fibre)
open Holonics.Objects.RatioPhase (alignCost phaseGap)

/-! ## 1. Hoeffding's lemma on a finite section -/

section Hoeffding

/-- The two-point mass `1 − θ + θ e^u` is positive for `θ ∈ [0, 1]`. -/
theorem two_point_pos {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (u : ℝ) :
    0 < 1 - θ + θ * Real.exp u := by
  rcases hθ0.eq_or_lt with h | h
  · subst h; norm_num
  · have := mul_pos h (Real.exp_pos u)
    linarith

/-- [proved-standard; formal-checked] **The two-point bound.** For `θ ∈ [0, 1]` and `h ≥ 0`,
`log(1 − θ + θ e^h) − θ h ≤ h²/8`. Its second derivative in `h` is a two-point variance, at most
`1/4`. -/
theorem two_point_log_le {θ h : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hh : 0 ≤ h) :
    Real.log (1 - θ + θ * Real.exp h) - θ * h ≤ h ^ 2 / 8 := by
  let A : ℝ → ℝ := fun u => 1 - θ + θ * Real.exp u
  have hApos : ∀ u, 0 < A u := two_point_pos hθ0 hθ1
  have hA : ∀ u, HasDerivAt A (θ * Real.exp u) u := by
    intro u
    simpa [A] using ((Real.hasDerivAt_exp u).const_mul θ).const_add (1 - θ)
  let G : ℝ → ℝ := fun u => u / 4 - θ * Real.exp u / A u + θ
  let G' : ℝ → ℝ := fun u => 1 / 4 - θ * (1 - θ) * Real.exp u / A u ^ 2
  have hG : ∀ u, HasDerivAt G (G' u) u := by
    intro u
    have h1 : HasDerivAt (fun u : ℝ => u / 4) (1 / 4) u := by
      simpa using (hasDerivAt_id u).div_const 4
    have h2 := ((Real.hasDerivAt_exp u).const_mul θ).div (hA u) (hApos u).ne'
    refine ((h1.sub h2).add_const θ).congr_deriv ?_
    show 1 / 4 - (θ * Real.exp u * (1 - θ + θ * Real.exp u) - θ * Real.exp u * (θ * Real.exp u)) /
        (1 - θ + θ * Real.exp u) ^ 2 = 1 / 4 - θ * (1 - θ) * Real.exp u / (1 - θ + θ * Real.exp u) ^ 2
    ring
  have hG'nonneg : 0 ≤ G' := by
    intro u
    have hA2 : 0 < A u ^ 2 := by have := hApos u; positivity
    simp only [G', Pi.zero_apply, sub_nonneg]
    rw [div_le_iff₀ hA2]
    have hsq : 0 ≤ (1 - θ - θ * Real.exp u) ^ 2 := sq_nonneg _
    have : A u ^ 2 - 4 * (θ * (1 - θ) * Real.exp u) = (1 - θ - θ * Real.exp u) ^ 2 := by
      simp only [A]; ring
    linarith
  have hGmono : Monotone G := monotone_of_hasDerivAt_nonneg hG hG'nonneg
  have hG0 : G 0 = 0 := by simp [G, A]
  let F : ℝ → ℝ := fun u => u ^ 2 / 8 - (Real.log (A u) - θ * u)
  have hF : ∀ u, HasDerivAt F (G u) u := by
    intro u
    have h1 : HasDerivAt (fun u : ℝ => u ^ 2 / 8) (u / 4) u := by
      refine ((hasDerivAt_pow 2 u).div_const 8).congr_deriv ?_
      norm_num; ring
    have h2 := ((hA u).log (hApos u).ne').sub ((hasDerivAt_id u).const_mul θ)
    refine (h1.sub h2).congr_deriv ?_
    show _ = u / 4 - θ * Real.exp u / A u + θ
    ring
  have hFmono : MonotoneOn F (Set.Ici 0) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (fun u _ => (hF u).continuousAt.continuousWithinAt)
      (fun u _ => (hF u).hasDerivWithinAt) ?_
    intro u hu
    rw [interior_Ici] at hu
    have := hGmono (le_of_lt hu)
    linarith
  have hF0 : F 0 = 0 := by simp [F, A]
  have := hFmono Set.self_mem_Ici (Set.mem_Ici.mpr hh) hh
  rw [hF0] at this
  simp only [F, A] at this
  linarith

theorem nonempty_of_section {ι : Type*} [Fintype ι] (p : PositiveProbabilitySection ι) :
    Nonempty ι := by
  by_contra h
  rw [not_nonempty_iff] at h
  have := p.normalized
  simp at this

/-- [proved-standard; formal-checked] **Hoeffding's lemma on a finite section.** For a positive
normalized section `p` and `a ≤ ψ ≤ b`, `log Σ p e^ψ − Σ p ψ ≤ (b − a)²/8`. -/
theorem log_mean_exp_sub_mean_le {ι : Type*} [Fintype ι] (p : PositiveProbabilitySection ι)
    (ψ : ι → ℝ) {a b : ℝ} (ha : ∀ i, a ≤ ψ i) (hb : ∀ i, ψ i ≤ b) :
    Real.log (∑ i, p.mass i * Real.exp (ψ i)) - ∑ i, p.mass i * ψ i ≤ (b - a) ^ 2 / 8 := by
  have hne := nonempty_of_section p
  obtain ⟨i₀⟩ := hne
  have hab : a ≤ b := (ha i₀).trans (hb i₀)
  have hma : a ≤ ∑ i, p.mass i * ψ i := by
    calc a = ∑ i, p.mass i * a := by rw [← Finset.sum_mul, p.normalized, one_mul]
      _ ≤ _ := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (ha i) (p.nonnegative i)
  have hmb : ∑ i, p.mass i * ψ i ≤ b := by
    calc ∑ i, p.mass i * ψ i ≤ ∑ i, p.mass i * b :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hb i) (p.nonnegative i)
      _ = b := by rw [← Finset.sum_mul, p.normalized, one_mul]
  have hS : 0 < ∑ i, p.mass i * Real.exp (ψ i) :=
    Finset.sum_pos (fun i _ => mul_pos (p.positive i) (Real.exp_pos _)) ⟨i₀, Finset.mem_univ _⟩
  rcases hab.eq_or_lt with heq | hlt
  · -- a constant shift: the section's mean exponential is `e^a`
    subst heq
    have hψ : ∀ i, ψ i = a := fun i => le_antisymm (hb i) (ha i)
    simp only [hψ]
    rw [← Finset.sum_mul, ← Finset.sum_mul, p.normalized]
    simp
  set m := ∑ i, p.mass i * ψ i with hm
  have hh : 0 < b - a := sub_pos.mpr hlt
  have hconv : ∀ i, Real.exp (ψ i) ≤
      (b - ψ i) / (b - a) * Real.exp a + (ψ i - a) / (b - a) * Real.exp b := by
    intro i
    have h := convexOn_exp.2 (Set.mem_univ a) (Set.mem_univ b)
      (div_nonneg (sub_nonneg.2 (hb i)) hh.le) (div_nonneg (sub_nonneg.2 (ha i)) hh.le)
      (by field_simp [hh.ne']; ring)
    simp only [smul_eq_mul] at h
    have harg : (b - ψ i) / (b - a) * a + (ψ i - a) / (b - a) * b = ψ i := by
      field_simp [hh.ne']; ring
    rwa [harg] at h
  have hexpb : Real.exp b = Real.exp a * Real.exp (b - a) := by
    rw [← Real.exp_add]; congr 1; ring
  set θ := (m - a) / (b - a) with hθ
  have hθ0 : 0 ≤ θ := div_nonneg (sub_nonneg.2 hma) hh.le
  have hθ1 : θ ≤ 1 := (div_le_one hh).2 (by linarith)
  have hsum : ∑ i, p.mass i * Real.exp (ψ i) ≤
      Real.exp a * (1 - θ + θ * Real.exp (b - a)) := by
    calc ∑ i, p.mass i * Real.exp (ψ i)
        ≤ ∑ i, p.mass i * ((b - ψ i) / (b - a) * Real.exp a +
            (ψ i - a) / (b - a) * Real.exp b) :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hconv i) (p.nonnegative i)
      _ = (Real.exp b - Real.exp a) / (b - a) * m +
            (b * Real.exp a - a * Real.exp b) / (b - a) * ∑ i, p.mass i := by
          rw [hm, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          field_simp [hh.ne']
          ring
      _ = Real.exp a * (1 - θ + θ * Real.exp (b - a)) := by
          rw [p.normalized, hθ, hexpb]
          field_simp [hh.ne']
          ring
  have hlog : Real.log (∑ i, p.mass i * Real.exp (ψ i)) ≤
      a + Real.log (1 - θ + θ * Real.exp (b - a)) := by
    calc Real.log (∑ i, p.mass i * Real.exp (ψ i))
        ≤ Real.log (Real.exp a * (1 - θ + θ * Real.exp (b - a))) := Real.log_le_log hS hsum
      _ = a + Real.log (1 - θ + θ * Real.exp (b - a)) := by
          rw [Real.log_mul (Real.exp_pos a).ne' (two_point_pos hθ0 hθ1 _).ne', Real.log_exp]
  have htwo := two_point_log_le hθ0 hθ1 hh.le
  have hθh : θ * (b - a) = m - a := by rw [hθ]; field_simp [hh.ne']
  linarith

end Hoeffding

/-! ## 2. One reading of a shifted face -/

section Reading

variable {ι : Type*} [Fintype ι] [Nonempty ι]

theorem partition_shift (φ ψ : ι → ℝ) :
    partition (φ + ψ) = partition φ * ∑ i, (face φ).mass i * Real.exp (ψ i) := by
  have hZ := partition_ne_zero φ
  rw [Finset.mul_sum]
  calc partition (φ + ψ) = ∑ i, Real.exp (φ i) * Real.exp (ψ i) := by
        simp [partition, Real.exp_add]
    _ = _ := Finset.sum_congr rfl fun i _ => by
        simp only [face]
        field_simp

/-- [proved-derived; formal-checked] **The divergence of a shifted face.** Shifting the potentials
by `ψ` gives `D(p‖p_ψ) = log Σ p e^ψ − Σ p ψ`, with `p` the face before the shift. -/
theorem klDivergence_face_shift (φ ψ : ι → ℝ) :
    (face φ).klDivergence (face (φ + ψ)) =
      Real.log (∑ i, (face φ).mass i * Real.exp (ψ i)) - ∑ i, (face φ).mass i * ψ i := by
  have hS : 0 < ∑ i, (face φ).mass i * Real.exp (ψ i) :=
    Finset.sum_pos (fun i _ => mul_pos ((face φ).positive i) (Real.exp_pos _))
      Finset.univ_nonempty
  have hlog : Real.log (partition (φ + ψ)) - Real.log (partition φ) =
      Real.log (∑ i, (face φ).mass i * Real.exp (ψ i)) := by
    rw [partition_shift, Real.log_mul (partition_ne_zero φ) hS.ne']
    ring
  rw [PositiveProbabilitySection.klDivergence_eq_logDifference]
  simp_rw [log_face_mass]
  calc ∑ i, (face φ).mass i * (φ i - Real.log (partition φ) -
          ((φ + ψ) i - Real.log (partition (φ + ψ))))
      = ∑ i, (face φ).mass i * (Real.log (partition (φ + ψ)) - Real.log (partition φ)) -
          ∑ i, (face φ).mass i * ψ i := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [Pi.add_apply]
        ring
    _ = _ := by rw [← Finset.sum_mul, (face φ).normalized, one_mul, hlog]

/-- [proved-derived; formal-checked] **One reading's divergence, before against after.** If the
shift lies in `[a, b]` (nats), `D(p‖p_ψ) ≤ (b − a)²/8`. -/
theorem klDivergence_face_shift_le (φ ψ : ι → ℝ) {a b : ℝ} (ha : ∀ i, a ≤ ψ i)
    (hb : ∀ i, ψ i ≤ b) :
    (face φ).klDivergence (face (φ + ψ)) ≤ (b - a) ^ 2 / 8 := by
  rw [klDivergence_face_shift]
  exact log_mean_exp_sub_mean_le (face φ) ψ ha hb

/-- [proved-derived; formal-checked] **One reading's divergence, after against before**, with the
same bound: the face before is the face after shifted by `−ψ`, whose range is the same. -/
theorem klDivergence_face_shift_le' (φ ψ : ι → ℝ) {a b : ℝ} (ha : ∀ i, a ≤ ψ i)
    (hb : ∀ i, ψ i ≤ b) :
    (face (φ + ψ)).klDivergence (face φ) ≤ (b - a) ^ 2 / 8 := by
  have hface : face φ = face (φ + ψ + -ψ) := by rw [add_neg_cancel_right]
  rw [hface]
  have := klDivergence_face_shift_le (φ + ψ) (-ψ) (a := -b) (b := -a)
    (fun i => neg_le_neg (hb i)) (fun i => neg_le_neg (ha i))
  calc _ ≤ (-a - -b) ^ 2 / 8 := this
    _ = (b - a) ^ 2 / 8 := by ring

theorem face_bits_shift (v δ : ι → ℝ) :
    (face fun i => (v i + δ i) * Real.log 2) =
      face ((fun i => v i * Real.log 2) + fun i => δ i * Real.log 2) := by
  congr 1
  funext i
  simp only [Pi.add_apply]
  ring

/-- [proved-derived; formal-checked] **One reading carries at most `(ln 2/8)(b − a)²` bits.** The
receiver's face `2^v/Z` moved to `2^(v+δ)/Z` with `a ≤ δ ≤ b` bits: the divergence in bits, in
either direction, is at most `(ln 2/8)(b − a)²`. -/
theorem klBits_face_shift_le (v δ : ι → ℝ) {a b : ℝ} (ha : ∀ i, a ≤ δ i) (hb : ∀ i, δ i ≤ b) :
    (face fun i => v i * Real.log 2).klDivergence (face fun i => (v i + δ i) * Real.log 2) /
        Real.log 2 ≤ Real.log 2 / 8 * (b - a) ^ 2 ∧
      (face fun i => (v i + δ i) * Real.log 2).klDivergence (face fun i => v i * Real.log 2) /
        Real.log 2 ≤ Real.log 2 / 8 * (b - a) ^ 2 := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ha' : ∀ i, a * Real.log 2 ≤ δ i * Real.log 2 :=
    fun i => mul_le_mul_of_nonneg_right (ha i) hl.le
  have hb' : ∀ i, δ i * Real.log 2 ≤ b * Real.log 2 :=
    fun i => mul_le_mul_of_nonneg_right (hb i) hl.le
  have key : (b * Real.log 2 - a * Real.log 2) ^ 2 / 8 / Real.log 2 =
      Real.log 2 / 8 * (b - a) ^ 2 := by
    field_simp
  rw [face_bits_shift]
  constructor
  · rw [← key]
    exact div_le_div_of_nonneg_right
      (klDivergence_face_shift_le _ (fun i => δ i * Real.log 2) ha' hb') hl.le
  · rw [← key]
    exact div_le_div_of_nonneg_right
      (klDivergence_face_shift_le' _ (fun i => δ i * Real.log 2) ha' hb') hl.le

/-- [proved-derived; formal-checked] **The record's bound, exact.** With `|δ_c| ≤ M` bits, one
reading carries at most `(ln 2/2)·M²` bits about the change, in either direction. -/
theorem klBits_face_shift_le_abs (v δ : ι → ℝ) {M : ℝ} (hM : ∀ i, |δ i| ≤ M) :
    (face fun i => v i * Real.log 2).klDivergence (face fun i => (v i + δ i) * Real.log 2) /
        Real.log 2 ≤ Real.log 2 / 2 * M ^ 2 ∧
      (face fun i => (v i + δ i) * Real.log 2).klDivergence (face fun i => v i * Real.log 2) /
        Real.log 2 ≤ Real.log 2 / 2 * M ^ 2 := by
  have h := klBits_face_shift_le v δ (a := -M) (b := M) (fun i => neg_le_of_abs_le (hM i))
    (fun i => le_of_abs_le (hM i))
  have e : Real.log 2 / 8 * (M - -M) ^ 2 = Real.log 2 / 2 * M ^ 2 := by ring
  rw [e] at h
  exact h

end Reading

/-! ## 3. Independent readings -/

section Readings

variable {ι ρ : Type*} [Fintype ι] [Fintype ρ] [DecidableEq ρ]

/-- [definition] **The joint section of independent readings**: reading `r` has section `p r`,
and the joint mass of outcomes `x` is `∏_r p_r(x_r)`. -/
def joint (p : ρ → PositiveProbabilitySection ι) : PositiveProbabilitySection (ρ → ι) where
  mass x := ∏ r, (p r).mass (x r)
  positive x := Finset.prod_pos fun r _ => (p r).positive (x r)
  normalized := by
    show ∑ x : ρ → ι, ∏ r, (p r).mass (x r) = 1
    have h := Fintype.prod_sum (κ := fun _ : ρ => ι) (fun r i => (p r).mass i)
    rw [← h]
    simp [PositiveProbabilitySection.normalized]

/-- [proved-derived; formal-checked] A function of one reading's outcome has its marginal mean. -/
theorem joint_marginal (p : ρ → PositiveProbabilitySection ι) (r : ρ) (f : ι → ℝ) :
    ∑ x : ρ → ι, (joint p).mass x * f (x r) = ∑ i, (p r).mass i * f i := by
  have key := Fintype.prod_sum (κ := fun _ : ρ => ι)
    (fun s i => (p s).mass i * (if s = r then f i else 1))
  have hl : ∏ s, ∑ i, (p s).mass i * (if s = r then f i else 1) = ∑ i, (p r).mass i * f i := by
    rw [Fintype.prod_eq_single r]
    · simp
    · intro s hs
      simp [hs, (p s).normalized]
  have hr : ∀ x : ρ → ι, ∏ s, (p s).mass (x s) * (if s = r then f (x s) else 1) =
      (joint p).mass x * f (x r) := by
    intro x
    rw [Finset.prod_mul_distrib]
    simp [joint]
  rw [← hl, key]
  exact (Finset.sum_congr rfl fun x _ => hr x).symm

/-- [proved-standard; formal-checked] **Independent readings add their divergences.** -/
theorem klDivergence_joint (p q : ρ → PositiveProbabilitySection ι) :
    (joint p).klDivergence (joint q) = ∑ r, (p r).klDivergence (q r) := by
  have hlog : ∀ (s : ρ → PositiveProbabilitySection ι) (x : ρ → ι),
      Real.log ((joint s).mass x) = ∑ r, Real.log ((s r).mass (x r)) := by
    intro s x
    exact Real.log_prod (fun r _ => ((s r).positive (x r)).ne')
  rw [PositiveProbabilitySection.klDivergence_eq_logDifference]
  simp_rw [hlog, ← Finset.sum_sub_distrib, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [PositiveProbabilitySection.klDivergence_eq_logDifference]
  exact joint_marginal p r (fun i => Real.log ((p r).mass i) - Real.log ((q r).mass i))

/-- [proved-derived; formal-checked] `N` readings, each carrying at most `B`, carry at most `N·B`. -/
theorem klDivergence_joint_le (p q : ρ → PositiveProbabilitySection ι) {B : ℝ}
    (h : ∀ r, (p r).klDivergence (q r) ≤ B) :
    (joint p).klDivergence (joint q) ≤ Fintype.card ρ * B := by
  rw [klDivergence_joint]
  calc ∑ r, (p r).klDivergence (q r) ≤ ∑ _r : ρ, B := Finset.sum_le_sum fun r _ => h r
    _ = Fintype.card ρ * B := by simp

end Readings

/-! ## 4. What a divergence allows a test -/

section Testing

variable {Ω : Type*} [Fintype Ω]

/-- [proved-standard; formal-checked] **The Bhattacharyya coefficient dominates `e^(−D/2)`**
(Jensen for `exp`). -/
theorem exp_neg_half_kl_le (P Q : PositiveProbabilitySection Ω) :
    Real.exp (-P.klDivergence Q / 2) ≤ ∑ i, Real.sqrt (P.mass i * Q.mass i) := by
  let y : Ω → ℝ := fun i => (Real.log (Q.mass i) - Real.log (P.mass i)) / 2
  have hj := convexOn_exp.map_sum_le (t := Finset.univ) (w := P.mass) (p := y)
    (fun i _ => P.nonnegative i) P.normalized (fun i _ => Set.mem_univ _)
  have hl : ∑ i, P.mass i • y i = -P.klDivergence Q / 2 := by
    rw [PositiveProbabilitySection.klDivergence_eq_logDifference, neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [smul_eq_mul, y]
    ring
  have hr : ∀ i, P.mass i • Real.exp (y i) = Real.sqrt (P.mass i * Q.mass i) := by
    intro i
    have hp := P.positive i
    have hq := Q.positive i
    have hsq : (P.mass i * Real.exp (y i)) ^ 2 = P.mass i * Q.mass i := by
      rw [mul_pow, ← Real.exp_nat_mul]
      have : ((2 : ℕ) : ℝ) * y i = Real.log (Q.mass i) - Real.log (P.mass i) := by
        simp only [y]; push_cast; ring
      rw [this, Real.exp_sub, Real.exp_log hp, Real.exp_log hq]
      field_simp
    rw [smul_eq_mul, ← hsq, Real.sqrt_sq (mul_pos hp (Real.exp_pos _)).le]
  rw [← hl]
  calc Real.exp (∑ i, P.mass i • y i) ≤ ∑ i, P.mass i • Real.exp (y i) := hj
    _ = _ := Finset.sum_congr rfl fun i _ => hr i

/-- [proved-standard; formal-checked] **No test beats the divergence.** For any decision region
`A` (decide the second medium on `A`), the two error probabilities `P(A) + Q(Aᶜ)` sum to at least
`1 − √D(P‖Q)`, `D` in nats. -/
theorem test_error_ge (P Q : PositiveProbabilitySection Ω) (A : Ω → Prop) [DecidablePred A] :
    1 - Real.sqrt (P.klDivergence Q) ≤ ∑ i, if A i then P.mass i else Q.mass i := by
  set BC := ∑ i, Real.sqrt (P.mass i * Q.mass i) with hBC
  set M := ∑ i, min (P.mass i) (Q.mass i) with hMdef
  have hM : M ≤ ∑ i, if A i then P.mass i else Q.mass i :=
    Finset.sum_le_sum fun i _ => by
      split_ifs
      · exact min_le_left _ _
      · exact min_le_right _ _
  have habs : ∑ i, |P.mass i - Q.mass i| = 2 - 2 * M := by
    have e : ∀ i, |P.mass i - Q.mass i| =
        P.mass i + Q.mass i - 2 * min (P.mass i) (Q.mass i) := by
      intro i
      rcases le_total (P.mass i) (Q.mass i) with h | h
      · rw [min_eq_left h, abs_of_nonpos (by linarith)]; ring
      · rw [min_eq_right h, abs_of_nonneg (by linarith)]; ring
    simp_rw [e]
    rw [hMdef, Finset.sum_sub_distrib, Finset.sum_add_distrib, P.normalized, Q.normalized,
      ← Finset.mul_sum]
    ring
  have hsqrt : ∀ i, Real.sqrt (P.mass i) * Real.sqrt (Q.mass i) =
      Real.sqrt (P.mass i * Q.mass i) := fun i =>
    (Real.sqrt_mul (P.nonnegative i) _).symm
  have hcs : (∑ i, |P.mass i - Q.mass i|) ^ 2 ≤ (2 - 2 * BC) * (2 + 2 * BC) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun i => |Real.sqrt (P.mass i) - Real.sqrt (Q.mass i)|)
      (fun i => Real.sqrt (P.mass i) + Real.sqrt (Q.mass i))
    have e1 : ∀ i, |Real.sqrt (P.mass i) - Real.sqrt (Q.mass i)| *
        (Real.sqrt (P.mass i) + Real.sqrt (Q.mass i)) = |P.mass i - Q.mass i| := by
      intro i
      have hs : 0 ≤ Real.sqrt (P.mass i) + Real.sqrt (Q.mass i) := by positivity
      have hprod : (Real.sqrt (P.mass i) - Real.sqrt (Q.mass i)) *
          (Real.sqrt (P.mass i) + Real.sqrt (Q.mass i)) = P.mass i - Q.mass i := by
        rw [show (Real.sqrt (P.mass i) - Real.sqrt (Q.mass i)) *
            (Real.sqrt (P.mass i) + Real.sqrt (Q.mass i)) =
            Real.sqrt (P.mass i) ^ 2 - Real.sqrt (Q.mass i) ^ 2 by ring,
          Real.sq_sqrt (P.nonnegative i), Real.sq_sqrt (Q.nonnegative i)]
      rw [← hprod, abs_mul, abs_of_nonneg hs]
    have e2 : ∑ i, |Real.sqrt (P.mass i) - Real.sqrt (Q.mass i)| ^ 2 = 2 - 2 * BC := by
      have : ∀ i, |Real.sqrt (P.mass i) - Real.sqrt (Q.mass i)| ^ 2 =
          P.mass i + Q.mass i - 2 * Real.sqrt (P.mass i * Q.mass i) := by
        intro i
        rw [sq_abs, ← hsqrt, sub_sq, Real.sq_sqrt (P.nonnegative i),
          Real.sq_sqrt (Q.nonnegative i)]
        ring
      simp_rw [this]
      rw [hBC, Finset.sum_sub_distrib, Finset.sum_add_distrib, P.normalized, Q.normalized,
        ← Finset.mul_sum]
      ring
    have e3 : ∑ i, (Real.sqrt (P.mass i) + Real.sqrt (Q.mass i)) ^ 2 = 2 + 2 * BC := by
      have : ∀ i, (Real.sqrt (P.mass i) + Real.sqrt (Q.mass i)) ^ 2 =
          P.mass i + Q.mass i + 2 * Real.sqrt (P.mass i * Q.mass i) := by
        intro i
        rw [← hsqrt, add_sq, Real.sq_sqrt (P.nonnegative i), Real.sq_sqrt (Q.nonnegative i)]
        ring
      simp_rw [this]
      rw [hBC, Finset.sum_add_distrib, Finset.sum_add_distrib, P.normalized, Q.normalized,
        ← Finset.mul_sum]
      ring
    simp_rw [e1] at h
    rw [e2, e3] at h
    exact h
  have hBC0 : 0 ≤ BC := Finset.sum_nonneg fun i _ => Real.sqrt_nonneg _
  have hexp := exp_neg_half_kl_le P Q
  have hBC2 : Real.exp (-P.klDivergence Q) ≤ BC ^ 2 := by
    have : Real.exp (-P.klDivergence Q) = Real.exp (-P.klDivergence Q / 2) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [this]
    exact pow_le_pow_left₀ (Real.exp_pos _).le hexp 2
  have hK := Real.add_one_le_exp (-P.klDivergence Q)
  have hsq : (1 - M) ^ 2 ≤ P.klDivergence Q := by
    rw [habs] at hcs
    nlinarith
  have := Real.abs_le_sqrt hsq
  have := le_abs_self (1 - M)
  linarith

/-- [proved-derived; formal-checked] **The receiver cannot tell the media apart.** Over `N`
independent readings whose exponents move by `|δ| ≤ M` bits, every test errs with
`α + β ≥ 1 − √(N (ln 2)² M²/2)`. -/
theorem receiver_cannot_tell {ι ρ : Type*} [Fintype ι] [Nonempty ι] [Fintype ρ] [DecidableEq ρ]
    (v δ : ρ → ι → ℝ) {M : ℝ} (hM : ∀ r c, |δ r c| ≤ M) (A : (ρ → ι) → Prop)
    [DecidablePred A] :
    1 - Real.sqrt (Fintype.card ρ * ((Real.log 2) ^ 2 * M ^ 2 / 2)) ≤
      ∑ x, if A x then (joint fun r => face fun c => v r c * Real.log 2).mass x
        else (joint fun r => face fun c => (v r c + δ r c) * Real.log 2).mass x := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hread : ∀ r, (face fun c => v r c * Real.log 2).klDivergence
      (face fun c => (v r c + δ r c) * Real.log 2) ≤ (Real.log 2) ^ 2 * M ^ 2 / 2 := by
    intro r
    have h := (klBits_face_shift_le_abs (v r) (δ r) (hM r)).1
    rw [div_le_iff₀ hl] at h
    nlinarith
  have hjoint := klDivergence_joint_le _ _ hread
  have htest := test_error_ge (joint fun r => face fun c => v r c * Real.log 2)
    (joint fun r => face fun c => (v r c + δ r c) * Real.log 2) A
  have := Real.sqrt_le_sqrt hjoint
  linarith

end Testing

/-! ## 5. On data no face produced, the code moves at first order -/

section Code

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- [proved-derived; formal-checked] **One reading's code moves by at most the shift's range.**
For any target `t`, `|codeLength (f + δ) t − codeLength f t| ≤ b − a` when `a ≤ δ ≤ b` bits. This
holds whatever produced the target. -/
theorem codeLength_shift_abs_le (f δ : ι → ℝ) {a b : ℝ} (ha : ∀ c, a ≤ δ c)
    (hb : ∀ c, δ c ≤ b) (t : ι) :
    |codeLength (fun c => f c + δ c) t - codeLength f t| ≤ b - a := by
  set S := ∑ c, (2 : ℝ) ^ f c
  set S' := ∑ c, (2 : ℝ) ^ (f c + δ c)
  have hS : 0 < S := Finset.sum_pos (fun c _ => by positivity) Finset.univ_nonempty
  have hlo : (2 : ℝ) ^ a * S ≤ S' := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun c _ => ?_
    rw [← Real.rpow_add (by norm_num)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [ha c])
  have hhi : S' ≤ (2 : ℝ) ^ b * S := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun c _ => ?_
    rw [← Real.rpow_add (by norm_num)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [hb c])
  have hS' : 0 < S' := lt_of_lt_of_le (by positivity) hlo
  have hlog1 : a + Real.logb 2 S ≤ Real.logb 2 S' := by
    have := Real.logb_le_logb_of_le (b := 2) (by norm_num) (mul_pos (by positivity) hS) hlo
    rwa [Real.logb_mul (by positivity) hS.ne', Real.logb_rpow (by norm_num) (by norm_num)] at this
  have hlog2 : Real.logb 2 S' ≤ b + Real.logb 2 S := by
    have := Real.logb_le_logb_of_le (b := 2) (by norm_num) hS' hhi
    rwa [Real.logb_mul (by positivity) hS.ne', Real.logb_rpow (by norm_num) (by norm_num)] at this
  have hdiff : codeLength (fun c => f c + δ c) t - codeLength f t =
      -δ t + (Real.logb 2 S' - Real.logb 2 S) := by
    simp only [codeLength, S, S']
    ring
  rw [hdiff, abs_le]
  constructor <;> linarith [ha t, hb t]

/-- [proved-derived; formal-checked] **Over `N` readings the code moves by at most `N` ranges**,
at first order in the shift. -/
theorem codeLength_shift_sum_le {ρ : Type*} [Fintype ρ] (f δ : ρ → ι → ℝ) (t : ρ → ι)
    {a b : ℝ} (ha : ∀ r c, a ≤ δ r c) (hb : ∀ r c, δ r c ≤ b) :
    |∑ r, (codeLength (fun c => f r c + δ r c) (t r) - codeLength (f r) (t r))| ≤
      Fintype.card ρ * (b - a) := by
  calc |∑ r, (codeLength (fun c => f r c + δ r c) (t r) - codeLength (f r) (t r))|
      ≤ ∑ r, |codeLength (fun c => f r c + δ r c) (t r) - codeLength (f r) (t r)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r : ρ, (b - a) :=
        Finset.sum_le_sum fun r _ => codeLength_shift_abs_le (f r) (δ r) (ha r) (hb r) (t r)
    _ = Fintype.card ρ * (b - a) := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end Code

/-! ## 6. The station score's curvature and the grain lemma -/

theorem log_two_bounds : (0.6931471803 : ℝ) < Real.log 2 ∧ Real.log 2 < 0.6931471808 :=
  ⟨Real.log_two_gt_d9, Real.log_two_lt_d9⟩

section Curvature

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-- [proved-derived; formal-checked] **The station score's curvature, magnitude part.** The
base-two score `ℓ_t(f) = −f_t + log₂ Σ_c 2^(f_c)` in its realified logits `f` obeys the quadratic
upper model with curvature `ln 2/2`:
`ℓ_t(f + δ) ≤ ℓ_t(f) + Σ_c (p_c − [c = t]) δ_c + ½ (ln 2/2) Σ_c δ_c²`, with `p` the face at `f`.
The remainder over the first-order term is the face's divergence in bits,
`log₂ Σ p 2^δ − Σ p δ`, and Hoeffding's lemma bounds it by `(ln 2/8)(max δ − min δ)²`, at most
`(ln 2/4) Σ δ²`. This is the Hessian bound `ln 2 (diag p − ppᵀ) ⪯ (ln 2/2) I` in the integrated
form `Holon/Deposition.quadratic_upper_model` consumes, so `s = ln 2/2` is a theorem. -/
theorem codeLength_quadratic_upper (f δ : ι → ℝ) (t : ι) :
    codeLength (fun c => f c + δ c) t ≤ codeLength f t +
        ∑ c, ((face fun c => f c * Real.log 2).mass c - if c = t then 1 else 0) * δ c +
      1 / 2 * (Real.log 2 / 2) * ∑ c, δ c ^ 2 := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hS : 0 < ∑ c, (2 : ℝ) ^ f c :=
    Finset.sum_pos (fun c _ => by positivity) Finset.univ_nonempty
  have hpart : partition (fun c => f c * Real.log 2) = ∑ c, (2 : ℝ) ^ f c := by
    simp only [partition, two_rpow_eq_exp]
  have hmass : ∀ c, (face fun c => f c * Real.log 2).mass c = (2 : ℝ) ^ f c / ∑ c, (2 : ℝ) ^ f c := by
    intro c
    simp only [face, hpart, two_rpow_eq_exp]
  set p := face fun c => f c * Real.log 2 with hp
  set T := ∑ c, p.mass c * Real.exp (δ c * Real.log 2) with hTdef
  have hT : 0 < T := Finset.sum_pos (fun c _ => mul_pos (p.positive c) (Real.exp_pos _))
    Finset.univ_nonempty
  have hS' : ∑ c, (2 : ℝ) ^ (f c + δ c) = (∑ c, (2 : ℝ) ^ f c) * T := by
    rw [hTdef, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [hmass, Real.rpow_add (by norm_num), ← two_rpow_eq_exp (δ c)]
    field_simp [hS.ne']
  have hdiff : codeLength (fun c => f c + δ c) t - codeLength f t =
      -δ t + Real.log T / Real.log 2 := by
    simp only [codeLength]
    rw [hS', Real.logb_mul hS.ne' hT.ne']
    simp only [Real.logb]
    ring
  have hfirst : ∑ c, (p.mass c - if c = t then 1 else 0) * δ c = ∑ c, p.mass c * δ c - δ t := by
    simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
  obtain ⟨i₁, -, hi₁⟩ := Finset.exists_min_image Finset.univ δ Finset.univ_nonempty
  obtain ⟨i₂, -, hi₂⟩ := Finset.exists_max_image Finset.univ δ Finset.univ_nonempty
  have hH := log_mean_exp_sub_mean_le p (fun c => δ c * Real.log 2)
    (a := δ i₁ * Real.log 2) (b := δ i₂ * Real.log 2)
    (fun c => mul_le_mul_of_nonneg_right (hi₁ c (Finset.mem_univ _)) hl.le)
    (fun c => mul_le_mul_of_nonneg_right (hi₂ c (Finset.mem_univ _)) hl.le)
  have hmean : ∑ c, p.mass c * (δ c * Real.log 2) = Real.log 2 * ∑ c, p.mass c * δ c := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => by ring
  beta_reduce at hH
  rw [hmean, ← hTdef] at hH
  have hrange : (δ i₂ - δ i₁) ^ 2 ≤ 2 * ∑ c, δ c ^ 2 := by
    by_cases h : i₁ = i₂
    · rw [h, sub_self]
      have : 0 ≤ ∑ c, δ c ^ 2 := Finset.sum_nonneg fun c _ => sq_nonneg _
      nlinarith
    · have hpair : δ i₁ ^ 2 + δ i₂ ^ 2 ≤ ∑ c, δ c ^ 2 := by
        rw [← Finset.sum_pair (f := fun c => δ c ^ 2) h]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun _ _ _ => sq_nonneg _)
      nlinarith [sq_nonneg (δ i₁ + δ i₂)]
  have hlogT : Real.log T / Real.log 2 ≤
      ∑ c, p.mass c * δ c + Real.log 2 / 4 * ∑ c, δ c ^ 2 := by
    rw [div_le_iff₀ hl]
    have e : (δ i₂ * Real.log 2 - δ i₁ * Real.log 2) ^ 2 / 8 =
        Real.log 2 ^ 2 * (δ i₂ - δ i₁) ^ 2 / 8 := by ring
    rw [e] at hH
    have h2 : Real.log 2 ^ 2 * (δ i₂ - δ i₁) ^ 2 ≤ Real.log 2 ^ 2 * (2 * ∑ c, δ c ^ 2) :=
      mul_le_mul_of_nonneg_left hrange (sq_nonneg _)
    nlinarith [h2, hH]
  rw [hfirst]
  have := hdiff
  linarith [hlogT]

omit [Nonempty ι] [DecidableEq ι] in
/-- [proved-derived; formal-checked] **The station score's curvature, phase part.** The
alignment cost `½ Σ_c q_c Δ_c²`, `Δ_c = φ^T_c − y_c/2`, is exactly quadratic in the imaginary
logits `y`: along `y + h` it moves by its slope `−½ q_c Δ_c` and curvature `q_c/4`. -/
theorem alignCost_quadratic (q φT y h : ι → ℝ) :
    alignCost q φT (fun c => y c + h c) = alignCost q φT y +
        ∑ c, (-(1 / 2) * q c * phaseGap φT y c) * h c + 1 / 2 * ∑ c, q c / 4 * h c ^ 2 := by
  unfold alignCost phaseGap
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

/-- [proved-derived; formal-checked] **The whole station score's curvature.** With the target
weights `q_c ≤ 1`, the magnitude score plus the alignment cost obeys the quadratic upper model
in all its realified logits `(f, y)` with the one curvature `ln 2/2`: the phase part's `q_c/4 ≤ ¼`
lies below it. -/
theorem station_score_quadratic_upper (f δ : ι → ℝ) (t : ι) (q φT y h : ι → ℝ)
    (hq1 : ∀ c, q c ≤ 1) :
    codeLength (fun c => f c + δ c) t + alignCost q φT (fun c => y c + h c) ≤
      codeLength f t + alignCost q φT y +
        (∑ c, ((face fun c => f c * Real.log 2).mass c - if c = t then 1 else 0) * δ c +
          ∑ c, (-(1 / 2) * q c * phaseGap φT y c) * h c) +
        1 / 2 * (Real.log 2 / 2) * (∑ c, δ c ^ 2 + ∑ c, h c ^ 2) := by
  have hm := codeLength_quadratic_upper f δ t
  have hp := alignCost_quadratic q φT y h
  have hl : (1 : ℝ) / 2 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hph : ∑ c, q c / 4 * h c ^ 2 ≤ Real.log 2 / 2 * ∑ c, h c ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun c _ => ?_
    have : q c / 4 ≤ Real.log 2 / 2 := by linarith [hq1 c]
    exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
  rw [hp]
  nlinarith [hm, hph]

/-- [proved-derived; formal-checked] **The curvature constant against the code's.** The tight
constant `ln 2/2` lies above the phase part's `¼` and below the code's declared `s = ½` by the
factor `1/ln 2 ∈ (36/25, 13/9)`; its rational upper enclosures `26/75` and the dyadic `3/8`
both lie below `½`. -/
theorem station_curvature_constant :
    1 / 4 < Real.log 2 / 2 ∧ Real.log 2 / 2 < 26 / 75 ∧ (26 : ℝ) / 75 < 3 / 8 ∧
      (3 : ℝ) / 8 < 1 / 2 ∧ 36 / 25 < 1 / Real.log 2 ∧ 1 / Real.log 2 < 13 / 9 := by
  obtain ⟨hlo, hhi⟩ := log_two_bounds
  have hl : 0 < Real.log 2 := by linarith
  refine ⟨by linarith, by linarith, by norm_num, by norm_num, ?_, ?_⟩
  · rw [lt_div_iff₀ hl]; linarith
  · rw [div_lt_iff₀ hl]; linarith

end Curvature

section Grain

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- [proved-standard; formal-checked] `1 + s²/2 ≤ cosh s`. -/
theorem one_add_sq_half_le_cosh (s : ℝ) : 1 + s ^ 2 / 2 ≤ Real.cosh s := by
  have h2 : Real.cosh s = 1 + 2 * Real.sinh (s / 2) ^ 2 := by
    have := Real.cosh_two_mul (s / 2)
    rw [show 2 * (s / 2) = s by ring] at this
    rw [this, Real.cosh_sq]
    ring
  have hab : |s / 2| ≤ |Real.sinh (s / 2)| := by
    rw [Real.abs_sinh]
    exact Real.self_le_sinh_iff.mpr (abs_nonneg _)
  have hsq : |s / 2| ^ 2 ≤ |Real.sinh (s / 2)| ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) hab 2
  rw [sq_abs, sq_abs] at hsq
  rw [h2]
  nlinarith [hsq]

/-- [proved-standard; formal-checked] **The two-class tilt, from below.**
`log cosh s ≥ s²/2 − s⁴/4`: through `log x ≥ 1 − 1/x` at `x ≥ 1 + s²/2`. -/
theorem log_cosh_ge (s : ℝ) : s ^ 2 / 2 - s ^ 4 / 4 ≤ Real.log (Real.cosh s) := by
  have hc := one_add_sq_half_le_cosh s
  have hm : 0 < 1 + s ^ 2 / 2 := by positivity
  have hx : 0 < Real.cosh s := Real.cosh_pos s
  have h1 := Real.one_sub_inv_le_log_of_pos hx
  have h2 : (1 + s ^ 2 / 2)⁻¹ ≥ (Real.cosh s)⁻¹ := inv_anti₀ hm hc
  have h3 : s ^ 2 / 2 - s ^ 4 / 4 ≤ 1 - (1 + s ^ 2 / 2)⁻¹ := by
    have hinv : (1 + s ^ 2 / 2)⁻¹ ≤ 1 - s ^ 2 / 2 + s ^ 4 / 4 := by
      rw [inv_eq_one_div, div_le_iff₀ hm]
      nlinarith [pow_nonneg (sq_nonneg s) 3]
    linarith
  linarith

/-- [proved-derived; formal-checked] **The grain lemma.** Two media whose exponents share every
cell of the grain `1/L` (`HNN/Ratio.grainRead`, the receiver's read) differ by `|δ_c| < 1/L` for
every class, and one reading carries less than `(ln 2/2)/L²` bits about which medium is present,
in both directions. The bound is strict and exact (Hoeffding through `klBits_face_shift_le_abs`,
at the largest `|δ_c|`). -/
theorem grain_lemma {L : ℕ} (hL : 0 < L) (v v' : ι → ℝ)
    (hcell : ∀ c, grainRead L (v' c) = grainRead L (v c)) :
    (face fun i => v i * Real.log 2).klDivergence (face fun i => v' i * Real.log 2) /
        Real.log 2 < Real.log 2 / 2 / (L : ℝ) ^ 2 ∧
      (face fun i => v' i * Real.log 2).klDivergence (face fun i => v i * Real.log 2) /
        Real.log 2 < Real.log 2 / 2 / (L : ℝ) ^ 2 := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  have hδ : ∀ c, |v' c - v c| < 1 / L := by
    intro c
    obtain ⟨-, hk0, hkL, -, -, hiff, -⟩ := face_constant_on_fibre.{0, 0} hL (v c)
    have hself := (hiff (grainRead L (v c)).1 (grainRead L (v c)).2 (v c) hk0 hkL).mp rfl
    have hother := (hiff (grainRead L (v c)).1 (grainRead L (v c)).2 (v' c) hk0 hkL).mp
      (hcell c)
    have e : (((grainRead L (v c)).2 : ℝ) + 1) / L =
        ((grainRead L (v c)).2 : ℝ) / L + 1 / L := by ring
    rw [e] at hself hother
    rw [abs_sub_lt_iff]
    constructor <;> linarith [hself.1, hself.2, hother.1, hother.2]
  obtain ⟨c₀, -, hc₀⟩ := Finset.exists_max_image Finset.univ (fun c => |v' c - v c|)
    Finset.univ_nonempty
  have h := klBits_face_shift_le_abs v (fun i => v' i - v i) (M := |v' c₀ - v c₀|)
    (fun i => hc₀ i (Finset.mem_univ _))
  have e : ∀ i, v i + (v' i - v i) = v' i := fun i => by ring
  simp only [e] at h
  have hsq : |v' c₀ - v c₀| ^ 2 < (1 / (L : ℝ)) ^ 2 :=
    pow_lt_pow_left₀ (hδ c₀) (abs_nonneg _) two_ne_zero
  have hb : Real.log 2 / 2 * |v' c₀ - v c₀| ^ 2 < Real.log 2 / 2 / (L : ℝ) ^ 2 := by
    rw [div_eq_mul_one_div (Real.log 2 / 2), ← one_div_pow]
    exact mul_lt_mul_of_pos_left hsq (by positivity)
  exact ⟨h.1.trans_lt hb, h.2.trans_lt hb⟩

/-- [proved-derived; formal-checked] **The grain lemma is tight.** Two equal classes shifted by
`±t` bits carry at least `(ln 2/2) t² − (ln 2)³ t⁴/4` bits a reading, so as `t → 1/L` the bound
`(ln 2/2)/L²` is reached to second order in `1/L`. -/
theorem grain_lemma_tight (t : ℝ) :
    Real.log 2 / 2 * t ^ 2 - Real.log 2 ^ 3 / 4 * t ^ 4 ≤
      (face fun _ : Bool => (0 : ℝ) * Real.log 2).klDivergence
          (face fun b : Bool => ((0 : ℝ) + if b then t else -t) * Real.log 2) / Real.log 2 := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [face_bits_shift, klDivergence_face_shift]
  have hmass : ∀ b : Bool, (face fun _ : Bool => (0 : ℝ) * Real.log 2).mass b = 1 / 2 := by
    intro b
    norm_num [face, partition, Fintype.sum_bool]
  simp only [hmass, Fintype.sum_bool, if_true, Bool.false_eq_true, if_false]
  have hc : 1 / 2 * Real.exp (t * Real.log 2) + 1 / 2 * Real.exp (-t * Real.log 2) =
      Real.cosh (t * Real.log 2) := by
    rw [Real.cosh_eq, neg_mul]
    ring
  have hz : 1 / 2 * (t * Real.log 2) + 1 / 2 * (-t * Real.log 2) = 0 := by ring
  rw [hc, hz, sub_zero, le_div_iff₀ hl]
  have := log_cosh_ge (t * Real.log 2)
  nlinarith [this]

/-- [proved-derived; formal-checked] **Same-cell media are unconfirmable from `N` readings when
`2L² ≥ N ln 2`.** Over `N` independent readings, each pair of same-cell media, the readings carry
less than `N (ln 2/2)/L²` bits, which is at most one bit exactly when `2L² ≥ N ln 2`
(`grain_criterion_iff`); by `grain_lemma_tight` the criterion is sharp to second order. -/
theorem grain_unconfirmable {ρ : Type*} [Fintype ρ] [DecidableEq ρ] {L : ℕ} (hL : 0 < L)
    (hρ : 0 < Fintype.card ρ) (h : (Fintype.card ρ : ℝ) * Real.log 2 ≤ 2 * (L : ℝ) ^ 2)
    (v v' : ρ → ι → ℝ) (hcell : ∀ r c, grainRead L (v' r c) = grainRead L (v r c)) :
    (joint fun r => face fun i => v r i * Real.log 2).klDivergence
        (joint fun r => face fun i => v' r i * Real.log 2) / Real.log 2 < 1 := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  have : Nonempty ρ := Fintype.card_pos_iff.mp hρ
  rw [klDivergence_joint, Finset.sum_div]
  have hlt : ∑ r, (face fun i => v r i * Real.log 2).klDivergence
        (face fun i => v' r i * Real.log 2) / Real.log 2 <
      ∑ _r : ρ, Real.log 2 / 2 / (L : ℝ) ^ 2 :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun r _ =>
      (grain_lemma hL (v r) (v' r) (hcell r)).1
  refine hlt.trans_le ?_
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [show (Fintype.card ρ : ℝ) * (Real.log 2 / 2 / (L : ℝ) ^ 2) =
      (Fintype.card ρ * Real.log 2) / (2 * (L : ℝ) ^ 2) by ring]
  rw [div_le_one (by positivity)]
  exact h

/-- [proved-derived; formal-checked] **The two-part criterion.** `N (ln 2/2)/L² ≤ 1` exactly when
`2L² ≥ N ln 2`. -/
theorem grain_criterion_iff {L : ℕ} (hL : 0 < L) (N : ℝ) :
    N * (Real.log 2 / 2 / (L : ℝ) ^ 2) ≤ 1 ↔ N * Real.log 2 ≤ 2 * (L : ℝ) ^ 2 := by
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  rw [show N * (Real.log 2 / 2 / (L : ℝ) ^ 2) = (N * Real.log 2) / (2 * (L : ℝ) ^ 2) by
    ring]
  exact div_le_one (by positivity)

/-- [proved-derived; formal-checked] **The derived grains of the constants record.** The least
`L` with `2L² ≥ N ln 2` is `47` at the exposure's declared population `N = 6148` and `244` for
the whole pinned cut, `N = 171754`. -/
theorem derived_grains :
    2 * (46 : ℝ) ^ 2 < 6148 * Real.log 2 ∧ 6148 * Real.log 2 ≤ 2 * (47 : ℝ) ^ 2 ∧
      2 * (243 : ℝ) ^ 2 < 171754 * Real.log 2 ∧ 171754 * Real.log 2 ≤ 2 * (244 : ℝ) ^ 2 := by
  obtain ⟨hlo, hhi⟩ := log_two_bounds
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

end Grain

/-! ## 7. Campaign 1's numbers -/

section Campaign


/-- [proved-derived; formal-checked] **The resolution at one aeon.** With `N = 1190` readings and
the one-bit criterion, `√(2/(1190 ln 2))` lies in `(1/21, 1/20)`. -/
theorem resolution_aeon_bounds :
    1 / 21 < Real.sqrt (2 / (1190 * Real.log 2)) ∧ Real.sqrt (2 / (1190 * Real.log 2)) < 1 / 20 := by
  obtain ⟨hlo, hhi⟩ := log_two_bounds
  have hpos : 0 < 1190 * Real.log 2 := by positivity
  constructor
  · rw [Real.lt_sqrt (by norm_num), lt_div_iff₀ hpos]
    nlinarith
  · rw [Real.sqrt_lt' (by norm_num), div_lt_iff₀ hpos]
    nlinarith

/-- [proved-derived; formal-checked] **The declared grain against the resolution.** The declared
`1/16` bit lies above the resolution, by less than a factor `4/3`. -/
theorem declared_grain_vs_resolution :
    Real.sqrt (2 / (1190 * Real.log 2)) < 1 / 16 ∧
      1 / 16 < 4 / 3 * Real.sqrt (2 / (1190 * Real.log 2)) := by
  obtain ⟨h1, h2⟩ := resolution_aeon_bounds
  constructor <;> linarith

/-- [proved-derived; formal-checked] **The measured change against the resolution.** The largest
measured change `7/2^18` bits lies between `2^10` and `2^11` times below the resolution, so not
more than `2^12` times below it. -/
theorem measured_change_ratio :
    2 ^ 10 * (7 / 2 ^ 18 : ℝ) < Real.sqrt (2 / (1190 * Real.log 2)) ∧
      Real.sqrt (2 / (1190 * Real.log 2)) < 2 ^ 11 * (7 / 2 ^ 18 : ℝ) ∧
      ¬ (2 ^ 12 * (7 / 2 ^ 18 : ℝ) < Real.sqrt (2 / (1190 * Real.log 2))) := by
  obtain ⟨h1, h2⟩ := resolution_aeon_bounds
  refine ⟨by linarith, by linarith, by intro h; linarith⟩

/-- [proved-derived; formal-checked] **How many readings the measured change needs.** If `N`
readings of the measured change accumulate one bit under the bound `(ln 2/2)·M²`, then
`N > 1190·2^21`: more than `2^21` aeons, hence more than `2^31` readings. -/
theorem measured_change_readings (N : ℝ) (h : 1 ≤ N * (Real.log 2 / 2 * (7 / 2 ^ 18) ^ 2)) :
    1190 * 2 ^ 21 < N ∧ (2 : ℝ) ^ 31 < N := by
  obtain ⟨_, hhi⟩ := log_two_bounds
  have hN : 0 ≤ N := by
    by_contra hneg
    replace hneg := not_le.mp hneg
    have : N * (Real.log 2 / 2 * (7 / 2 ^ 18) ^ 2) < 0 :=
      mul_neg_of_neg_of_pos hneg (by positivity)
    linarith
  have hlt : N * (Real.log 2 / 2 * (7 / 2 ^ 18) ^ 2) ≤ N * (17 / 2 ^ 36) :=
    mul_le_mul_of_nonneg_left (by nlinarith) hN
  constructor <;> nlinarith

/-- [proved-derived; formal-checked] **Over one aeon every test errs almost as a coin does.** With
`|δ| ≤ 7/2^18` bits at each of `1190` readings, `√(1190 (ln 2)² M²/2) < 2^(−11)`, so
`receiver_cannot_tell` gives `α + β > 1 − 2^(−11)`. -/
theorem measured_aeon_test_bound :
    Real.sqrt (1190 * ((Real.log 2) ^ 2 * (7 / 2 ^ 18) ^ 2 / 2)) < 1 / 2 ^ 11 := by
  obtain ⟨hlo, hhi⟩ := log_two_bounds
  rw [Real.sqrt_lt' (by norm_num)]
  have h0 : 0 < Real.log 2 := by linarith
  have hsq : (Real.log 2) ^ 2 < 0.4806 := by nlinarith
  nlinarith

/-- [proved-derived; formal-checked] **On real text the code's margin is small.** Over one aeon
the two media's code lengths differ by at most `1190·(2·7/2^18) < 1/15` bit, and a change that moved
every reading's code the same way would reach one bit only after more than `15` aeons. -/
theorem measured_aeon_code_bound :
    (1190 : ℝ) * (2 * (7 / 2 ^ 18)) < 1 / 15 ∧
      ∀ N : ℝ, 1 ≤ N * (2 * (7 / 2 ^ 18)) → 15 * 1190 < N := by
  refine ⟨by norm_num, fun N h => by nlinarith⟩

end Campaign

section Audit

#print axioms two_point_log_le
#print axioms log_mean_exp_sub_mean_le
#print axioms klDivergence_face_shift
#print axioms klDivergence_face_shift_le
#print axioms klDivergence_face_shift_le'
#print axioms klBits_face_shift_le
#print axioms klBits_face_shift_le_abs
#print axioms joint_marginal
#print axioms klDivergence_joint
#print axioms klDivergence_joint_le
#print axioms exp_neg_half_kl_le
#print axioms test_error_ge
#print axioms receiver_cannot_tell
#print axioms codeLength_shift_abs_le
#print axioms codeLength_shift_sum_le
#print axioms resolution_aeon_bounds
#print axioms declared_grain_vs_resolution
#print axioms measured_change_ratio
#print axioms measured_change_readings
#print axioms measured_aeon_test_bound
#print axioms measured_aeon_code_bound
#print axioms codeLength_quadratic_upper
#print axioms alignCost_quadratic
#print axioms station_score_quadratic_upper
#print axioms station_curvature_constant
#print axioms one_add_sq_half_le_cosh
#print axioms log_cosh_ge
#print axioms grain_lemma
#print axioms grain_lemma_tight
#print axioms grain_unconfirmable
#print axioms grain_criterion_iff
#print axioms derived_grains

end Audit

end Holonics.HNN.Ratio.Resolution
