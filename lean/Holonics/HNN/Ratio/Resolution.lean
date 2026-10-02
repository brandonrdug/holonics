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
7. **The odometer covector's pairing** (owed item 3). If the odometer masses obey `r_c ≤ K p_c`,
   then `‖r − q‖²/K ≤ ⟨p − q, r − q⟩` (`odometer_pairing_ratio`). Inside a grain cell the chord
   bound `2^y ≥ (e ln 2/2)(1 + y)` (`two_rpow_ge_chord`, `odometer_le_face_weight`) gives
   `K = 2^(1/L) · 2/(e ln 2)` (`odometer_mass_le`). A step `−η(r − q)` then lowers the smooth score
   by `η a/K` to first order, `a = ‖r − q‖²` (`odometer_step_bound`), and the certificate owes the
   factor `1/K`: under the code's rule the decrease is at least `η a (1/K − ½)`, and `½ η a/K` with
   the rule tightened by `1/K` (`odometer_certified_decrease`). At `L = 16`, `K < 8/7`, so the
   code's rule keeps at least `3/8 · η a` (`odometer_ratio_sixteen`). This covers a logit step
   along the covector itself. A deposit's move pulled back through a locus mixes the stations'
   covectors; item 8 treats it. The curvature `s` (item 5) is a
   separate question: `s = ½` stays sound there; what the factor corrects is the first-order term
   `a`, which reads the odometer covector rather than the smooth score's gradient.
8. **A deposit's move through its loci.** A deposit moves a locus, and each station `s` receives
   a logit move `δ_s` that mixes the covectors of every station the locus serves. For any move,
   `ℓ_t(f + δ) ≤ ℓ_t(f) + Σ_c r_c (δ_c − δ_t) + (K − 1) Σ_c r_c |δ_c − δ_t| + ½ (ln 2/2) Σ δ²`
   (`odometer_move_bound`, from `odometer_mismatch_le` and the two-sided mass bound
   `face_mass_le_odometer`), summed over the stations by `deposit_move_bound`. With
   `x_c = m_c − m_t`, the odometer's reading of a unit move is `a = A⁺ − A⁻` and what it can miss is
   `e = (K − 1)(A⁺ + A⁻)`, `A^± = Σ r_c max(±x_c, 0)` the right-way and wrong-way mass
   (`reading_split`). Under the code's rule `η C ≤ a` the score falls by at least `η (a/2 − e)`
   (`deposit_descends`), so the deposit descends when `(2K − 1) A⁻ < (3 − 2K) A⁺`
   (`deposit_condition_iff`); at `L = 16` it suffices that `9 A⁻ ≤ 5 A⁺`
   (`deposit_condition_sixteen`). No condition-free guarantee holds: a move whose wrong-way mass
   matches its right-way mass has `a` near zero while `e` is not. A coarser sufficient condition
   uses only the stations' target masses and a bound `B_s` on their moves:
   `e ≤ 2 Σ_s w_s (K_s − 1)(1 − r_s t_s) B_s` (`miss_le_target_mass`).
9. **The grain of a continuing machine** (owed item 4). The grain read from a reading count,
   `L(N) = ⌈√(N ln 2/2)⌉`, is the least meeting the criterion of item 6 (`refiningGrain_spec`); it
   is monotone, within one of `√(N ln 2/2)`, and at most doubles when the count quadruples
   (`refiningGrain_growth`). A grain refined by an integer factor determines the coarser read
   (`grainRead_of_refined`, `grainRead_refines`), so a dyadically refining machine keeps every
   read it made. At every count, same-cell media carry less than one bit over the readings
   (`refiningGrain_unconfirmable`).
10. **Campaign 1's numbers** (`resolution_aeon_bounds`, `declared_grain_vs_resolution`,
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
open Holonics.HNN.Ratio (codeLength two_rpow_eq_exp grainRead face_constant_on_fibre
  odometerWeight face_weight_le_odometer)
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

/-! ## 7. The odometer covector's pairing with the smooth score -/

section Pairing

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- [proved-derived; formal-checked] **The odometer covector reads at least `1/K` of its own
decrease.** With positive normalized masses `p` (the smooth face) and `r` (the odometer chart),
the one-hot target `q` at `t`, and `r_c ≤ K p_c` for every class, the smooth score's first-order
decrease along the odometer covector is at least `1/K` of the odometer's own:
`‖r − q‖²/K ≤ ⟨p − q, r − q⟩`. Off the target each `p_c r_c ≥ r_c²/K`; at the target
`1 − r_t = Σ_(c≠t) r_c ≤ K (1 − p_t)`. -/
theorem odometer_pairing_ratio (p r : ι → ℝ) (hr : ∀ c, 0 < r c) (hp1 : ∑ c, p c = 1)
    (hr1 : ∑ c, r c = 1) (t : ι) {K : ℝ} (hK : 0 < K) (hpr : ∀ c, r c ≤ K * p c) :
    (∑ c, (r c - (Pi.single t (1 : ℝ) : ι → ℝ) c) ^ 2) / K ≤
      ∑ c, (p c - (Pi.single t (1 : ℝ) : ι → ℝ) c) * (r c - (Pi.single t (1 : ℝ) : ι → ℝ) c) := by
  have hrt : 1 - r t = ∑ c ∈ Finset.univ.erase t, r c := by
    rw [← hr1, ← Finset.add_sum_erase _ _ (Finset.mem_univ t)]; ring
  have hpt : 1 - p t = ∑ c ∈ Finset.univ.erase t, p c := by
    rw [← hp1, ← Finset.add_sum_erase _ _ (Finset.mem_univ t)]; ring
  have hrest : ∑ c ∈ Finset.univ.erase t, r c ≤ K * ∑ c ∈ Finset.univ.erase t, p c := by
    rw [Finset.mul_sum]; exact Finset.sum_le_sum fun c _ => hpr c
  have hrt0 : 0 ≤ 1 - r t := by
    rw [hrt]; exact Finset.sum_nonneg fun c _ => (hr c).le
  have htgt : (r t - 1) ^ 2 ≤ K * ((p t - 1) * (r t - 1)) := by
    have h1 : 1 - r t ≤ K * (1 - p t) := by rw [hrt, hpt]; exact hrest
    nlinarith [mul_le_mul_of_nonneg_right h1 hrt0]
  have hoff : ∑ c ∈ Finset.univ.erase t, (r c - (Pi.single t (1 : ℝ) : ι → ℝ) c) ^ 2 ≤
      K * ∑ c ∈ Finset.univ.erase t,
        (p c - (Pi.single t (1 : ℝ) : ι → ℝ) c) * (r c - (Pi.single t (1 : ℝ) : ι → ℝ) c) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun c hc => ?_
    have hct : c ≠ t := (Finset.mem_erase.mp hc).1
    simp only [Pi.single_eq_of_ne hct, sub_zero]
    nlinarith [mul_le_mul_of_nonneg_right (hpr c) (hr c).le]
  rw [div_le_iff₀ hK, ← Finset.add_sum_erase _ _ (Finset.mem_univ t),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ t)]
  simp only [Pi.single_eq_same]
  nlinarith [hoff, htgt]

/-- [proved-standard; formal-checked] **The face's weight against the chord.**
`2^y ≥ (e ln 2/2)(1 + y)` for every `y`: the tangent to `2^y` at `y = 1/ln 2 − 1`, through
`e^z ≥ 1 + z`. -/
theorem two_rpow_ge_chord (y : ℝ) : Real.exp 1 * Real.log 2 / 2 * (1 + y) ≤ (2 : ℝ) ^ y := by
  rw [two_rpow_eq_exp]
  have h1 := Real.add_one_le_exp (y * Real.log 2 - 1 + Real.log 2)
  have h2 : Real.exp (y * Real.log 2 - 1 + Real.log 2) =
      Real.exp (y * Real.log 2) * 2 / Real.exp 1 := by
    rw [Real.exp_add, Real.exp_sub, Real.exp_log (by norm_num)]
    ring
  rw [h2, le_div_iff₀ (Real.exp_pos 1)] at h1
  nlinarith [h1]

/-- [proved-derived; formal-checked] **The odometer chart lies within `2/(e ln 2)` of the face's
weight.** `(e ln 2/2) · 2^n (1 + k/L) ≤ 2^(n + k/L)`; with `face_weight_le_odometer` the chart's
weight is pinned to the face's within the factor `2/(e ln 2) ∈ (1, 17/16)`, whatever `L`. -/
theorem odometer_le_face_weight (n : ℤ) (k L : ℕ) :
    Real.exp 1 * Real.log 2 / 2 * odometerWeight n k L ≤ (2 : ℝ) ^ ((n : ℝ) + (k : ℝ) / L) := by
  rw [Real.rpow_add (by norm_num), Real.rpow_intCast, odometerWeight]
  have h2 : (0 : ℝ) < (2 : ℝ) ^ n := zpow_pos (by norm_num) n
  calc Real.exp 1 * Real.log 2 / 2 * ((2 : ℝ) ^ n * (1 + (k : ℝ) / L)) =
        (2 : ℝ) ^ n * (Real.exp 1 * Real.log 2 / 2 * (1 + (k : ℝ) / L)) := by ring
    _ ≤ (2 : ℝ) ^ n * (2 : ℝ) ^ ((k : ℝ) / L) :=
        mul_le_mul_of_nonneg_left (two_rpow_ge_chord _) h2.le

omit [DecidableEq ι] in
/-- [proved-derived; formal-checked] **The odometer's masses against the face's.** With every
exponent `x_c` in its grain cell `[n_c + k_c/L, n_c + (k_c + 1)/L)`, `k_c ≤ L`, the odometer mass
`r_c = ω_c/Σ ω` and the face's mass `p_c = 2^(x_c)/Σ 2^x` obey
`r_c ≤ 2^(1/L) · (2/(e ln 2)) · p_c`. -/
theorem odometer_mass_le [Nonempty ι] (n : ι → ℤ) (k : ι → ℕ) {L : ℕ} (hL : 0 < L)
    (hk : ∀ c, k c ≤ L) (x : ι → ℝ) (hx0 : ∀ c, (n c : ℝ) + (k c : ℝ) / L ≤ x c)
    (hx1 : ∀ c, x c < (n c : ℝ) + (k c : ℝ) / L + 1 / L) (c : ι) :
    odometerWeight (n c) (k c) L / ∑ d, odometerWeight (n d) (k d) L ≤
      (2 : ℝ) ^ (1 / (L : ℝ)) / (Real.exp 1 * Real.log 2 / 2) *
        ((2 : ℝ) ^ x c / ∑ d, (2 : ℝ) ^ x d) := by
  have hμ : 0 < Real.exp 1 * Real.log 2 / 2 := by
    have := Real.log_pos (show (1 : ℝ) < 2 by norm_num); positivity
  have ha : (0 : ℝ) < (2 : ℝ) ^ (1 / (L : ℝ)) := by positivity
  have hω : ∀ d, 0 < odometerWeight (n d) (k d) L := fun d => by
    unfold odometerWeight; have := zpow_pos (show (0 : ℝ) < 2 by norm_num) (n d); positivity
  have hW : 0 < ∑ d, odometerWeight (n d) (k d) L :=
    Finset.sum_pos (fun d _ => hω d) Finset.univ_nonempty
  have hA : 0 < ∑ d, (2 : ℝ) ^ x d := Finset.sum_pos (fun d _ => by positivity) Finset.univ_nonempty
  -- the chart's weight at `c` is at most the face's weight over `μ`
  have hωc : odometerWeight (n c) (k c) L ≤ (2 : ℝ) ^ x c / (Real.exp 1 * Real.log 2 / 2) := by
    rw [le_div_iff₀ hμ, mul_comm]
    exact (odometer_le_face_weight (n c) (k c) L).trans
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) (hx0 c))
  -- the face's partition is at most `2^(1/L)` times the chart's
  have hAW : ∑ d, (2 : ℝ) ^ x d ≤ (2 : ℝ) ^ (1 / (L : ℝ)) * ∑ d, odometerWeight (n d) (k d) L := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun d _ => ?_
    calc (2 : ℝ) ^ x d ≤ (2 : ℝ) ^ (((n d : ℝ) + (k d : ℝ) / L) + 1 / L) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (hx1 d).le
      _ = (2 : ℝ) ^ ((n d : ℝ) + (k d : ℝ) / L) * (2 : ℝ) ^ (1 / (L : ℝ)) :=
          Real.rpow_add (by norm_num) _ _
      _ ≤ odometerWeight (n d) (k d) L * (2 : ℝ) ^ (1 / (L : ℝ)) :=
          mul_le_mul_of_nonneg_right (face_weight_le_odometer (n d) hL (hk d)) ha.le
      _ = _ := by ring
  rw [div_le_iff₀ hW]
  have h1 : 1 ≤ (2 : ℝ) ^ (1 / (L : ℝ)) * (∑ d, odometerWeight (n d) (k d) L) /
      ∑ d, (2 : ℝ) ^ x d := by
    rw [le_div_iff₀ hA]; linarith
  have hfx : 0 ≤ (2 : ℝ) ^ x c / (Real.exp 1 * Real.log 2 / 2) := by positivity
  calc odometerWeight (n c) (k c) L ≤ (2 : ℝ) ^ x c / (Real.exp 1 * Real.log 2 / 2) * 1 := by
        rw [mul_one]; exact hωc
    _ ≤ (2 : ℝ) ^ x c / (Real.exp 1 * Real.log 2 / 2) *
        ((2 : ℝ) ^ (1 / (L : ℝ)) * (∑ d, odometerWeight (n d) (k d) L) / ∑ d, (2 : ℝ) ^ x d) :=
        mul_le_mul_of_nonneg_left h1 hfx
    _ = _ := by ring

/-- [proved-derived; formal-checked] **The certified step's decrease under the odometer
covector.** Stepping the station logits along `−η (r − q)`, with the odometer masses `r` within
`r ≤ K p` of the smooth face `p`, the smooth score obeys
`ℓ_t(f − η g̃) ≤ ℓ_t(f) − η a/K + ½ (ln 2/2) η² a`, `a = ‖r − q‖²` the deposit's first-order
decrease read on the odometer covector. -/
theorem odometer_step_bound [Nonempty ι] (f r : ι → ℝ) (t : ι) (hr : ∀ c, 0 < r c)
    (hr1 : ∑ c, r c = 1) {K η : ℝ} (hK : 0 < K) (hη : 0 ≤ η)
    (hpr : ∀ c, r c ≤ K * (face fun c => f c * Real.log 2).mass c) :
    codeLength (fun c => f c - η * (r c - (Pi.single t (1 : ℝ) : ι → ℝ) c)) t ≤
      codeLength f t - η * ((∑ c, (r c - (Pi.single t (1 : ℝ) : ι → ℝ) c) ^ 2) / K) +
        1 / 2 * (Real.log 2 / 2) * η ^ 2 * ∑ c, (r c - (Pi.single t (1 : ℝ) : ι → ℝ) c) ^ 2 := by
  set p := face fun c => f c * Real.log 2 with hp
  have hq := codeLength_quadratic_upper f
    (fun c => -(η * (r c - (Pi.single t (1 : ℝ) : ι → ℝ) c))) t
  have e1 : (fun c => f c + -(η * (r c - (Pi.single t (1 : ℝ) : ι → ℝ) c))) =
      fun c => f c - η * (r c - (Pi.single t (1 : ℝ) : ι → ℝ) c) := by
    funext c; ring
  rw [e1] at hq
  have hpair := odometer_pairing_ratio p.mass r hr p.normalized hr1 t hK hpr
  have e2 : ∑ c, (p.mass c - if c = t then 1 else 0) *
        -(η * (r c - (Pi.single t (1 : ℝ) : ι → ℝ) c)) =
      -η * ∑ c, (p.mass c - (Pi.single t (1 : ℝ) : ι → ℝ) c) *
        (r c - (Pi.single t (1 : ℝ) : ι → ℝ) c) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [Pi.single_apply]
    ring
  have e3 : ∑ c, (-(η * (r c - (Pi.single t (1 : ℝ) : ι → ℝ) c))) ^ 2 =
      η ^ 2 * ∑ c, (r c - (Pi.single t (1 : ℝ) : ι → ℝ) c) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => by ring
  rw [e2, e3] at hq
  have := mul_le_mul_of_nonneg_left hpair hη
  nlinarith [this, hq]

/-- [proved-derived; formal-checked] **What the certificate guarantees.** Under the code's step
rule `η · s · a ≤ a` with `s ≥ ln 2/2`, the smooth score falls by at least `η a (1/K − ½)`, not
the `½ η a` the deposit reads; with the rule tightened to `η (ln 2/2) a ≤ a/K` it falls by at
least `½ η a/K`. The certified decrease `½ η a` is therefore owed exactly the factor `1/K`. The
model `hmodel` is `odometer_step_bound`'s, a logit step along the odometer covector. -/
theorem odometer_certified_decrease {φ φ₀ a η s K : ℝ} (hη : 0 ≤ η) (ha : 0 ≤ a)
    (hs : Real.log 2 / 2 ≤ s)
    (hmodel : φ ≤ φ₀ - η * (a / K) + 1 / 2 * (Real.log 2 / 2) * η ^ 2 * a) :
    (η * s * a ≤ a → φ ≤ φ₀ - η * a * (1 / K - 1 / 2)) ∧
      (η * (Real.log 2 / 2) * a ≤ a / K → φ ≤ φ₀ - 1 / 2 * η * (a / K)) := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  constructor
  · intro hstep
    have h1 : η * (Real.log 2 / 2) * a ≤ η * s * a := by
      have : 0 ≤ η * a := mul_nonneg hη ha
      nlinarith
    have h2 : 1 / 2 * (Real.log 2 / 2) * η ^ 2 * a ≤ 1 / 2 * η * a := by
      have := mul_le_mul_of_nonneg_left (h1.trans hstep) hη
      nlinarith
    have e : η * a * (1 / K - 1 / 2) = η * (a / K) - 1 / 2 * η * a := by ring
    rw [e]; linarith
  · intro hstep
    have := mul_le_mul_of_nonneg_left hstep hη
    nlinarith

/-- [proved-derived; formal-checked] **At the declared grain `L = 16` the odometer pairing keeps
seven eighths.** `K = 2^(1/16) · 2/(e ln 2) < 8/7`, so under the code's rule the smooth score falls
by at least `3/8 · η a`. -/
theorem odometer_ratio_sixteen :
    (2 : ℝ) ^ (1 / (16 : ℝ)) / (Real.exp 1 * Real.log 2 / 2) < 8 / 7 ∧
      3 / 8 < 1 / ((2 : ℝ) ^ (1 / (16 : ℝ)) / (Real.exp 1 * Real.log 2 / 2)) - 1 / 2 := by
  have he := Real.exp_one_gt_d9
  have hl := Real.log_two_gt_d9
  have hμ : (119 : ℝ) / 128 < Real.exp 1 * Real.log 2 / 2 := by nlinarith
  have hμ0 : 0 < Real.exp 1 * Real.log 2 / 2 := by linarith
  have hb : (2 : ℝ) ^ (1 / (16 : ℝ)) ≤ 17 / 16 := by
    have := rpow_one_add_le_one_add_mul_self (s := 1) (by norm_num)
      (show (0 : ℝ) ≤ 1 / 16 by norm_num) (show (1 : ℝ) / 16 ≤ 1 by norm_num)
    norm_num at this ⊢
    linarith
  have hb0 : (0 : ℝ) < (2 : ℝ) ^ (1 / (16 : ℝ)) := by positivity
  have hK : (2 : ℝ) ^ (1 / (16 : ℝ)) / (Real.exp 1 * Real.log 2 / 2) < 8 / 7 := by
    rw [div_lt_iff₀ hμ0]; linarith
  refine ⟨hK, ?_⟩
  have hK0 : 0 < (2 : ℝ) ^ (1 / (16 : ℝ)) / (Real.exp 1 * Real.log 2 / 2) := by positivity
  have : (7 : ℝ) / 8 < 1 / ((2 : ℝ) ^ (1 / (16 : ℝ)) / (Real.exp 1 * Real.log 2 / 2)) := by
    rw [lt_div_iff₀ hK0]; linarith
  linarith

end Pairing

/-! ## 8. A deposit's move through its loci -/

section Deposit

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- [proved-derived; formal-checked] **The face's masses against the odometer's.** With every
exponent in its grain cell, `p_c ≤ 2^(1/L) · (2/(e ln 2)) · r_c`: with `odometer_mass_le` the two
masses lie within the one factor `K = 2^(1/L) · 2/(e ln 2)` of each other, in both directions. -/
theorem face_mass_le_odometer [Nonempty ι] (n : ι → ℤ) (k : ι → ℕ) {L : ℕ} (hL : 0 < L)
    (hk : ∀ c, k c ≤ L) (x : ι → ℝ) (hx0 : ∀ c, (n c : ℝ) + (k c : ℝ) / L ≤ x c)
    (hx1 : ∀ c, x c < (n c : ℝ) + (k c : ℝ) / L + 1 / L) (c : ι) :
    (2 : ℝ) ^ x c / ∑ d, (2 : ℝ) ^ x d ≤
      (2 : ℝ) ^ (1 / (L : ℝ)) / (Real.exp 1 * Real.log 2 / 2) *
        (odometerWeight (n c) (k c) L / ∑ d, odometerWeight (n d) (k d) L) := by
  have hμ : 0 < Real.exp 1 * Real.log 2 / 2 := by
    have := Real.log_pos (show (1 : ℝ) < 2 by norm_num); positivity
  have ha : (0 : ℝ) < (2 : ℝ) ^ (1 / (L : ℝ)) := by positivity
  have hω : ∀ d, 0 < odometerWeight (n d) (k d) L := fun d => by
    unfold odometerWeight; have := zpow_pos (show (0 : ℝ) < 2 by norm_num) (n d); positivity
  have hW : 0 < ∑ d, odometerWeight (n d) (k d) L :=
    Finset.sum_pos (fun d _ => hω d) Finset.univ_nonempty
  have hA : 0 < ∑ d, (2 : ℝ) ^ x d := Finset.sum_pos (fun d _ => by positivity) Finset.univ_nonempty
  -- the face's weight at `c` is at most `2^(1/L)` times the chart's
  have hxc : (2 : ℝ) ^ x c ≤ (2 : ℝ) ^ (1 / (L : ℝ)) * odometerWeight (n c) (k c) L := by
    calc (2 : ℝ) ^ x c ≤ (2 : ℝ) ^ (((n c : ℝ) + (k c : ℝ) / L) + 1 / L) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (hx1 c).le
      _ = (2 : ℝ) ^ ((n c : ℝ) + (k c : ℝ) / L) * (2 : ℝ) ^ (1 / (L : ℝ)) :=
          Real.rpow_add (by norm_num) _ _
      _ ≤ odometerWeight (n c) (k c) L * (2 : ℝ) ^ (1 / (L : ℝ)) :=
          mul_le_mul_of_nonneg_right (face_weight_le_odometer (n c) hL (hk c)) ha.le
      _ = _ := by ring
  -- the chart's partition is at most the face's over `μ`
  have hWA : Real.exp 1 * Real.log 2 / 2 * ∑ d, odometerWeight (n d) (k d) L ≤
      ∑ d, (2 : ℝ) ^ x d := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun d _ => (odometer_le_face_weight (n d) (k d) L).trans
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) (hx0 d))
  rw [div_le_iff₀ hA]
  calc (2 : ℝ) ^ x c ≤ (2 : ℝ) ^ (1 / (L : ℝ)) * odometerWeight (n c) (k c) L := hxc
    _ = (2 : ℝ) ^ (1 / (L : ℝ)) / (Real.exp 1 * Real.log 2 / 2) *
          (odometerWeight (n c) (k c) L / ∑ d, odometerWeight (n d) (k d) L) *
          (Real.exp 1 * Real.log 2 / 2 * ∑ d, odometerWeight (n d) (k d) L) := by
        field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hWA
        (mul_nonneg (div_nonneg ha.le hμ.le) (div_nonneg (hω c).le hW.le))

/-- [proved-derived; formal-checked] **A covector read against its target.** For normalized
masses `w` and the one-hot target at `t`, `⟨w − e_t, m⟩ = Σ_c w_c (m_c − m_t)`: only the moves
relative to the target's are read. -/
theorem reading_relative (w m : ι → ℝ) (hw1 : ∑ c, w c = 1) (t : ι) :
    ∑ c, (w c - (Pi.single t (1 : ℝ) : ι → ℝ) c) * m c = ∑ c, w c * (m c - m t) := by
  have h1 : ∑ c, (Pi.single t (1 : ℝ) : ι → ℝ) c * m c = m t := by
    simp [Pi.single_apply]
  have h2 : ∑ c, w c * m t = m t := by rw [← Finset.sum_mul, hw1, one_mul]
  simp only [sub_mul, mul_sub, Finset.sum_sub_distrib, h1, h2]

omit [DecidableEq ι] in
/-- [proved-derived; formal-checked] **What the odometer misreads of any move.** With normalized
masses within `K ≥ 1` of each other in both directions (`r ≤ K p`, `p ≤ K r`), the smooth face
and the odometer read any move `m` within `(K − 1) Σ_c r_c |m_c − m_t|`, for any class `t`. -/
theorem odometer_mismatch_le (p r m : ι → ℝ) (hp1 : ∑ c, p c = 1) (hr1 : ∑ c, r c = 1)
    (hr : ∀ c, 0 ≤ r c) (t : ι) {K : ℝ} (hK : 1 ≤ K) (hpr : ∀ c, r c ≤ K * p c)
    (hrp : ∀ c, p c ≤ K * r c) :
    |∑ c, (p c - r c) * m c| ≤ (K - 1) * ∑ c, r c * |m c - m t| := by
  have e : ∑ c, (p c - r c) * m c = ∑ c, (p c - r c) * (m c - m t) := by
    have h0 : ∑ c, (p c - r c) * m t = 0 := by
      rw [← Finset.sum_mul, Finset.sum_sub_distrib, hp1, hr1]; ring
    rw [← sub_zero (∑ c, (p c - r c) * m c), ← h0, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun c _ => by ring
  have hdiff : ∀ c, |p c - r c| ≤ (K - 1) * r c := by
    intro c
    rw [abs_le]
    constructor
    · have h : K * 0 ≤ K * (p c + (K - 2) * r c) := by
        nlinarith [hpr c, mul_nonneg (sq_nonneg (K - 1)) (hr c)]
      have := le_of_mul_le_mul_left h (by linarith)
      linarith
    · linarith [hrp c]
  rw [e, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun c _ => ?_)
  rw [abs_mul, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hdiff c) (abs_nonneg _)

/-- [proved-derived; formal-checked] **One station under any move.** For any move `δ` of a
station's logits, with the odometer masses `r` and the smooth face within `K ≥ 1` of each other,
the base-two score obeys
`ℓ_t(f + δ) ≤ ℓ_t(f) + Σ_c r_c (δ_c − δ_t) + (K − 1) Σ_c r_c |δ_c − δ_t| + ½ (ln 2/2) Σ δ²`.
The first sum is the odometer covector's reading `⟨r − e_t, δ⟩`; the second is what that reading
can miss. -/
theorem odometer_move_bound [Nonempty ι] (f r δ : ι → ℝ) (t : ι) (hr : ∀ c, 0 ≤ r c)
    (hr1 : ∑ c, r c = 1) {K : ℝ} (hK : 1 ≤ K)
    (hpr : ∀ c, r c ≤ K * (face fun c => f c * Real.log 2).mass c)
    (hrp : ∀ c, (face fun c => f c * Real.log 2).mass c ≤ K * r c) :
    codeLength (fun c => f c + δ c) t ≤ codeLength f t + ∑ c, r c * (δ c - δ t) +
      (K - 1) * ∑ c, r c * |δ c - δ t| + 1 / 2 * (Real.log 2 / 2) * ∑ c, δ c ^ 2 := by
  set p := face fun c => f c * Real.log 2 with hp
  have hq := codeLength_quadratic_upper f δ t
  have e1 : ∑ c, (p.mass c - if c = t then 1 else 0) * δ c =
      ∑ c, p.mass c * (δ c - δ t) := by
    rw [← reading_relative p.mass δ p.normalized t]
    exact Finset.sum_congr rfl fun c _ => by simp [Pi.single_apply]
  have e2 : ∑ c, p.mass c * (δ c - δ t) =
      ∑ c, r c * (δ c - δ t) + ∑ c, (p.mass c - r c) * δ c := by
    rw [← reading_relative p.mass δ p.normalized t, ← reading_relative r δ hr1 t,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun c _ => by ring
  have hm := odometer_mismatch_le p.mass r δ p.normalized hr1 hr t hK hpr hrp
  have := le_abs_self (∑ c, (p.mass c - r c) * δ c)
  rw [e1, e2] at hq
  linarith

/-- [proved-derived; formal-checked] **The deposit as it happens: every station at once.** A
deposit moves its loci, and through the reach each station `s` (weight `w_s ≥ 0`, target `t_s`,
odometer masses `r_s` within `K_s` of its face) receives a logit move `δ_s`, which mixes the
covectors of every station the locus serves. The weighted score obeys the sum of the stations'
bounds: the odometer's reading `Σ_s w_s Σ_c r_sc (δ_sc − δ_s t_s)`, what it can miss
`Σ_s w_s (K_s − 1) Σ_c r_sc |δ_sc − δ_s t_s|`, and the curvature `½ (ln 2/2) Σ_s w_s ‖δ_s‖²`. -/
theorem deposit_move_bound [Nonempty ι] {σ : Type*} [Fintype σ] (w : σ → ℝ)
    (hw : ∀ s, 0 ≤ w s) (f r δ : σ → ι → ℝ) (t : σ → ι) (hr : ∀ s c, 0 ≤ r s c)
    (hr1 : ∀ s, ∑ c, r s c = 1) (K : σ → ℝ) (hK : ∀ s, 1 ≤ K s)
    (hpr : ∀ s c, r s c ≤ K s * (face fun c => f s c * Real.log 2).mass c)
    (hrp : ∀ s c, (face fun c => f s c * Real.log 2).mass c ≤ K s * r s c) :
    ∑ s, w s * codeLength (fun c => f s c + δ s c) (t s) ≤
      ∑ s, w s * (codeLength (f s) (t s) + ∑ c, r s c * (δ s c - δ s (t s)) +
        (K s - 1) * ∑ c, r s c * |δ s c - δ s (t s)| +
          1 / 2 * (Real.log 2 / 2) * ∑ c, δ s c ^ 2) :=
  Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left
    (odometer_move_bound (f s) (r s) (δ s) (t s) (hr s) (hr1 s) (hK s) (hpr s) (hrp s)) (hw s)

omit [DecidableEq ι] in
/-- [proved-derived; formal-checked] **The reading splits into its right-way and wrong-way
parts.** With `x_c = m_c − m_t` the move of class `c` against the target, `A⁺ = Σ r_c max(x_c, 0)`
and `A⁻ = Σ r_c max(−x_c, 0)`: the odometer's reading is `A⁺ − A⁻` and what it can miss is
`(K − 1)(A⁺ + A⁻)`. -/
theorem reading_split (r x : ι → ℝ) :
    ∑ c, r c * x c = ∑ c, r c * max (x c) 0 - ∑ c, r c * max (-x c) 0 ∧
      ∑ c, r c * |x c| = ∑ c, r c * max (x c) 0 + ∑ c, r c * max (-x c) 0 := by
  have h : ∀ c, x c = max (x c) 0 - max (-x c) 0 ∧ |x c| = max (x c) 0 + max (-x c) 0 := by
    intro c
    rcases le_total 0 (x c) with h | h
    · simp [max_eq_left h, max_eq_right (neg_nonpos.mpr h), abs_of_nonneg h]
    · simp [max_eq_right h, max_eq_left (neg_nonneg.mpr h), abs_of_nonpos h]
  constructor
  · rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    conv_lhs => rw [(h c).1]
    ring
  · rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    conv_lhs => rw [(h c).2]
    ring

/-- [proved-derived; formal-checked] **When the code's step descends.** Let the deposit's
model be `φ(η) ≤ φ(0) − η a + η e + ½ η² C`, with `a` the odometer's reading of the unit move,
`e` what it can miss, and `C ≥ (ln 2/2) Σ w ‖δ‖²/η²` the curvature the certificate bounds. The
code's rule `η C ≤ a` gives `φ(η) ≤ φ(0) − η (a/2 − e)`: the deposit descends, by at least that,
when `e < a/2`. -/
theorem deposit_descends {φ φ₀ a e C η : ℝ} (hη : 0 ≤ η)
    (hmodel : φ ≤ φ₀ - η * a + η * e + 1 / 2 * η ^ 2 * C) (hstep : η * C ≤ a) :
    φ ≤ φ₀ - η * (a / 2 - e) := by
  have : 1 / 2 * η ^ 2 * C ≤ 1 / 2 * η * a := by
    have := mul_le_mul_of_nonneg_left hstep hη
    nlinarith
  nlinarith

/-- [proved-derived; formal-checked] **The condition, in the wrong-way mass.** With
`a = A⁺ − A⁻` and `e = (K − 1)(A⁺ + A⁻)` (`reading_split`, summed over the stations with one
`K`), `e < a/2` exactly when `(2K − 1) A⁻ < (3 − 2K) A⁺`. -/
theorem deposit_condition_iff {Ap Am K : ℝ} :
    (K - 1) * (Ap + Am) < (Ap - Am) / 2 ↔ (2 * K - 1) * Am < (3 - 2 * K) * Ap := by
  constructor <;> intro h <;> linarith

/-- [proved-derived; formal-checked] **At the declared grain `L = 16`.** `K < 8/7`, so the code's
step descends whenever the wrong-way mass is below five ninths of the right-way mass,
`9 A⁻ ≤ 5 A⁺` with `A⁺ > 0`. A covector step at one station has `A⁻ = 0`
(`odometer_certified_decrease` is the sharper bound there). -/
theorem deposit_condition_sixteen {Ap Am K : ℝ} (hK1 : 1 ≤ K) (hK : K < 8 / 7)
    (hAp : 0 < Ap) (h : 9 * Am ≤ 5 * Ap) : (K - 1) * (Ap + Am) < (Ap - Am) / 2 := by
  rw [deposit_condition_iff]
  nlinarith

/-- [proved-derived; formal-checked] **A sufficient condition from what the deposit already
reads.** With every move within `B` of zero, what the reading can miss at a station is at most
`2 B (1 − r_t)`: so `e ≤ 2 Σ_s w_s (K_s − 1)(1 − r_s t_s) B_s`, from the stations' target masses
and a bound on their moves, both of which the deposit's certificate already carries. -/
theorem miss_le_target_mass (r m : ι → ℝ) (hr : ∀ c, 0 ≤ r c) (hr1 : ∑ c, r c = 1) (t : ι)
    {B : ℝ} (hB : ∀ c, |m c| ≤ B) :
    ∑ c, r c * |m c - m t| ≤ 2 * B * (1 - r t) := by
  have hrt : 1 - r t = ∑ c ∈ Finset.univ.erase t, r c := by
    rw [← hr1, ← Finset.add_sum_erase _ _ (Finset.mem_univ t)]; ring
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ t), sub_self, abs_zero, mul_zero, zero_add,
    hrt, Finset.mul_sum]
  refine Finset.sum_le_sum fun c _ => ?_
  have : |m c - m t| ≤ 2 * B := by
    calc |m c - m t| ≤ |m c| + |m t| := abs_sub _ _
      _ ≤ 2 * B := by linarith [hB c, hB t]
  nlinarith [hr c]

end Deposit

/-! ## 9. The grain of a continuing machine -/

section Refining

/-- [definition] **The grain read from a reading count**: the least `L` with `2L² ≥ N ln 2`,
`L(N) = ⌈√(N ln 2/2)⌉`. -/
noncomputable def refiningGrain (N : ℕ) : ℕ := ⌈Real.sqrt (N * Real.log 2 / 2)⌉₊

/-- [proved-derived; formal-checked] **The read grain meets the criterion, and is the least that
does.** `N ln 2 ≤ 2 L(N)²`, and every `L < L(N)` has `2L² < N ln 2`. -/
theorem refiningGrain_spec (N : ℕ) :
    (N : ℝ) * Real.log 2 ≤ 2 * (refiningGrain N : ℝ) ^ 2 ∧
      ∀ L : ℕ, L < refiningGrain N → 2 * (L : ℝ) ^ 2 < N * Real.log 2 := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hx : 0 ≤ (N : ℝ) * Real.log 2 / 2 := by positivity
  constructor
  · have h := Nat.le_ceil (Real.sqrt ((N : ℝ) * Real.log 2 / 2))
    have hsq : Real.sqrt ((N : ℝ) * Real.log 2 / 2) ^ 2 ≤ (refiningGrain N : ℝ) ^ 2 :=
      pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
    rw [Real.sq_sqrt hx] at hsq
    linarith
  · intro L hL
    have h : (L : ℝ) < Real.sqrt ((N : ℝ) * Real.log 2 / 2) := Nat.lt_ceil.mp hL
    have hsq : (L : ℝ) ^ 2 < Real.sqrt ((N : ℝ) * Real.log 2 / 2) ^ 2 :=
      pow_lt_pow_left₀ h (Nat.cast_nonneg _) two_ne_zero
    rw [Real.sq_sqrt hx] at hsq
    linarith

/-- [proved-derived; formal-checked] **The grain refines as the count grows, as `√N`.** `L(N)` is
monotone, lies within one of `√(N ln 2/2)`, and quadrupling the count at most doubles it. A
moment with fewer remaining readings needs a coarser grain, so a grain read from the whole count
covers every later moment. -/
theorem refiningGrain_growth (N M : ℕ) (h : N ≤ M) :
    refiningGrain N ≤ refiningGrain M ∧
      (refiningGrain N : ℝ) < Real.sqrt (N * Real.log 2 / 2) + 1 ∧
      refiningGrain (4 * N) ≤ 2 * refiningGrain N := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · unfold refiningGrain
    refine Nat.ceil_mono (Real.sqrt_le_sqrt ?_)
    have : (N : ℝ) ≤ M := by exact_mod_cast h
    have := mul_le_mul_of_nonneg_right this hl.le
    linarith
  · exact Nat.ceil_lt_add_one (Real.sqrt_nonneg _)
  · unfold refiningGrain
    rw [Nat.ceil_le]
    have e : Real.sqrt (((4 * N : ℕ) : ℝ) * Real.log 2 / 2) =
        2 * Real.sqrt ((N : ℝ) * Real.log 2 / 2) := by
      rw [show (((4 * N : ℕ) : ℝ) * Real.log 2 / 2) = 2 ^ 2 * ((N : ℝ) * Real.log 2 / 2) by
        push_cast; ring]
      rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
    rw [e]
    push_cast
    linarith [Nat.le_ceil (Real.sqrt ((N : ℝ) * Real.log 2 / 2))]

/-- [proved-derived; formal-checked] **A finer grain determines the coarser read.** Refining by an
integer factor `m`, the read at `m L` determines the read at `L`:
`grainRead L f = (n, ⌊k′/m⌋)` with `(n, k′) = grainRead (m L) f`. So a machine whose grain
refines by integer factors (dyadically, `L = 2^j`) re-bases each lattice onto the finer one
without losing a read it already made. -/
theorem grainRead_of_refined {m : ℕ} (hm : 0 < m) (L : ℕ) (f : ℝ) :
    grainRead L f = ((grainRead (m * L) f).1, (grainRead (m * L) f).2 / (m : ℤ)) := by
  refine Prod.ext rfl ?_
  show ⌊(L : ℝ) * Int.fract f⌋ = ⌊((m * L : ℕ) : ℝ) * Int.fract f⌋ / (m : ℤ)
  rw [← Int.floor_div_natCast]
  congr 1
  have : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  push_cast
  field_simp

/-- [proved-derived; formal-checked] **Same fine cell, same coarse cell.** -/
theorem grainRead_refines {m : ℕ} (hm : 0 < m) (L : ℕ) {f f' : ℝ}
    (h : grainRead (m * L) f = grainRead (m * L) f') : grainRead L f = grainRead L f' := by
  rw [grainRead_of_refined hm L f, grainRead_of_refined hm L f', h]

/-- [proved-derived; formal-checked] **The continuing machine's grain hides nothing it could
confirm.** At reading count `N > 0` with grain `L(N)`, any two media in the same cell for every
class, over the `N` independent readings, carry less than one bit. -/
theorem refiningGrain_unconfirmable {ι ρ : Type*} [Fintype ι] [Nonempty ι] [Fintype ρ]
    [DecidableEq ρ] (hρ : 0 < Fintype.card ρ) (v v' : ρ → ι → ℝ)
    (hcell : ∀ r c, grainRead (refiningGrain (Fintype.card ρ)) (v' r c) =
      grainRead (refiningGrain (Fintype.card ρ)) (v r c)) :
    (joint fun r => face fun i => v r i * Real.log 2).klDivergence
        (joint fun r => face fun i => v' r i * Real.log 2) / Real.log 2 < 1 := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL : 0 < refiningGrain (Fintype.card ρ) := by
    unfold refiningGrain
    rw [Nat.ceil_pos]
    apply Real.sqrt_pos.mpr
    have : (0 : ℝ) < Fintype.card ρ := by exact_mod_cast hρ
    positivity
  exact grain_unconfirmable hL hρ (refiningGrain_spec _).1 v v' hcell

end Refining

/-! ## 10. Campaign 1's numbers -/

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
#print axioms odometer_pairing_ratio
#print axioms two_rpow_ge_chord
#print axioms odometer_le_face_weight
#print axioms odometer_mass_le
#print axioms odometer_step_bound
#print axioms odometer_certified_decrease
#print axioms odometer_ratio_sixteen
#print axioms face_mass_le_odometer
#print axioms reading_relative
#print axioms odometer_mismatch_le
#print axioms odometer_move_bound
#print axioms deposit_move_bound
#print axioms reading_split
#print axioms deposit_descends
#print axioms deposit_condition_iff
#print axioms deposit_condition_sixteen
#print axioms miss_le_target_mass
#print axioms refiningGrain_spec
#print axioms refiningGrain_growth
#print axioms grainRead_of_refined
#print axioms grainRead_refines
#print axioms refiningGrain_unconfirmable

end Audit

end Holonics.HNN.Ratio.Resolution
