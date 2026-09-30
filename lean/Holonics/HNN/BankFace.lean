import Holonics.HNN.FloquetPassage
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# HNN.BankFace: the receiving bank's learning path, the covector of the lock's decision

[definition] The receiving bank (`HNN/FloquetPassage`, the Rust owner `hnn::ring::ReceivingBank`)
decides a station by the lock's flip on the executed growth of every candidate's passage. Its
learning path reads the same lock at a declared temperature: the station's candidates are the
sheets of one lock, candidate `x` weighing the bank's second-order reading `A(x)`, and the station's
face is the exchange face `θ_x = A(x)/Σ_y A(y)` (`Objects/ParametronLock`: for two sheets
`θ = a/(a + K)`). The declared comparison with the target class `t` has the loss
`ℓ = log θ_t⁻¹ = log Σ_y A(y) − log A(t)`, the logarithm of the ratio of the target to the produced
face, and its covector on each log-reading is `θ_x − q_x` (the Rust owner
`hnn::prediction::stage_bank`, module header "The bank's learning path").

1. **The face's covector.** [proved-derived; formal-checked] Along any move `δ` of the
   log-readings, `d/dε (log Σ_y A_y e^(ε δ_y) − log(A_t e^(ε δ_t))) = Σ_y θ_y δ_y − δ_t`
   (`bank_face_covector`): the covector is `θ − q`, the lock's `dθ = θ(1 − θ) d ln a` read on every
   candidate (`Objects/ParametronLock.bias_susceptibility` is its two-sheet case).
2. **The reading is quadratic along a ray.** [proved-derived; formal-checked] A member's
   resonance amplitude is linear in the placed amplitudes, so along `W + ηV` the power is
   `|W|² + 2η Re(W̄V) + η²|V|²` (`member_amplitude_ray`), and a unit-carrier resonance over `d`
   crossings reads at most `d` times the passage's energy (`resonance_gain`): the gain
   `κ² = 2d Σ_m p_m²` of the chart (`hnn::ring::BankChart::gain`).
3. **The score's endpoint bound.** [proved-derived; formal-checked] `log(1 + u) ≥ u − 2u²` for
   `u ≥ −1/2` (`log_one_add_ge`); so a station's score moves along a ray by at most
   `(A(η) − A₀)/A₀ − (a(η) − a₀)/a₀ + 2((a(η) − a₀)/a₀)²` wherever `a(η) ≥ a₀/2`
   (`bank_score_endpoint`), and with `a₁² ≤ 4a₀a₂`, `a₂ ≤ â₂` and `η²â₂ ≤ a₀/16` the last term is
   at most `(81/8) η² â₂/a₀` and `a(η) ≥ a₀/2` holds (`bank_score_trust`). This is the quadratic
   reading's second order in the certified step: `C = Σ (2Â₂/A₀ + (81/4) â₂/a₀)`, the trust scale
   `ηc ≤ 1` with `c² = 16 â₂/a₀` (`hnn::constitution::BankReach::curvature`). The returns carry
   each reading's covector at a dyadic face within `e`; the true first-order decrease is at least
   their alignment less `e Σ_x |A′_x| ≤ 2e √(A₀ Â₂)` (`rounded_alignment`, `sum_sqrt_mul_le`).
4. **The joint certificate with a score beside the logits.** [proved-derived; formal-checked] A
   readout's score within `−A_r + ½J` and the bank's within `−a_b + ½Q_b` descend together by half
   their decrease when `J + Q_b ≤ A_r + a_b` (`joint_descends_beside`;
   `holon::deposition::JointReading::beside`).
5. **Where the executed law departs from the kicked chart.** [proved-derived; formal-checked] The
   node plane's reflection `F = R(1)` conjugates a pump's reflection to its conjugate carrier's,
   `F R(c) F = R(c̄)` (`flip_reflection`), and the kicked chart's transport to the conjugate turn,
   `F Rot(v) F = Rot(v̄)` (`flip_rotation`). The executed tick is `A ⊗ 1 + p B ⊗ R(c)`: its
   transport acts on the phase plane `(u, w)`, not on the node plane, so `1 ⊗ F` maps the passage
   `c` to `c̄` with the transport unchanged, and the executed growth reads a passage and its
   conjugate alike (the Rust test `the_executed_turn_reads_a_passage_and_its_conjugate_alike`). In
   the kicked chart `Rot_v (1 + p R_u)` the conjugate passage needs the conjugate transport, so it
   reads one sideband. The executed second order's pair terms are `Re(c_t c̄_s) Re(β ζ^(t−s))`, which
   read the resonance and its mirror equally,
   `Σ_(t,s) Re(c_t c̄_s) Re(β ζ^t conj ζ^s) = ½ Re β (|Σ_t c_t ζ^t|² + |Σ_t c_t ζ̄^t|²)`
   (`sideband_pair_sum`): the bank's face reads both (`hnn::ring::BankChart`, `W⁺` and `W⁻`).

[open] (#62) The executed law's full second order (its self term `p²|c|²` and the member's own
frequency, `|Σ_t c_t|²`, which past the standing bifurcation boosts), and the ordering of
candidates by the executed growth against their ordering by the face past the perturbative regime.

No `sorry`, no `axiom`, no `native_decide`; the audit block at the end prints the axioms.
-/

noncomputable section

namespace Holonics.HNN.BankFace

open Matrix
open Holonics.HNN.Floquet
open Holonics.HNN.FloquetPassage
open scoped BigOperators

/-! ## 1. The face's covector -/

/-- [proved-derived; formal-checked] **The face's covector is `θ − q`.** For positive readings
`A`, the loss `log Σ_y A_y e^(ε δ_y) − log(A_t e^(ε δ_t))` along a move `δ` of the log-readings has
the derivative `Σ_y θ_y δ_y − δ_t` at `ε = 0`, `θ_y = A_y / Σ A`. -/
theorem bank_face_covector {ι : Type*} (s : Finset ι) (A δ : ι → ℝ) (hA : ∀ y ∈ s, 0 < A y)
    {t : ι} (ht : t ∈ s) :
    HasDerivAt
      (fun ε : ℝ => Real.log (∑ y ∈ s, A y * Real.exp (ε * δ y)) -
        (Real.log (A t) + ε * δ t))
      ((∑ y ∈ s, A y * δ y) / (∑ y ∈ s, A y) - δ t) 0 := by
  have hsum : HasDerivAt (fun ε : ℝ => ∑ y ∈ s, A y * Real.exp (ε * δ y))
      (∑ y ∈ s, A y * δ y) 0 :=
    HasDerivAt.fun_sum (u := s) (A := fun y ε => A y * Real.exp (ε * δ y))
      (A' := fun y => A y * δ y) fun y _ => by
        simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (δ y)).exp.const_mul (A y)
  have h0 : (∑ y ∈ s, A y * Real.exp ((0 : ℝ) * δ y)) = ∑ y ∈ s, A y := by simp
  have hpos : (∑ y ∈ s, A y * Real.exp ((0 : ℝ) * δ y)) ≠ 0 := by
    rw [h0]
    exact (Finset.sum_pos hA ⟨t, ht⟩).ne'
  have hlog := hsum.log hpos
  rw [h0] at hlog
  have hlin : HasDerivAt (fun ε : ℝ => Real.log (A t) + ε * δ t) (δ t) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (δ t)).const_add (Real.log (A t))
  exact hlog.sub hlin

/-! ## 2. The reading along a ray -/

/-- [proved-derived; formal-checked] **A member's power is quadratic along a ray** of its
resonance amplitude: `|W + ηV|² = |W|² + 2η Re(W̄V) + η²|V|²`; its second order is the power of the
move. -/
theorem member_amplitude_ray (W V : ℂ) (η : ℝ) :
    Complex.normSq (W + η * V) =
      Complex.normSq W + 2 * η * (star W * V).re + η ^ 2 * Complex.normSq V := by
  rw [Complex.normSq_add]
  simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

/-- [proved-derived; formal-checked] **A unit-carrier resonance reads at most `d` times the
passage's energy**: `|Σ_(t<d) ω_t z_t|² ≤ d Σ_(t<d) |z_t|²` for `|ω_t| = 1` (the triangle
inequality, then Cauchy–Schwarz over the turn). -/
theorem resonance_gain (d : ℕ) (ω z : ℕ → ℂ) (hω : ∀ t, ‖ω t‖ = 1) :
    ‖∑ t ∈ Finset.range d, ω t * z t‖ ^ 2 ≤ d * ∑ t ∈ Finset.range d, ‖z t‖ ^ 2 := by
  have htri : ‖∑ t ∈ Finset.range d, ω t * z t‖ ≤ ∑ t ∈ Finset.range d, ‖z t‖ := by
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [norm_mul, hω t, one_mul]
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range d) (f := fun t => ‖z t‖)
  simp only [Finset.card_range] at hcs
  calc ‖∑ t ∈ Finset.range d, ω t * z t‖ ^ 2 ≤ (∑ t ∈ Finset.range d, ‖z t‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) htri 2
    _ ≤ d * ∑ t ∈ Finset.range d, ‖z t‖ ^ 2 := hcs

/-! ## 3. The score's endpoint bound -/

/-- [proved-derived; formal-checked] `log(1 + u) ≥ u − 2u²` for `u ≥ −1/2`: from
`log x ≥ 1 − 1/x`, `u/(1 + u) − (u − 2u²) = u²(1 + 2u)/(1 + u) ≥ 0`. -/
theorem log_one_add_ge {u : ℝ} (hu : -1 / 2 ≤ u) : u - 2 * u ^ 2 ≤ Real.log (1 + u) := by
  have hpos : 0 < 1 + u := by linarith
  have hlog := Real.one_sub_inv_le_log_of_pos hpos
  have hfrac : u - 2 * u ^ 2 ≤ 1 - (1 + u)⁻¹ := by
    rw [show (1 : ℝ) - (1 + u)⁻¹ = u / (1 + u) by field_simp; ring]
    rw [le_div_iff₀ hpos]
    nlinarith [sq_nonneg u]
  linarith

/-- [proved-derived; formal-checked] **A station's score moves by at most its linear change plus
the target's second-order term**: with the normalizer `A₀, A(η) > 0` and the target's reading
`a₀ > 0`, `a(η) ≥ a₀/2`,
`(log A(η) − log a(η)) − (log A₀ − log a₀) ≤ (A(η) − A₀)/A₀ − (a(η) − a₀)/a₀ + 2((a(η) − a₀)/a₀)²`. -/
theorem bank_score_endpoint {A₀ Aη a₀ aη : ℝ} (hA₀ : 0 < A₀) (hAη : 0 < Aη) (ha₀ : 0 < a₀)
    (haη : a₀ / 2 ≤ aη) :
    (Real.log Aη - Real.log aη) - (Real.log A₀ - Real.log a₀) ≤
      (Aη - A₀) / A₀ - (aη - a₀) / a₀ + 2 * ((aη - a₀) / a₀) ^ 2 := by
  have hupper : Real.log Aη - Real.log A₀ ≤ (Aη - A₀) / A₀ := by
    rw [← Real.log_div hAη.ne' hA₀.ne']
    calc Real.log (Aη / A₀) ≤ Aη / A₀ - 1 := Real.log_le_sub_one_of_pos (div_pos hAη hA₀)
      _ = (Aη - A₀) / A₀ := by field_simp
  set u := (aη - a₀) / a₀ with hu
  have hu' : -1 / 2 ≤ u := by
    rw [hu, le_div_iff₀ ha₀]
    linarith
  have hlower := log_one_add_ge hu'
  have hratio : 1 + u = aη / a₀ := by rw [hu]; field_simp; ring
  have haη' : 0 < aη := by linarith
  have hlog : Real.log (1 + u) = Real.log aη - Real.log a₀ := by
    rw [hratio, Real.log_div haη'.ne' ha₀.ne']
  linarith

/-- [proved-derived; formal-checked] **The trust region and the second-order constant**: with the
target's reading `a(η) = a₀ + a₁η + a₂η²` (`a₀ > 0`, `0 ≤ a₂ ≤ â₂`, `a₁² ≤ 4a₀a₂`, the
Cauchy–Schwarz of its linear term) and `η²â₂ ≤ a₀/16` (either sign of `η`): `u = (a(η) − a₀)/a₀ ≥ −1/2` and
`2u² ≤ (81/8) η² â₂/a₀`. -/
theorem bank_score_trust {a₀ a₁ a₂ â₂ η : ℝ} (ha₀ : 0 < a₀) (ha₂ : 0 ≤ a₂) (hâ : a₂ ≤ â₂)
    (hcs : a₁ ^ 2 ≤ 4 * a₀ * a₂) (htrust : η ^ 2 * â₂ ≤ a₀ / 16) :
    -1 / 2 ≤ (a₁ * η + a₂ * η ^ 2) / a₀ ∧
      2 * ((a₁ * η + a₂ * η ^ 2) / a₀) ^ 2 ≤ 81 / 8 * (η ^ 2 * â₂ / a₀) := by
  have hâ0 : 0 ≤ â₂ := ha₂.trans hâ
  set x := η ^ 2 * â₂ / a₀ with hx
  have hx0 : 0 ≤ x := by positivity
  have hx16 : x ≤ 1 / 16 := by
    rw [hx, div_le_iff₀ ha₀]
    linarith
  set p := a₁ * η / a₀ with hp
  set q := a₂ * η ^ 2 / a₀ with hq
  have hsplit : (a₁ * η + a₂ * η ^ 2) / a₀ = p + q := by rw [hp, hq]; ring
  have hp2 : p ^ 2 ≤ 4 * x := by
    have key : a₁ ^ 2 * η ^ 2 ≤ 4 * a₀ * â₂ * η ^ 2 := by
      have h1 := mul_le_mul_of_nonneg_right hcs (sq_nonneg η)
      have h2 := mul_le_mul_of_nonneg_left hâ (by positivity : (0 : ℝ) ≤ 4 * a₀ * η ^ 2)
      nlinarith [h1, h2]
    rw [hp, hx, div_pow, div_le_iff₀ (by positivity)]
    calc (a₁ * η) ^ 2 = a₁ ^ 2 * η ^ 2 := by ring
      _ ≤ 4 * a₀ * â₂ * η ^ 2 := key
      _ = 4 * (η ^ 2 * â₂ / a₀) * a₀ ^ 2 := by field_simp
  have hq0 : 0 ≤ q := by positivity
  have hqx : q ≤ x := by
    rw [hq, hx]
    apply div_le_div_of_nonneg_right _ ha₀.le
    nlinarith [sq_nonneg η]
  have hp_abs : |p| ≤ 1 / 2 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (p + 1 / 2), sq_nonneg (p - 1 / 2)]
  have hpq : |p| * q ≤ x / 2 := by
    have hsq : (|p| * q) ^ 2 ≤ (x / 2) ^ 2 := by
      rw [mul_pow, sq_abs]
      have : q ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ hq0 hqx 2
      have hx2 : 4 * x * x ^ 2 ≤ (x / 2) ^ 2 := by nlinarith [hx0, hx16]
      calc p ^ 2 * q ^ 2 ≤ 4 * x * x ^ 2 :=
            mul_le_mul hp2 this (sq_nonneg q) (by linarith)
        _ ≤ (x / 2) ^ 2 := hx2
    have habs := abs_le_of_sq_le_sq hsq (by positivity)
    rwa [abs_of_nonneg (by positivity)] at habs
  rw [hsplit]
  constructor
  · have := neg_abs_le p
    linarith
  · have hcross : 2 * p * q ≤ 2 * (|p| * q) := by
      have := le_abs_self p
      nlinarith
    have hq2 : q ^ 2 ≤ x / 16 := by nlinarith
    nlinarith [hp2, hcross, hpq, hq2]

/-- [proved-derived; formal-checked] **A rounded covector's alignment is charged by its rounding**:
with every reading's covector rounded within `e`, the returns' pairing differs from the true one by
at most `e Σ_x |A′_x|`. -/
theorem rounded_alignment {ι : Type*} (s : Finset ι) (c ĉ b : ι → ℝ) {e : ℝ}
    (h : ∀ x ∈ s, |c x - ĉ x| ≤ e) :
    |∑ x ∈ s, c x * b x - ∑ x ∈ s, ĉ x * b x| ≤ e * ∑ x ∈ s, |b x| := by
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x hx => ?_)
  rw [← sub_mul, abs_mul]
  exact mul_le_mul_of_nonneg_right (h x hx) (abs_nonneg _)

/-- [proved-derived; formal-checked] **and the readings' derivatives by Cauchy–Schwarz over the
candidates**: `Σ_x √(A_x) √(A₂,x) ≤ √(Σ A) √(Σ A₂)`, so `Σ_x |A′_x| ≤ 2 √(A₀ Â₂)` when
`|A′_x| ≤ 2 √(A_x) √(A₂,x)`. -/
theorem sum_sqrt_mul_le {ι : Type*} (s : Finset ι) (a b : ι → ℝ) (ha : ∀ x ∈ s, 0 ≤ a x)
    (hb : ∀ x ∈ s, 0 ≤ b x) :
    ∑ x ∈ s, Real.sqrt (a x) * Real.sqrt (b x) ≤
      Real.sqrt (∑ x ∈ s, a x) * Real.sqrt (∑ x ∈ s, b x) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq s (fun x => Real.sqrt (a x))
    (fun x => Real.sqrt (b x))
  have hsa : ∑ x ∈ s, Real.sqrt (a x) ^ 2 = ∑ x ∈ s, a x :=
    Finset.sum_congr rfl fun x hx => Real.sq_sqrt (ha x hx)
  have hsb : ∑ x ∈ s, Real.sqrt (b x) ^ 2 = ∑ x ∈ s, b x :=
    Finset.sum_congr rfl fun x hx => Real.sq_sqrt (hb x hx)
  rw [hsa, hsb] at hcs
  have hA : 0 ≤ ∑ x ∈ s, a x := Finset.sum_nonneg ha
  have hB : 0 ≤ ∑ x ∈ s, b x := Finset.sum_nonneg hb
  have hlhs : 0 ≤ ∑ x ∈ s, Real.sqrt (a x) * Real.sqrt (b x) :=
    Finset.sum_nonneg fun x _ => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  rw [← Real.sqrt_mul hA]
  exact Real.le_sqrt_of_sq_le hcs

/-! ## 4. The joint certificate with a score beside the logits -/

/-- [proved-derived; formal-checked] **A score beside the logits joins the joint certificate.** A
readout score within `−A_r + ½J` and a bank score within `−a_b + ½Q_b` along the families' rays,
with `J + Q_b ≤ A_r + a_b`, descend together by at least half their first-order decrease. -/
theorem joint_descends_beside {φr φr₀ φb φb₀ Ar ab J Qb : ℝ}
    (hr : φr ≤ φr₀ - Ar + 1 / 2 * J) (hb : φb ≤ φb₀ - ab + 1 / 2 * Qb)
    (hjoint : J + Qb ≤ Ar + ab) : φr + φb ≤ φr₀ + φb₀ - 1 / 2 * (Ar + ab) := by
  linarith

/-! ## 5. Where the executed law departs from the kicked chart -/

/-- [proved-derived; formal-checked] **The node plane's reflection conjugates a pump's reflection
to its conjugate carrier's**: `F R(c) F = R(c̄)`, `F = R(1) = diag(1, −1)`. -/
theorem flip_reflection {R : Type*} [CommRing R] (c s : R) :
    reflection (1 : R) 0 * reflection c s * reflection 1 0 = reflection c (-s) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [reflection, Matrix.mul_apply, Fin.sum_univ_two]

/-- [proved-derived; formal-checked] **and the kicked chart's transport to the conjugate turn**:
`F Rot(v) F = Rot(v̄)`. -/
theorem flip_rotation {R : Type*} [CommRing R] (a b : R) :
    reflection (1 : R) 0 * FloquetPassage.rotation a b * reflection 1 0 =
      FloquetPassage.rotation a (-b) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [reflection, FloquetPassage.rotation, Matrix.mul_apply, Fin.sum_univ_two]

private theorem sum_mul_star_sum (f : ℕ → ℂ) (n : ℕ) :
    ∑ t ∈ Finset.range n, ∑ s ∈ Finset.range n, f t * star (f s) =
      (∑ t ∈ Finset.range n, f t) * star (∑ s ∈ Finset.range n, f s) := by
  rw [star_sum, Finset.sum_mul_sum]

/-- `Re(a b̄) Re(β z w̄) = ½ (Re(β (a z) conj(b w)) + Re(β̄ (a z̄) conj(b w̄)))`: `Re U Re V =
½ Re((U + Ū) V)`. -/
private theorem re_mul_re_split (a b β z w : ℂ) :
    (a * star b).re * (β * z * star w).re =
      ((β * ((a * z) * star (b * w))).re + (star β * ((a * star z) * star (b * star w))).re) / 2 := by
  simp only [Complex.star_def, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    map_mul]
  ring

/-- `Σ_t Σ_s Re(γ f_t conj f_s) = Re γ · |Σ_t f_t|²`. -/
private theorem pair_sum_re (f : ℕ → ℂ) (γ : ℂ) (n : ℕ) :
    ∑ t ∈ Finset.range n, ∑ s ∈ Finset.range n, (γ * (f t * star (f s))).re =
      γ.re * Complex.normSq (∑ t ∈ Finset.range n, f t) := by
  have h1 : ∑ t ∈ Finset.range n, ∑ s ∈ Finset.range n, (γ * (f t * star (f s))).re =
      (γ * ∑ t ∈ Finset.range n, ∑ s ∈ Finset.range n, f t * star (f s)).re := by
    simp only [Finset.mul_sum, Complex.re_sum]
  rw [h1, sum_mul_star_sum, Complex.star_def, Complex.mul_conj]
  simp [Complex.mul_re]

/-- [proved-derived; formal-checked] **The executed pair terms read both sidebands**:
`Σ_(t,s) Re(c_t c̄_s) Re(β ζ^t conj ζ^s) = ½ Re β (|Σ_t c_t ζ^t|² + |Σ_t c_t ζ̄^t|²)`. A real
kernel on the relative phases reads the resonance and its mirror equally, where the kicked chart's
`v^n (u_t v̄^(2t)) conj(u_s v̄^(2s))` reads one. -/
theorem sideband_pair_sum (c : ℕ → ℂ) (β ζ : ℂ) (n : ℕ) :
    ∑ t ∈ Finset.range n, ∑ s ∈ Finset.range n,
        (c t * star (c s)).re * (β * ζ ^ t * star (ζ ^ s)).re =
      1 / 2 * β.re *
        (Complex.normSq (∑ t ∈ Finset.range n, c t * ζ ^ t) +
          Complex.normSq (∑ t ∈ Finset.range n, c t * star ζ ^ t)) := by
  have hsplit : ∀ t s : ℕ, (c t * star (c s)).re * (β * ζ ^ t * star (ζ ^ s)).re =
      ((β * ((c t * ζ ^ t) * star (c s * ζ ^ s))).re +
        (star β * ((c t * star ζ ^ t) * star (c s * star ζ ^ s))).re) / 2 := by
    intro t s
    simpa only [star_pow] using re_mul_re_split (c t) (c s) β (ζ ^ t) (ζ ^ s)
  calc ∑ t ∈ Finset.range n, ∑ s ∈ Finset.range n,
        (c t * star (c s)).re * (β * ζ ^ t * star (ζ ^ s)).re
      = ∑ t ∈ Finset.range n, ∑ s ∈ Finset.range n,
          ((β * ((c t * ζ ^ t) * star (c s * ζ ^ s))).re +
            (star β * ((c t * star ζ ^ t) * star (c s * star ζ ^ s))).re) / 2 :=
        Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun s _ => hsplit t s
    _ = (∑ t ∈ Finset.range n, ∑ s ∈ Finset.range n,
            (β * ((c t * ζ ^ t) * star (c s * ζ ^ s))).re +
          ∑ t ∈ Finset.range n, ∑ s ∈ Finset.range n,
            (star β * ((c t * star ζ ^ t) * star (c s * star ζ ^ s))).re) / 2 := by
        rw [← Finset.sum_add_distrib, Finset.sum_div]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [← Finset.sum_add_distrib, Finset.sum_div]
    _ = (β.re * Complex.normSq (∑ t ∈ Finset.range n, c t * ζ ^ t) +
          (star β).re * Complex.normSq (∑ t ∈ Finset.range n, c t * star ζ ^ t)) / 2 := by
        rw [pair_sum_re (fun t => c t * ζ ^ t) β n,
          pair_sum_re (fun t => c t * star ζ ^ t) (star β) n]
    _ = _ := by
        rw [Complex.star_def, Complex.conj_re]
        ring

section Audit

#print axioms bank_face_covector
#print axioms member_amplitude_ray
#print axioms resonance_gain
#print axioms log_one_add_ge
#print axioms bank_score_endpoint
#print axioms bank_score_trust
#print axioms rounded_alignment
#print axioms sum_sqrt_mul_le
#print axioms joint_descends_beside
#print axioms flip_reflection
#print axioms flip_rotation
#print axioms sideband_pair_sum

end Audit

end Holonics.HNN.BankFace
