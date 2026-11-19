import Holonics.HNN.TargetFace

/-!
# HNN.TargetFaceDescent: the innovation toward the target's code face descends the scored face

The #410 box reads: "Descent of the scored cross-entropy face (`HNN/TargetFace`): a relation between
`χ_R(T) − W f` and the reached covector `q − p̃`." It answers the `[open]` paragraph of
`Holonics/HNN/TargetFace.lean`: "A descent statement needs a relation between `χ_R(T) − W f` and the
reached covector `q − p̃`, which no law here provides." The scored face is the owner's base-2 code
length `ℓ_t(z) = codeLength z t = −z_t + log₂ Σ_c 2^(z_c)` (`HNN/Ratio`), read at the produced logits
`z = W f`; its smooth face is `p(z)_c = 2^(z_c)/Σ_d 2^(z_d)` (`smoothFace`, the owner's
`NormalizedExponential.face` at the potentials `z ln 2`, `smoothFace_eq_face`); the target is the
one-hot `q = e_t` and its declared chart the code face `χ = χ_R(T) = m·e_t` (`TargetFace.codeFace`),
whose margin law `MarginCodes |A| L m` makes it code the target within `1/L` bits
(`TargetFace.margin_rule_codeLength`). The innovation is `χ − z`; the reached covector is `q − r` for
a normalized face `r`: the smooth face `p(z)`, or the odometer's masses `p̃ ∝ 2^n (1 + k/L)`
(`HNN/Ratio.odometerWeight`).

Sources: the box; the owner's `[open]` paragraph; the record of September 25,
`research/records/2026-09-25_CAMPAIGN_ONE_LOCATED_FAILURE.md` (the addendum's Decision 26, "descent
of the cross-entropy face is not claimed, and the exposure's receipt decides", and Decision 27's
reading, "averaging the one-hot code face `m e_t` in the log chart settles the logits at `m p̄`, whose
face is far flatter than `p̄`", which `window_first_order_rise` states at first order); CLAUDE.md's
laws "Learning uses the covector of a declared comparison" and "Loss is the logarithm of a ratio of
Holons" (the classical loss is the perceived difference, and the HNN adjoint uses the odometer's
covector `p̃ − q`). Atlas rows served: `hnn.target-code-face` (the code face and its margin),
`hnn.exogenous-normal-law` (the step `W + (T − W F) H′⁻¹` whose one-sample move is item 6),
`receiver.odometer-pairing` and `hnn.odometer-covector-descends` (the odometer's covector paired with
the smooth gradient; here it is paired with the innovation), `receiver.station-score-curvature`
(`HNN/Ratio/Resolution.codeLength_quadratic_upper`, the quadratic upper model whose first-order term
is item 1's gradient; item 2 is its lower companion). No atlas row states the convexity of the code
length (`rg -n -i 'convex|jensen' docs/atlas/` finds none on the face).

[proved-standard; formal-checked] What is proved, classical.

1. **The gradient** (`hasDerivAt_codeLength`, `hasDerivAt_codeLength_single`): along every direction
   `v`, `s ↦ ℓ_t(z + s v)` has derivative `⟨p(z) − q, v⟩` at `0`; at `v = e_c` it is `p(z)_c − q_c`.
   The base-2 chart's `ln 2` cancels: the chart's gradient is the face's covector itself.
2. **The tangent inequality and convexity** (`codeLength_tangent`, `codeLength_segment_le`): for all
   `y z`, `ℓ_t(y) ≥ ℓ_t(z) + ⟨p(z) − q, y − z⟩`, which is Jensen for `exp` under the face's weights,
   `log₂ Σ_c p_c 2^(y_c − z_c) ≥ Σ_c p_c (y_c − z_c)`; and for `η ∈ [0, 1]`,
   `ℓ_t(z + η(y − z)) ≤ (1 − η) ℓ_t(z) + η ℓ_t(y)`, from the tangent at the segment's point.

[proved-derived; formal-checked] What is proved, the house's joins.

3. **The innovation descends the scored face** (`innovation_pairing_ge`,
   `innovation_pairing_ge_margin`, `innovation_descends`, `codeFace_innovation_descends`):
   `⟨q − p(z), χ − z⟩ ≥ ℓ_t(z) − ℓ_t(χ)`, and under `MarginCodes |A| L m`, `L > 0`, at the code face
   `≥ ℓ_t(z) − 1/L`. Wherever the face codes the target worse than the code face does, the innovation
   is a strict first-order descent direction (`⟨p(z) − q, χ − z⟩ < 0`, the derivative of item 1),
   and every point `z + η(χ − z)`, `η ∈ (0, 1]`, codes the target strictly better than `z`.
4. **The pairing identity for any normalized face** (`pairing_shortfall`): for every `r` with
   `Σ r = 1`, `⟨q − r, μ e_t − z⟩ = Σ_(c≠t) r_c (μ − (z_t − z_c))`: the reached covector pairs with
   the innovation as the `r`-weighted sum, over the other classes, of the margin's shortfall. It is
   positive when `r` is positive off `t`, some class differs from `t` and every margin `z_t − z_c` is
   below `μ` (`pairing_pos`); the odometer's normalized masses are such an `r`, so its covector
   `q − p̃` pairs positively with the innovation too (`odometer_pairing_innovation`). It vanishes
   where every margin equals `μ` (`pairing_zero_of_full_margins`), and with positive `r` and margins
   at most `μ` only there (`pairing_eq_zero_iff`); without the one-sided margins it can vanish
   elsewhere (`pairing_zero_needs_one_side`). It is unchanged by a common shift of the logits
   (`pairing_gauge`).
5. **The locus's map** (`map_pairing`, `hasDerivAt_map_codeLength`, `map_innovation_descends`): with
   `z = W f`, the innovation's rank-one map direction `(χ − W f) ⊗ f` pairs with the covector's map
   form `(q − r) ⊗ f` in the Frobenius pairing as `⟨q − r, χ − W f⟩ ⟨f, f⟩`; along a map direction
   `D` the scored face moves by `Σ_ij D_ij ((p − q) ⊗ f)_ij`, so the map's step along the innovation's
   direction descends at first order wherever item 3's does and `f ≠ 0`.
6. **One sample's exogenous step moves the logits along the innovation**
   (`exogenousStep_one_sample`, `gain_mem_unit`, `gain_pos`, `exogenous_one_sample_descends`,
   `exogenous_one_sample_strict`, `exogenousDeposit_one_sample`,
   `exogenousDeposit_codeFace_descends`): for one reached sample, `F = w f fᵀ`, `T = w χ fᵀ`,
   the owner's `exogenousStep W F T X` at any chart `X` reads `W′ f = W f + w ⟨f, X f⟩ (χ − W f)`. For
   `H` positive semidefinite, `w ≥ 0` and `H′ u = f`, `H′ = H + w f fᵀ`, the gain `w ⟨f, u⟩` lies in
   `[0, 1]`, since `⟨f, u⟩ = ⟨u, H u⟩ + w ⟨f, u⟩² ≥ w ⟨f, u⟩²`, and it is positive when `w > 0` and
   `f ≠ 0`. At the solved chart `X = H′⁻¹` the gain is `sampleGain H w f`, and with item 2
   `ℓ_t(W′ f) ≤ (1 − s) ℓ_t(W f) + s ℓ_t(χ)`: one sample's exogenous step never raises its scored
   face above that chord, and strictly descends it when `ℓ_t(χ) < ℓ_t(W f)`, `w > 0`, `f ≠ 0`. The
   receiving locus's own deposit on one reached comparison,
   `TargetFace.exogenousDeposit θ (targetWindow m [(w, f, t)])`, is this step at the code face, so
   under the margin law it descends wherever the face codes the target in more than one grain. No
   symmetry of `H′` is used for the move: the step's row factor is `fᵀ H′⁻¹`, and the move reads
   `⟨f, H′⁻¹ f⟩` whichever side the chart multiplies.

[counterexample; formal-checked] The witnesses.

7. **The innovation is not the covector** (`innovation_is_not_the_covector`, `smoothFace_witness`):
   three classes, `z = (0, 0, 1)`, `t = 0`, `m = 2`: `p(z) = (1/4, 1/4, 1/2)`,
   `q − p(z) = (3/4, −1/4, −1/2)`, `χ − z = (2, 0, −1)`; neither is a multiple of the other, and their
   pairing is `2 > 0`, read either way as `Σ_(c≠t) p_c (m − (z_t − z_c)) = ½ + 3/2`.
8. **A window's step can rise at first order** (`window_first_order_rise`,
   `window_samples_alone_descend`, `smoothFace_window`): three classes, one feature `f = 1`, prior
   Gram `1`, map `W = (0, 0, −1)ᵀ`, code faces at margin `1` (the least margin at `|A| = 3`, grain
   `1`), and two samples on the same feature with targets `0` and `1`. Each sample alone would be
   descended by its own one-sample step (item 6; its face codes its target in `log₂(5/2) > 1` bits).
   The window's deposit moves the map to `(1/3, 1/3, −1/3)ᵀ`, and along that move the window's summed
   scored face rises at rate `2/15`: the two code faces' additive-chart mean `(1/2, 1/2, 0)` lifts the
   third class, which both targets pay for.

What is not claimed. Strict decrease of the grain-quantized score: everything here is the smooth
score `codeLength` at the real logits, and a score read through the grain is constant inside a cell
(`HNN/Ratio.quantized_score_has_grain_plateau`). The phase part of the comparison (`alignCost`, the
imaginary logits) is not touched. The prox step's proxy (`HNN/Normal.normal_prox_step`,
`TargetFace.proxy_target_innovation`) is not treated: its innovation is the covector itself. No
descent law for a window of two or more samples is stated: item 8 shows a window's first-order
change can be positive, and the change at the window's endpoint is not computed. The gain's bound
`[0, 1]` is proved at the solved chart `H′⁻¹`; at an executed chart `X̂` the move of item 6 holds with
gain `w ⟨f, X̂ f⟩`, which is not bounded here. The sign of the odometer's pairing with the innovation
is read only where every margin stands below `m` (or at it); where margins pass `m` it depends on the
masses and is not read. No rate is given beyond the chord of item 6; the curvature along the step is
`HNN/Ratio/Resolution.codeLength_quadratic_upper`'s.

The computational object is the helical pair interaction read at the receiving contact: the produced
Holon's logits `z = W f` and the target's code face `χ` are its two sides, the smooth face is the
receiver's reading there, and two covectors cross it, the reached covector `q − r` (the news the
receiver perceives) and the innovation `χ − z` (the additive-chart residual the exogenous law
regresses); item 4 is their pairing, the margin's shortfall weighed by the reading. Of the winding
guide's six general objects this touches faces and placement (the receiver's face, its code length,
and the code face's placement at margin `m`) and the pair (produced against target, the reached
feature's Gram `w f fᵀ` and the rank-one map direction `(χ − W f) ⊗ f`); the helix, the cell
holonomy, the tube and the tower thread stay attached.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.HNN.TargetFaceDescent

open Matrix
open Holonics.Computation.HolonicAdjointNormalization
open Holonics.Computation.HolonicAdjointNormalization.NormalizedExponential
open Holonics.HNN.Ratio (codeLength two_rpow_eq_exp odometerWeight)
open Holonics.HNN.TargetFace (codeFace MarginCodes margin_rule_codeLength exogenousStep
  face_mass_two_rpow exogenousDeposit targetWindow)
open Holonics.HNN.Normal (LocusState windowGram windowCovector)

/-! ## 1–3. The gradient, the tangent inequality and the innovation's descent -/

section Face

variable {Index : Type*} [Fintype Index]

/-- [definition] **The smooth face** `p(z)_c = 2^(z_c) / Σ_d 2^(z_d)` of the logits `z`. -/
def smoothFace (z : Index → ℝ) (c : Index) : ℝ := (2 : ℝ) ^ z c / ∑ d, (2 : ℝ) ^ z d

/-- [proved-derived; formal-checked] The smooth face is the owner's face at the potentials `z ln 2`. -/
theorem smoothFace_eq_face [Nonempty Index] (z : Index → ℝ) (c : Index) :
    smoothFace z c = (face fun c => z c * Real.log 2).mass c :=
  (face_mass_two_rpow z c).symm

/-- [proved-standard; formal-checked] The base-2 partition `Σ_d 2^(z_d)` is positive. -/
theorem twoPartition_pos [Nonempty Index] (z : Index → ℝ) : 0 < ∑ d, (2 : ℝ) ^ z d :=
  Finset.sum_pos (fun _ _ => by positivity) Finset.univ_nonempty

/-- [proved-standard; formal-checked] Every class has positive mass under the smooth face. -/
theorem smoothFace_pos [Nonempty Index] (z : Index → ℝ) (c : Index) : 0 < smoothFace z c :=
  div_pos (by positivity) (twoPartition_pos z)

/-- [proved-standard; formal-checked] The smooth face is normalized. -/
theorem smoothFace_sum [Nonempty Index] (z : Index → ℝ) : ∑ c, smoothFace z c = 1 := by
  simp only [smoothFace, ← Finset.sum_div]
  exact div_self (twoPartition_pos z).ne'

/-- [proved-standard; formal-checked] A covector against the one-hot target reads
`⟨r − e_t, v⟩ = ⟨r, v⟩ − v_t`. -/
theorem pairing_one_hot [DecidableEq Index] (r v : Index → ℝ) (t : Index) :
    (r - Pi.single t 1) ⬝ᵥ v = r ⬝ᵥ v - v t := by
  rw [sub_dotProduct]
  simp [dotProduct, Pi.single_apply]

/-- [proved-standard; formal-checked] **The gradient of the scored face**: along `v`, the code length
moves at rate `⟨p(z) − q, v⟩`, `q = e_t`. -/
theorem hasDerivAt_codeLength [Nonempty Index] [DecidableEq Index] (z v : Index → ℝ) (t : Index) :
    HasDerivAt (fun s : ℝ => codeLength (z + s • v) t) ((smoothFace z - Pi.single t 1) ⬝ᵥ v) 0 := by
  have hl : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hterm : ∀ c ∈ (Finset.univ : Finset Index), HasDerivAt
      (fun s : ℝ => Real.exp ((z c + s * v c) * Real.log 2))
      (Real.exp (z c * Real.log 2) * (v c * Real.log 2)) 0 := by
    intro c _
    have hlin : HasDerivAt (fun s : ℝ => (z c + s * v c) * Real.log 2) (v c * Real.log 2) 0 := by
      have := (((hasDerivAt_id (0 : ℝ)).mul_const (v c)).const_add (z c)).mul_const (Real.log 2)
      simpa using this
    simpa using hlin.exp
  have hS := HasDerivAt.fun_sum hterm
  have hSpos : 0 < ∑ c, Real.exp ((z c + 0 * v c) * Real.log 2) := by
    simpa [two_rpow_eq_exp] using twoPartition_pos z
  have hlog := (hS.log hSpos.ne').div_const (Real.log 2)
  have hlinear : HasDerivAt (fun s : ℝ => -(z t + s * v t)) (-v t) 0 := by
    have := (((hasDerivAt_id' (0 : ℝ)).mul_const (v t)).const_add (z t)).neg
    exact this.congr_deriv (by ring)
  have hfun : (fun s : ℝ => codeLength (z + s • v) t) = fun s =>
      -(z t + s * v t) + Real.log (∑ c, Real.exp ((z c + s * v c) * Real.log 2)) / Real.log 2 := by
    funext s
    simp [codeLength, Real.logb, two_rpow_eq_exp]
  rw [hfun]
  refine (hlinear.add hlog).congr_deriv ?_
  rw [pairing_one_hot]
  simp only [dotProduct, smoothFace, two_rpow_eq_exp, zero_mul, add_zero]
  have hS0 : 0 < ∑ x, Real.exp (z x * Real.log 2) := by
    simpa [two_rpow_eq_exp] using twoPartition_pos z
  have h1 : ∑ x, Real.exp (z x * Real.log 2) / (∑ d, Real.exp (z d * Real.log 2)) * v x =
      (∑ x, Real.exp (z x * Real.log 2) * v x) / ∑ d, Real.exp (z d * Real.log 2) := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun x _ => by ring
  have h2 : ∑ i, Real.exp (z i * Real.log 2) * (v i * Real.log 2) =
      Real.log 2 * ∑ i, Real.exp (z i * Real.log 2) * v i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [h1, h2]
  field_simp
  ring

/-- [proved-standard; formal-checked] **The partial derivative** of the code length in `z_c` is
`p(z)_c − q_c`. -/
theorem hasDerivAt_codeLength_single [Nonempty Index] [DecidableEq Index] (z : Index → ℝ)
    (t c : Index) :
    HasDerivAt (fun s : ℝ => codeLength (z + s • Pi.single c 1) t)
      (smoothFace z c - (Pi.single t 1 : Index → ℝ) c) 0 := by
  refine (hasDerivAt_codeLength z (Pi.single c 1) t).congr_deriv ?_
  rw [dotProduct_single, mul_one, Pi.sub_apply]

/-- [proved-standard; formal-checked] **The tangent inequality**: `ℓ_t(y) ≥ ℓ_t(z) + ⟨p(z) − q, y − z⟩`
(Jensen for `exp` under the face's weights). -/
theorem codeLength_tangent [Nonempty Index] [DecidableEq Index] (y z : Index → ℝ) (t : Index) :
    codeLength z t + (smoothFace z - Pi.single t 1) ⬝ᵥ (y - z) ≤ codeLength y t := by
  have hS := twoPartition_pos z
  have hjensen : Real.exp (∑ c, smoothFace z c * ((y c - z c) * Real.log 2)) ≤
      ∑ c, smoothFace z c * Real.exp ((y c - z c) * Real.log 2) := by
    have h := convexOn_exp.map_sum_le (t := Finset.univ) (w := smoothFace z)
      (p := fun c => (y c - z c) * Real.log 2) (fun c _ => (smoothFace_pos z c).le)
      (smoothFace_sum z) (fun c _ => Set.mem_univ _)
    simpa only [smul_eq_mul] using h
  have hmean : ∑ c, smoothFace z c * ((y c - z c) * Real.log 2) =
      (smoothFace z ⬝ᵥ (y - z)) * Real.log 2 := by
    simp only [dotProduct, Finset.sum_mul, Pi.sub_apply]
    exact Finset.sum_congr rfl fun c _ => by ring
  have hpart : (∑ c, (2 : ℝ) ^ z c) * ∑ c, smoothFace z c * Real.exp ((y c - z c) * Real.log 2) =
      ∑ c, (2 : ℝ) ^ y c := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← two_rpow_eq_exp, smoothFace, ← mul_assoc, mul_div_cancel₀ _ hS.ne',
      ← Real.rpow_add (by norm_num)]
    congr 1
    ring
  have hle : (2 : ℝ) ^ (smoothFace z ⬝ᵥ (y - z)) * ∑ c, (2 : ℝ) ^ z c ≤ ∑ c, (2 : ℝ) ^ y c := by
    rw [← hpart, two_rpow_eq_exp, ← hmean, mul_comm]
    exact mul_le_mul_of_nonneg_left hjensen hS.le
  have hlog := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) hle
  rw [Real.logb_mul (by positivity) hS.ne', Real.logb_rpow (by norm_num) (by norm_num)] at hlog
  rw [pairing_one_hot]
  simp only [codeLength, Pi.sub_apply]
  linarith

/-- [proved-standard; formal-checked] **The scored face is convex**: on the segment from `z` to `y`
it stays under the chord, `ℓ_t(z + η(y − z)) ≤ (1 − η) ℓ_t(z) + η ℓ_t(y)`, `η ∈ [0, 1]`. -/
theorem codeLength_segment_le [Nonempty Index] [DecidableEq Index] (y z : Index → ℝ) (t : Index)
    {η : ℝ} (h0 : 0 ≤ η) (h1 : η ≤ 1) :
    codeLength (z + η • (y - z)) t ≤ (1 - η) * codeLength z t + η * codeLength y t := by
  set x := z + η • (y - z) with hx
  have hz := codeLength_tangent z x t
  have hy := codeLength_tangent y x t
  have ez : z - x = (-η) • (y - z) := by
    rw [hx]; ext c; simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  have ey : y - x = (1 - η) • (y - z) := by
    rw [hx]; ext c; simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [ez, dotProduct_smul, smul_eq_mul] at hz
  rw [ey, dotProduct_smul, smul_eq_mul] at hy
  nlinarith [mul_le_mul_of_nonneg_left hz (sub_nonneg.mpr h1), mul_le_mul_of_nonneg_left hy h0]

/-- [proved-derived; formal-checked] **The innovation pairs with the reached covector at least by the
code's gap**: `⟨q − p(z), χ − z⟩ ≥ ℓ_t(z) − ℓ_t(χ)`. -/
theorem innovation_pairing_ge [Nonempty Index] [DecidableEq Index] (χ z : Index → ℝ) (t : Index) :
    codeLength z t - codeLength χ t ≤ (Pi.single t 1 - smoothFace z) ⬝ᵥ (χ - z) := by
  have h := codeLength_tangent χ z t
  have e : (Pi.single t 1 - smoothFace z) ⬝ᵥ (χ - z) =
      -((smoothFace z - Pi.single t 1) ⬝ᵥ (χ - z)) := by
    rw [← neg_dotProduct, neg_sub]
  rw [e]
  linarith

/-- [proved-derived; formal-checked] **At the code face under the margin law**:
`⟨q − p(z), m e_t − z⟩ ≥ ℓ_t(z) − 1/L`. -/
theorem innovation_pairing_ge_margin [Nonempty Index] [DecidableEq Index] {L m : ℕ} (hL : 0 < L)
    (hm : MarginCodes (Fintype.card Index) L m) (z : Index → ℝ) (t : Index) :
    codeLength z t - 1 / L ≤ (Pi.single t 1 - smoothFace z) ⬝ᵥ ((codeFace m t : Index → ℝ) - z) := by
  have h1 := (margin_rule_codeLength hL m t).mp hm
  have h2 := innovation_pairing_ge (codeFace m t) z t
  linarith

/-- [proved-derived; formal-checked] **The innovation descends the scored face** wherever `χ` codes
the target better than `z`: a strict first-order descent direction, and every point of the segment
`z + η(χ − z)`, `η ∈ (0, 1]`, codes the target strictly better than `z`. -/
theorem innovation_descends [Nonempty Index] [DecidableEq Index] (χ z : Index → ℝ) (t : Index)
    (h : codeLength χ t < codeLength z t) :
    (smoothFace z - Pi.single t 1) ⬝ᵥ (χ - z) < 0 ∧
      HasDerivAt (fun s : ℝ => codeLength (z + s • (χ - z)) t)
        ((smoothFace z - Pi.single t 1) ⬝ᵥ (χ - z)) 0 ∧
      ∀ η : ℝ, 0 < η → η ≤ 1 → codeLength (z + η • (χ - z)) t < codeLength z t := by
  refine ⟨?_, hasDerivAt_codeLength z (χ - z) t, fun η h0 h1 => ?_⟩
  · have := codeLength_tangent χ z t
    linarith
  · have hseg := codeLength_segment_le χ z t h0.le h1
    nlinarith

/-- [proved-derived; formal-checked] **Toward the code face under the margin law**: where the face
codes the target in more than `1/L` bits, the innovation `m e_t − z` descends it strictly. -/
theorem codeFace_innovation_descends [Nonempty Index] [DecidableEq Index] {L m : ℕ} (hL : 0 < L)
    (hm : MarginCodes (Fintype.card Index) L m) (z : Index → ℝ) (t : Index)
    (hz : 1 / (L : ℝ) < codeLength z t) :
    (smoothFace z - Pi.single t 1) ⬝ᵥ ((codeFace m t : Index → ℝ) - z) < 0 ∧
      ∀ η : ℝ, 0 < η → η ≤ 1 →
        codeLength (z + η • ((codeFace m t : Index → ℝ) - z)) t < codeLength z t := by
  have h1 := (margin_rule_codeLength hL m t).mp hm
  obtain ⟨hneg, -, hseg⟩ := innovation_descends (codeFace m t) z t (by linarith)
  exact ⟨hneg, hseg⟩

end Face

/-! ## 4. The pairing identity, for any normalized face -/

section Pairing

variable {Index : Type*} [Fintype Index] [DecidableEq Index]

/-- [proved-derived; formal-checked] **The pairing is the weighted shortfall of the margins**: for
`Σ r = 1`, `⟨q − r, μ e_t − z⟩ = Σ_(c≠t) r_c (μ − (z_t − z_c))`. -/
theorem pairing_shortfall (r z : Index → ℝ) (hr : ∑ c, r c = 1) (t : Index) (μ : ℝ) :
    (Pi.single t 1 - r) ⬝ᵥ (Pi.single t μ - z) =
      ∑ c ∈ Finset.univ.erase t, r c * (μ - (z t - z c)) := by
  have hrt : r t = 1 - ∑ c ∈ Finset.univ.erase t, r c := by
    rw [← hr, ← Finset.add_sum_erase _ _ (Finset.mem_univ t)]; ring
  rw [dotProduct, ← Finset.add_sum_erase _ _ (Finset.mem_univ t)]
  have hrest : ∑ c ∈ Finset.univ.erase t,
      ((Pi.single t 1 : Index → ℝ) - r) c * ((Pi.single t μ : Index → ℝ) - z) c =
      ∑ c ∈ Finset.univ.erase t, r c * z c := by
    refine Finset.sum_congr rfl fun c hc => ?_
    have hct : c ≠ t := (Finset.mem_erase.mp hc).1
    simp [Pi.single_eq_of_ne hct]
  rw [hrest]
  simp only [Pi.sub_apply, Pi.single_eq_same, hrt]
  rw [show ∑ c ∈ Finset.univ.erase t, r c * (μ - (z t - z c)) =
      (∑ c ∈ Finset.univ.erase t, r c) * (μ - z t) + ∑ c ∈ Finset.univ.erase t, r c * z c by
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun c _ => by ring]
  ring

/-- [proved-derived; formal-checked] **The pairing is positive** when `r` is positive off `t`, some
class differs from `t`, and every margin `z_t − z_c` is below `μ`. -/
theorem pairing_pos (r z : Index → ℝ) (hr : ∑ c, r c = 1) (t : Index) (μ : ℝ)
    (hpos : ∀ c, c ≠ t → 0 < r c) (hshort : ∀ c, c ≠ t → z t - z c < μ) (hc : ∃ c, c ≠ t) :
    0 < (Pi.single t 1 - r) ⬝ᵥ (Pi.single t μ - z) := by
  rw [pairing_shortfall r z hr t μ]
  obtain ⟨c, hct⟩ := hc
  refine Finset.sum_pos (fun i hi => ?_) ⟨c, Finset.mem_erase.mpr ⟨hct, Finset.mem_univ c⟩⟩
  have hit : i ≠ t := (Finset.mem_erase.mp hi).1
  exact mul_pos (hpos i hit) (sub_pos.mpr (hshort i hit))

/-- [proved-derived; formal-checked] **The pairing vanishes where every margin equals `μ`**, for any
normalized `r`. -/
theorem pairing_zero_of_full_margins (r z : Index → ℝ) (hr : ∑ c, r c = 1) (t : Index) (μ : ℝ)
    (hfull : ∀ c, c ≠ t → z t - z c = μ) :
    (Pi.single t 1 - r) ⬝ᵥ (Pi.single t μ - z) = 0 := by
  rw [pairing_shortfall r z hr t μ]
  refine Finset.sum_eq_zero fun c hc => ?_
  rw [hfull c (Finset.mem_erase.mp hc).1, sub_self, mul_zero]

/-- [proved-derived; formal-checked] **Only there, under one-sided margins**: with `r` positive off
`t` and every margin at most `μ`, the pairing vanishes if and only if every margin equals `μ`. -/
theorem pairing_eq_zero_iff (r z : Index → ℝ) (hr : ∑ c, r c = 1) (t : Index) (μ : ℝ)
    (hpos : ∀ c, c ≠ t → 0 < r c) (hshort : ∀ c, c ≠ t → z t - z c ≤ μ) :
    (Pi.single t 1 - r) ⬝ᵥ (Pi.single t μ - z) = 0 ↔ ∀ c, c ≠ t → z t - z c = μ := by
  refine ⟨fun h c hct => ?_, pairing_zero_of_full_margins r z hr t μ⟩
  rw [pairing_shortfall r z hr t μ] at h
  have hnn : ∀ i ∈ Finset.univ.erase t, 0 ≤ r i * (μ - (z t - z i)) := fun i hi =>
    mul_nonneg (hpos i (Finset.mem_erase.mp hi).1).le
      (sub_nonneg.mpr (hshort i (Finset.mem_erase.mp hi).1))
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h c
    (Finset.mem_erase.mpr ⟨hct, Finset.mem_univ c⟩)
  rcases mul_eq_zero.mp h0 with h' | h'
  · exact absurd h' (hpos c hct).ne'
  · linarith

/-- [proved-derived; formal-checked] **The pairing is gauge-free**: a common shift `z + a` of the
logits leaves it. -/
theorem pairing_gauge (r z : Index → ℝ) (hr : ∑ c, r c = 1) (t : Index) (μ a : ℝ) :
    (Pi.single t 1 - r) ⬝ᵥ (Pi.single t μ - fun c => z c + a) =
      (Pi.single t 1 - r) ⬝ᵥ (Pi.single t μ - z) := by
  rw [pairing_shortfall r _ hr t μ, pairing_shortfall r z hr t μ]
  exact Finset.sum_congr rfl fun c _ => by ring

/-- [proved-derived; formal-checked] **The odometer's covector pairs positively with the
innovation**: the normalized masses `p̃_c ∝ 2^(n_c)(1 + k_c/L)` give `⟨q − p̃, μ e_t − z⟩ > 0` when
every margin is below `μ`. -/
theorem odometer_pairing_innovation [Nonempty Index] (n : Index → ℤ) (k : Index → ℕ) (L : ℕ)
    (z : Index → ℝ) (t : Index) (μ : ℝ) (hshort : ∀ c, c ≠ t → z t - z c < μ)
    (hc : ∃ c, c ≠ t) :
    0 < (Pi.single t 1 - fun c => odometerWeight (n c) (k c) L / ∑ d, odometerWeight (n d) (k d) L)
      ⬝ᵥ (Pi.single t μ - z) := by
  have hw : ∀ c, 0 < odometerWeight (n c) (k c) L := fun c => by unfold odometerWeight; positivity
  have hS : 0 < ∑ d, odometerWeight (n d) (k d) L :=
    Finset.sum_pos (fun d _ => hw d) Finset.univ_nonempty
  refine pairing_pos _ z ?_ t μ (fun c _ => div_pos (hw c) hS) hshort hc
  rw [← Finset.sum_div]
  exact div_self hS.ne'

/-- [counterexample; formal-checked] **The one-sided margins are load-bearing for the zero**: at
`r = (1/3, 1/3, 1/3)`, `z = (0, −1, −3)`, `μ = 2`, the margins `1` and `3` straddle `μ` and the
pairing vanishes. -/
theorem pairing_zero_needs_one_side :
    ((Pi.single 0 1 : Fin 3 → ℝ) - ![1 / 3, 1 / 3, 1 / 3]) ⬝ᵥ
        ((Pi.single 0 2 : Fin 3 → ℝ) - ![0, -1, -3]) = 0 ∧
      (![0, -1, -3] : Fin 3 → ℝ) 0 - (![0, -1, -3] : Fin 3 → ℝ) 1 ≠ 2 := by
  constructor
  · simp [dotProduct, Fin.sum_univ_three]
    norm_num
  · norm_num

end Pairing

/-! ## 5. The locus's map -/

section Map

variable {Index σ : Type*} [Fintype Index] [DecidableEq Index] [Fintype σ]

/-- [proved-derived; formal-checked] **The map forms pair as the logits do, times `⟨f, f⟩`**: in the
Frobenius pairing, `⟨(χ − W f) ⊗ f, (q − r) ⊗ f⟩ = ⟨q − r, χ − W f⟩ ⟨f, f⟩`. -/
theorem map_pairing (W : Matrix Index σ ℝ) (f : σ → ℝ) (χ r : Index → ℝ) (t : Index) :
    ∑ i, ∑ j, vecMulVec (χ - W *ᵥ f) f i j * vecMulVec (Pi.single t 1 - r) f i j =
      ((Pi.single t 1 - r) ⬝ᵥ (χ - W *ᵥ f)) * (f ⬝ᵥ f) := by
  rw [dotProduct, dotProduct, Finset.sum_mul_sum]
  simp only [vecMulVec_apply]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- [proved-derived; formal-checked] **The scored face's gradient on the map** is `(p − q) ⊗ f`:
along `W + s D`, `ℓ_t((W + s D) f)` moves at rate `Σ_ij D_ij ((p − q) ⊗ f)_ij`. -/
theorem hasDerivAt_map_codeLength [Nonempty Index] (W D : Matrix Index σ ℝ) (f : σ → ℝ)
    (t : Index) :
    HasDerivAt (fun s : ℝ => codeLength ((W + s • D) *ᵥ f) t)
      (∑ i, ∑ j, D i j * vecMulVec (smoothFace (W *ᵥ f) - Pi.single t 1) f i j) 0 := by
  have hpath : (fun s : ℝ => codeLength ((W + s • D) *ᵥ f) t) =
      fun s : ℝ => codeLength (W *ᵥ f + s • (D *ᵥ f)) t := by
    funext s
    congr 1
    ext i
    simp only [mulVec, dotProduct, Matrix.add_apply, Matrix.smul_apply, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
  rw [hpath]
  refine (hasDerivAt_codeLength (W *ᵥ f) (D *ᵥ f) t).congr_deriv ?_
  simp only [dotProduct, mulVec, vecMulVec_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- [proved-derived; formal-checked] **The map's step along the innovation's direction descends**:
along `W + s (χ − W f) ⊗ f`, the rate is `⟨p − q, χ − W f⟩ ⟨f, f⟩ < 0` when `ℓ_t(χ) < ℓ_t(W f)`,
`f ≠ 0`. -/
theorem map_innovation_descends [Nonempty Index] (W : Matrix Index σ ℝ) (f : σ → ℝ)
    (χ : Index → ℝ) (t : Index) (hf : f ≠ 0) (h : codeLength χ t < codeLength (W *ᵥ f) t) :
    HasDerivAt (fun s : ℝ => codeLength ((W + s • vecMulVec (χ - W *ᵥ f) f) *ᵥ f) t)
        (((smoothFace (W *ᵥ f) - Pi.single t 1) ⬝ᵥ (χ - W *ᵥ f)) * (f ⬝ᵥ f)) 0 ∧
      ((smoothFace (W *ᵥ f) - Pi.single t 1) ⬝ᵥ (χ - W *ᵥ f)) * (f ⬝ᵥ f) < 0 := by
  have hff : 0 < f ⬝ᵥ f := by
    have h0 : 0 ≤ f ⬝ᵥ f := Finset.sum_nonneg fun i _ => mul_self_nonneg (f i)
    exact lt_of_le_of_ne h0 (fun h' => hf (dotProduct_self_eq_zero.mp h'.symm))
  refine ⟨(hasDerivAt_map_codeLength W _ f t).congr_deriv ?_,
    mul_neg_of_neg_of_pos (innovation_descends χ (W *ᵥ f) t h).1 hff⟩
  rw [dotProduct, dotProduct, Finset.sum_mul_sum]
  simp only [vecMulVec_apply]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end Map

/-! ## 6. One sample's exogenous step -/

section Exogenous

variable {σ : Type*} [Fintype σ]

/-- [proved-standard; formal-checked] A rank-one map acts as `(a ⊗ b) u = ⟨b, u⟩ a`. -/
theorem rankOne_mulVec {𝕜 τ : Type*} [Field 𝕜] (a : τ → 𝕜) (b u : σ → 𝕜) :
    vecMulVec a b *ᵥ u = (b ⬝ᵥ u) • a := by
  ext i
  simp only [mulVec, dotProduct, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- [proved-derived; formal-checked] **One sample's exogenous step moves the logits along the
innovation**: at `F = w f fᵀ`, `T = w χ fᵀ` and any chart `X`, `W′ f = W f + w ⟨f, X f⟩ (χ − W f)`. -/
theorem exogenousStep_one_sample {𝕜 τ : Type*} [Field 𝕜] (W : Matrix τ σ 𝕜) (w : 𝕜) (f : σ → 𝕜)
    (χ : τ → 𝕜) (X : Matrix σ σ 𝕜) :
    exogenousStep W (w • vecMulVec f f) (w • vecMulVec χ f) X *ᵥ f =
      W *ᵥ f + (w * (f ⬝ᵥ (X *ᵥ f))) • (χ - W *ᵥ f) := by
  have hinn : w • vecMulVec χ f - W * (w • vecMulVec f f) = w • vecMulVec (χ - W *ᵥ f) f := by
    rw [Matrix.mul_smul, mul_vecMulVec]
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply, Pi.sub_apply, smul_eq_mul]
    ring
  unfold exogenousStep
  rw [hinn, add_mulVec, ← mulVec_mulVec, Matrix.smul_mulVec, rankOne_mulVec, smul_smul]

/-- [proved-derived; formal-checked] **The one-sample gain lies in `[0, 1]`**: for `H` positive
semidefinite, `w ≥ 0` and `(H + w f fᵀ) u = f`, `⟨f, u⟩ ≥ 0` and `0 ≤ w ⟨f, u⟩ ≤ 1`. -/
theorem gain_mem_unit {H : Matrix σ σ ℝ} (hH : H.PosSemidef) {w : ℝ} (hw : 0 ≤ w) (f u : σ → ℝ)
    (hu : (H + w • vecMulVec f f) *ᵥ u = f) :
    0 ≤ f ⬝ᵥ u ∧ 0 ≤ w * (f ⬝ᵥ u) ∧ w * (f ⬝ᵥ u) ≤ 1 := by
  have hq : 0 ≤ u ⬝ᵥ H *ᵥ u := by simpa using hH.dotProduct_mulVec_nonneg u
  have key : f ⬝ᵥ u = u ⬝ᵥ H *ᵥ u + w * (f ⬝ᵥ u) ^ 2 := by
    calc f ⬝ᵥ u = u ⬝ᵥ ((H + w • vecMulVec f f) *ᵥ u) := by rw [hu, dotProduct_comm]
      _ = u ⬝ᵥ H *ᵥ u + w * (f ⬝ᵥ u) ^ 2 := by
        rw [add_mulVec, Matrix.smul_mulVec, rankOne_mulVec, dotProduct_add, dotProduct_smul,
          dotProduct_smul, dotProduct_comm u f, smul_eq_mul, smul_eq_mul, sq]
  have ha : 0 ≤ f ⬝ᵥ u := by nlinarith [sq_nonneg (f ⬝ᵥ u)]
  refine ⟨ha, mul_nonneg hw ha, ?_⟩
  have hs : (w * (f ⬝ᵥ u)) ^ 2 ≤ w * (f ⬝ᵥ u) := by
    have : w * (w * (f ⬝ᵥ u) ^ 2) ≤ w * (f ⬝ᵥ u) := mul_le_mul_of_nonneg_left (by linarith) hw
    nlinarith
  nlinarith [mul_nonneg hw ha]

/-- [proved-derived; formal-checked] **The one-sample gain is positive** when `w > 0` and `f ≠ 0`. -/
theorem gain_pos {H : Matrix σ σ ℝ} (hH : H.PosSemidef) {w : ℝ} (hw : 0 < w) (f u : σ → ℝ)
    (hf : f ≠ 0) (hu : (H + w • vecMulVec f f) *ᵥ u = f) : 0 < w * (f ⬝ᵥ u) := by
  obtain ⟨ha, -, -⟩ := gain_mem_unit hH hw.le f u hu
  refine mul_pos hw (lt_of_le_of_ne ha fun h0 => hf ?_)
  have hq : u ⬝ᵥ H *ᵥ u = 0 := by
    have key : f ⬝ᵥ u = u ⬝ᵥ ((H + w • vecMulVec f f) *ᵥ u) := by rw [hu, dotProduct_comm]
    rw [add_mulVec, Matrix.smul_mulVec, rankOne_mulVec, dotProduct_add, ← h0, zero_smul,
      smul_zero, dotProduct_zero, add_zero] at key
    exact key.symm
  have hHu : H *ᵥ u = 0 := (hH.dotProduct_mulVec_zero_iff u).mp (by simpa using hq)
  rw [← hu, add_mulVec, hHu, Matrix.smul_mulVec, rankOne_mulVec, ← h0, zero_smul, smul_zero,
    zero_add]

/-- [definition] **The one-sample gain** at the solved chart, `s = w ⟨f, (H + w f fᵀ)⁻¹ f⟩`. -/
def sampleGain [DecidableEq σ] (H : Matrix σ σ ℝ) (w : ℝ) (f : σ → ℝ) : ℝ :=
  w * (f ⬝ᵥ ((H + w • vecMulVec f f)⁻¹ *ᵥ f))

variable [DecidableEq σ]

/-- [proved-standard; formal-checked] The solved chart solves: `H′ (H′⁻¹ f) = f` for invertible `H′`. -/
theorem solve_mulVec {H' : Matrix σ σ ℝ} (hunit : IsUnit H'.det) (f : σ → ℝ) :
    H' *ᵥ (H'⁻¹ *ᵥ f) = f := by
  rw [mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit, one_mulVec]

/-- [proved-derived; formal-checked] **One sample's exogenous step stays under the chord**: at the
solved chart its gain `s` lies in `[0, 1]`, it moves the logits to `W f + s (χ − W f)`, and
`ℓ_t(W′ f) ≤ (1 − s) ℓ_t(W f) + s ℓ_t(χ)`. -/
theorem exogenous_one_sample_descends {Index : Type*} [Fintype Index] [Nonempty Index]
    [DecidableEq Index] (W : Matrix Index σ ℝ) {H : Matrix σ σ ℝ} (hH : H.PosSemidef) {w : ℝ}
    (hw : 0 ≤ w) (f : σ → ℝ) (χ : Index → ℝ) (t : Index)
    (hunit : IsUnit (H + w • vecMulVec f f).det) :
    0 ≤ sampleGain H w f ∧ sampleGain H w f ≤ 1 ∧
      exogenousStep W (w • vecMulVec f f) (w • vecMulVec χ f) (H + w • vecMulVec f f)⁻¹ *ᵥ f =
        W *ᵥ f + sampleGain H w f • (χ - W *ᵥ f) ∧
      codeLength (exogenousStep W (w • vecMulVec f f) (w • vecMulVec χ f)
          (H + w • vecMulVec f f)⁻¹ *ᵥ f) t ≤
        (1 - sampleGain H w f) * codeLength (W *ᵥ f) t + sampleGain H w f * codeLength χ t := by
  obtain ⟨-, h0, h1⟩ := gain_mem_unit hH hw f _ (solve_mulVec hunit f)
  have hstep := exogenousStep_one_sample W w f χ (H + w • vecMulVec f f)⁻¹
  refine ⟨h0, h1, hstep, ?_⟩
  rw [hstep]
  exact codeLength_segment_le χ (W *ᵥ f) t h0 h1

/-- [proved-derived; formal-checked] **One sample's exogenous step descends strictly** where `χ`
codes the target better than `W f`, with `w > 0` and `f ≠ 0`. -/
theorem exogenous_one_sample_strict {Index : Type*} [Fintype Index] [Nonempty Index]
    [DecidableEq Index] (W : Matrix Index σ ℝ) {H : Matrix σ σ ℝ} (hH : H.PosSemidef) {w : ℝ}
    (hw : 0 < w) (f : σ → ℝ) (hf : f ≠ 0) (χ : Index → ℝ) (t : Index)
    (hunit : IsUnit (H + w • vecMulVec f f).det) (h : codeLength χ t < codeLength (W *ᵥ f) t) :
    0 < sampleGain H w f ∧
      codeLength (exogenousStep W (w • vecMulVec f f) (w • vecMulVec χ f)
        (H + w • vecMulVec f f)⁻¹ *ᵥ f) t < codeLength (W *ᵥ f) t := by
  have hpos := gain_pos hH hw f _ hf (solve_mulVec hunit f)
  obtain ⟨-, -, -, hle⟩ := exogenous_one_sample_descends W hH hw.le f χ t hunit
  refine ⟨hpos, ?_⟩
  have : sampleGain H w f * codeLength χ t < sampleGain H w f * codeLength (W *ᵥ f) t :=
    mul_lt_mul_of_pos_left h hpos
  linarith

/-- [proved-derived; formal-checked] **The receiving locus's deposit on one reached comparison** is
the exogenous step at the code face, `F = w f fᵀ`, `T = w χ_R(T) fᵀ`, `X = (H + F)⁻¹`. -/
theorem exogenousDeposit_one_sample {Index : Type*} [DecidableEq Index]
    (θ : LocusState ℝ σ Index) (m : ℕ) (w : ℝ) (f : σ → ℝ) (t : Index) :
    (exogenousDeposit θ (targetWindow m [(w, f, t)])).map =
      exogenousStep θ.map (w • vecMulVec f f) (w • vecMulVec (codeFace m t) f)
        (θ.gram + w • vecMulVec f f)⁻¹ := by
  simp [exogenousDeposit, targetWindow, windowGram, windowCovector]

/-- [proved-derived; formal-checked] **The deposit on one reached comparison descends the scored
face** under the margin law, wherever the face codes the target in more than one grain. -/
theorem exogenousDeposit_codeFace_descends {Index : Type*} [Fintype Index] [Nonempty Index]
    [DecidableEq Index] (θ : LocusState ℝ σ Index) (hH : θ.gram.PosSemidef) {L m : ℕ}
    (hL : 0 < L) (hm : MarginCodes (Fintype.card Index) L m) {w : ℝ} (hw : 0 < w) (f : σ → ℝ)
    (hf : f ≠ 0) (t : Index) (hunit : IsUnit (θ.gram + w • vecMulVec f f).det)
    (hz : 1 / (L : ℝ) < codeLength (θ.map *ᵥ f) t) :
    (exogenousDeposit θ (targetWindow m [(w, f, t)])).map *ᵥ f =
        θ.map *ᵥ f + sampleGain θ.gram w f • ((codeFace m t : Index → ℝ) - θ.map *ᵥ f) ∧
      0 < sampleGain θ.gram w f ∧ sampleGain θ.gram w f ≤ 1 ∧
      codeLength ((exogenousDeposit θ (targetWindow m [(w, f, t)])).map *ᵥ f) t <
        codeLength (θ.map *ᵥ f) t := by
  have hcode := (margin_rule_codeLength hL m t).mp hm
  rw [exogenousDeposit_one_sample]
  obtain ⟨-, h1, hstep, -⟩ :=
    exogenous_one_sample_descends θ.map hH hw.le f (codeFace m t) t hunit
  obtain ⟨hpos, hlt⟩ := exogenous_one_sample_strict θ.map hH hw f hf (codeFace m t) t hunit
    (by linarith)
  exact ⟨hstep, hpos, h1, hlt⟩

end Exogenous

/-! ## 7–8. The witnesses -/

section Witness

/-- [proved-derived; formal-checked] The smooth face of `(0, 0, 1)` is `(1/4, 1/4, 1/2)`. -/
theorem smoothFace_witness : smoothFace (![0, 0, 1] : Fin 3 → ℝ) = ![1 / 4, 1 / 4, 1 / 2] := by
  ext c
  fin_cases c <;> simp [smoothFace, Fin.sum_univ_three] <;> norm_num

/-- [counterexample; formal-checked] **The innovation is not the covector**: at `z = (0, 0, 1)`,
`t = 0`, `m = 2`, neither `χ − z = (2, 0, −1)` nor `q − p(z) = (3/4, −1/4, −1/2)` is a multiple of the
other, and their pairing is `2 > 0`. -/
theorem innovation_is_not_the_covector :
    (¬ ∃ a : ℝ, (codeFace 2 0 : Fin 3 → ℝ) - ![0, 0, 1] =
        a • (Pi.single 0 1 - smoothFace (![0, 0, 1] : Fin 3 → ℝ))) ∧
      (¬ ∃ a : ℝ, Pi.single 0 1 - smoothFace (![0, 0, 1] : Fin 3 → ℝ) =
        a • ((codeFace 2 0 : Fin 3 → ℝ) - ![0, 0, 1])) ∧
      (Pi.single 0 1 - smoothFace (![0, 0, 1] : Fin 3 → ℝ)) ⬝ᵥ
        ((codeFace 2 0 : Fin 3 → ℝ) - ![0, 0, 1]) = 2 := by
  have hχ : (codeFace 2 0 : Fin 3 → ℝ) - ![0, 0, 1] = ![2, 0, -1] := by
    ext c
    fin_cases c <;> simp [codeFace]
  have hq : (Pi.single 0 1 : Fin 3 → ℝ) - smoothFace ![0, 0, 1] = ![3 / 4, -1 / 4, -1 / 2] := by
    rw [smoothFace_witness]
    ext c
    fin_cases c <;> simp <;> norm_num
  rw [hχ, hq]
  refine ⟨fun ⟨a, ha⟩ => ?_, fun ⟨a, ha⟩ => ?_, ?_⟩
  · have h0 := congrFun ha 0
    have h1 := congrFun ha 1
    simp at h0 h1
    rw [h1] at h0
    norm_num at h0
  · have h0 := congrFun ha 0
    have h1 := congrFun ha 1
    simp at h0 h1
  · simp [dotProduct, Fin.sum_univ_three]
    norm_num

/-- [proved-derived; formal-checked] The smooth face of `(0, 0, −1)` is `(2/5, 2/5, 1/5)`. -/
theorem smoothFace_window : smoothFace (![0, 0, -1] : Fin 3 → ℝ) = ![2 / 5, 2 / 5, 1 / 5] := by
  ext c
  fin_cases c <;> simp [smoothFace, Fin.sum_univ_three, Real.rpow_neg_one] <;> norm_num

/-- [counterexample; formal-checked] **Each sample of the window, alone, is descended**: at the
locus `W = (0, 0, −1)ᵀ`, prior Gram `1`, one feature `f = 1` and margin `1` (which codes three classes
at grain `1`), the deposit on either sample alone lowers that sample's scored face. -/
theorem window_samples_alone_descend (t : Fin 3) :
    codeLength ((exogenousDeposit (⟨!![0; 0; -1], 1, !![0; 0; -1]⟩ : LocusState ℝ (Fin 1) (Fin 3))
        (targetWindow 1 [(1, ![1], t)])).map *ᵥ ![1]) t <
      codeLength ((!![0; 0; -1] : Matrix (Fin 3) (Fin 1) ℝ) *ᵥ ![1]) t := by
  have hm : MarginCodes (Fintype.card (Fin 3)) 1 1 := by
    rw [Fintype.card_fin]; unfold MarginCodes; decide
  have hunit : IsUnit ((1 : Matrix (Fin 1) (Fin 1) ℝ) + (1 : ℝ) • vecMulVec ![1] ![1]).det := by
    rw [isUnit_iff_ne_zero, Matrix.det_fin_one]
    norm_num [vecMulVec]
  have hz : 1 / ((1 : ℕ) : ℝ) <
      codeLength ((!![0; 0; -1] : Matrix (Fin 3) (Fin 1) ℝ) *ᵥ ![1]) t := by
    have hv : (!![0; 0; -1] : Matrix (Fin 3) (Fin 1) ℝ) *ᵥ ![1] = ![0, 0, -1] := by
      ext i; fin_cases i <;> simp [mulVec, dotProduct]
    have h : (1 : ℝ) < Real.logb 2 (1 + 1 + 2⁻¹) := by
      rw [Real.lt_logb_iff_rpow_lt (by norm_num) (by norm_num)]; norm_num
    rw [hv]
    fin_cases t <;> simp [codeLength, Fin.sum_univ_three, Real.rpow_neg_one] <;> linarith
  exact (exogenousDeposit_codeFace_descends _ Matrix.PosSemidef.one one_pos hm one_pos ![1]
    (fun h => by simpa using congrFun h 0) t hunit hz).2.2.2

/-- [counterexample; formal-checked] **A window's step can raise the summed scored face at first
order**: the same locus deposits two samples on one feature, targets `0` and `1`, at margin `1`; its
map moves to `(1/3, 1/3, −1/3)ᵀ`, and along that move the window's summed face rises at rate `2/15`. -/
theorem window_first_order_rise :
    MarginCodes 3 1 1 ∧
      (!![0; 0; -1] : Matrix (Fin 3) (Fin 1) ℝ) * (1 : Matrix (Fin 1) (Fin 1) ℝ) = !![0; 0; -1] ∧
      (exogenousDeposit (⟨!![0; 0; -1], 1, !![0; 0; -1]⟩ : LocusState ℝ (Fin 1) (Fin 3))
          (targetWindow 1 [(1, ![1], 0), (1, ![1], 1)])).map = !![1 / 3; 1 / 3; -1 / 3] ∧
      HasDerivAt (fun s : ℝ =>
          codeLength ((!![0; 0; -1] + s • (!![1 / 3; 1 / 3; -1 / 3] - !![0; 0; -1]) :
            Matrix (Fin 3) (Fin 1) ℝ) *ᵥ ![1]) 0 +
          codeLength ((!![0; 0; -1] + s • (!![1 / 3; 1 / 3; -1 / 3] - !![0; 0; -1]) :
            Matrix (Fin 3) (Fin 1) ℝ) *ᵥ ![1]) 1) (2 / 15) 0 := by
  refine ⟨by unfold MarginCodes; decide, by simp, ?_, ?_⟩
  · have hG : windowGram (targetWindow 1 [((1 : ℝ), (![1] : Fin 1 → ℝ), (0 : Fin 3)),
        (1, ![1], 1)]) = !![2] := by
      ext i j; fin_cases i; fin_cases j
      simp [targetWindow, windowGram]; norm_num
    have hT : windowCovector (targetWindow 1 [((1 : ℝ), (![1] : Fin 1 → ℝ), (0 : Fin 3)),
        (1, ![1], 1)]) = !![1; 1; 0] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [targetWindow, windowCovector, codeFace]
    have hinv : ((1 : Matrix (Fin 1) (Fin 1) ℝ) + !![2])⁻¹ = !![1 / 3] := by
      apply Matrix.inv_eq_left_inv
      ext i j; fin_cases i; fin_cases j; simp [vecMul, dotProduct]; norm_num
    simp only [exogenousDeposit, hG, hT, hinv]
    ext i j; fin_cases i <;> fin_cases j <;> norm_num [exogenousStep]
  · have hv : ∀ s : ℝ, ((!![0; 0; -1] + s • (!![1 / 3; 1 / 3; -1 / 3] - !![0; 0; -1]) :
        Matrix (Fin 3) (Fin 1) ℝ) *ᵥ ![1]) =
          (![0, 0, -1] : Fin 3 → ℝ) + s • ![1 / 3, 1 / 3, 2 / 3] := by
      intro s
      ext i
      fin_cases i <;> norm_num [mulVec, dotProduct]
    simp only [hv]
    have h0 := hasDerivAt_codeLength (![0, 0, -1] : Fin 3 → ℝ) ![1 / 3, 1 / 3, 2 / 3] 0
    have h1 := hasDerivAt_codeLength (![0, 0, -1] : Fin 3 → ℝ) ![1 / 3, 1 / 3, 2 / 3] 1
    refine (h0.add h1).congr_deriv ?_
    rw [smoothFace_window]
    simp [dotProduct, Fin.sum_univ_three]
    norm_num

end Witness

end Holonics.HNN.TargetFaceDescent
