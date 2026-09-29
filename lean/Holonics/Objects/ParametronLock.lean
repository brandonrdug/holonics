import Holonics.Objects.Parametron
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
# The parametron's lock: an Ising site, its exchange polynomial, its winding and its hearing

[definition] Object 5 of `docs/ELEMENTARY_OBJECTS.md`, re-derived from its constitution (September
29). `Objects/Parametron` owns the storage↔flow exchange, the tick as a clock and the locked-sheet
face (the perceptron). This module owns the **lock's receiver faces**: what a two-sheet lock reads
under a bias, what a population of locks can separate, how the count of flipped locks is a winding,
how coupling moves the pivots, and when a mode is heard.

1. **The exchange polynomial of one lock.** [definition] A two-sheet lock whose biased sheet
   carries the weight `a` against its resting sheet's `K` has the exchange polynomial
   `Π(a) = 1 + a/K` (its partition function read at the resting sheet) and the face
   `θ = a/(a + K)`, the biased sheet's share. [proved-derived; formal-checked] `θ = a Π′/Π`
   (`exchange_hasDerivAt`, `lockFace_eq_bias_logDeriv`); `θ` is the logistic of the log-bias,
   `θ = 1/(1 + e^{−(ln a − ln K)})` (`lockFace_logistic`); its susceptibility is
   `a ∂_a θ = θ(1 − θ) ≤ 1/4` (`lockFace_hasDerivAt`, `bias_susceptibility`,
   `susceptibility_le_quarter`, `lock_susceptibility_le_quarter`). The threshold (the perceptron)
   is this face at zero temperature.
2. **Many locks.** [proved-derived; formal-checked] `N` independent locks have
   `Π(a) = ∏_i (1 + a/K_i)`, whose zeros are exactly the pivots `a = −K_i`
   (`exchangeN_eq_zero_iff`).
3. **Capacity is lock count, not coordinate count.** [proved-derived; formal-checked] Two biases'
   responses have the ratio `S = Π(a₂)/Π(a₁) = ∏_i (a₂ + K_i)/(a₁ + K_i)`
   (`selectivity_eq_exchange_ratio`): each factor is the cross ratio of the two biases about the
   pivot `−K_i` with `∞`, and lies strictly between `1` and `a₂/a₁` (`pivotRatio_between`,
   `pivotRatio_between'`), so `S` lies strictly between `1` and `(a₂/a₁)^N`
   (`selectivity_lock_count_bound`, `selectivity_lock_count_bound'`). The form
   `(a₂/a₁)^N < S < (a₁/a₂)^N` is the case `a₂ < a₁`, where the sharper upper bound is `1`.
4. **The winding is the carry.** [proved-standard; formal-checked] `Π′/Π = Σ_i (a + K_i)⁻¹`
   (`logDeriv_exchangeC`), and on the circle `|a| = r` (no pivot on it) the winding
   `(2πi)⁻¹ ∮ Σ_i (a + K_i)⁻¹ da` is the number of pivots inside, `#{i : K_i < r}`
   (`pivot_winding_inside`, `pivot_winding_outside`, `winding_is_carry`): as the bias's magnitude
   passes each pivot, one more lock has flipped, and that count is the carry (the argument
   principle, read on the locks).
5. **Coupled locks (Lee–Yang).** [proved-derived; formal-checked] Two locks with exchange weight
   `y = e^{−2w}` have `Π(a) = a² + 2ya + 1` (the four sheet pairs `(+,+), (+,−), (−,+), (−,−)` with
   weights `1, ya, ya, a²`). Uncoupled (`y = 1`) it is `(1 + a)²`, a double pivot on the negative
   real axis (`uncoupled_double_pivot`); coupled ferromagnetically (`|y| < 1`) both zeros leave the
   axis for the unit circle (`coupled_zeros_leave_the_axis`). This is the coupled-sheet parametron.
6. **Modal hearing is dormancy.** [proved-derived; formal-checked] A mode `v` carries a source `s`
   to a receiver `r` with the port coefficient `c = ⟨s, M v⟩⟨r, v⟩`; the mode is silent exactly
   when one of its two couplings vanishes (`modal_silent_iff`), and a constitutive change that
   moves the mode reopens a silent one (`dormant_mode_reopens`): the dormant mode waiting for a
   fitting antecedent.

[open] The spectral expansion `rᵀ(K − λM)⁻¹Ms = Σ_v c_v/(λ_v − λ)` for `M`-orthonormal modes is
standard and not restated here (#62). The identification of the pumped ring's lock with a
Boltzmann site at a declared temperature is an interpretation, not a theorem.

No `sorry`, no `axiom`, no `native_decide`; the audit block at the end prints the axioms.
-/

noncomputable section

namespace Holonics.Objects.ParametronLock

open scoped BigOperators Real
open Complex Matrix Metric

/-! ## 1. The exchange polynomial of one lock -/

section OneLock

/-- [definition] **The exchange polynomial of a two-sheet lock**: `Π(a) = 1 + a/K`, the partition
function of the lock's two sheets read at the resting sheet (weight `K`) under the bias `a`. -/
def exchange (K a : ℝ) : ℝ := 1 + a / K

/-- [definition] **The lock's face**: the biased sheet's share `θ = a/(a + K)`. -/
def lockFace (K a : ℝ) : ℝ := a / (a + K)

/-- [proved-derived; formal-checked] The exchange polynomial's derivative in the bias is `1/K`. -/
theorem exchange_hasDerivAt (K a : ℝ) : HasDerivAt (exchange K) (1 / K) a := by
  show HasDerivAt (fun x => 1 + x / K) (1 / K) a
  simpa using ((hasDerivAt_id a).div_const K).const_add 1

/-- [proved-derived; formal-checked] **The face is the bias times the logarithmic derivative**:
`θ = a Π′/Π`. -/
theorem lockFace_eq_bias_logDeriv {K a : ℝ} (hK : K ≠ 0) (haK : a + K ≠ 0) :
    lockFace K a = a * (1 / K) / exchange K a := by
  have hEx : exchange K a = (a + K) / K := by
    unfold exchange; field_simp; ring
  rw [hEx, lockFace]
  field_simp

/-- [proved-derived; formal-checked] **The logistic face of the log-bias**:
`θ = 1/(1 + e^{−(ln a − ln K)})` for positive bias and resting weight. -/
theorem lockFace_logistic {K a : ℝ} (ha : 0 < a) (hK : 0 < K) :
    lockFace K a = 1 / (1 + Real.exp (-(Real.log a - Real.log K))) := by
  have he : Real.exp (-(Real.log a - Real.log K)) = K / a := by
    rw [neg_sub, Real.exp_sub, Real.exp_log hK, Real.exp_log ha]
  rw [he, lockFace]
  have : a + K ≠ 0 := by positivity
  field_simp

/-- [proved-derived; formal-checked] The face's derivative in the bias: `∂_a θ = K/(a + K)²`. -/
theorem lockFace_hasDerivAt (K : ℝ) {a : ℝ} (haK : a + K ≠ 0) :
    HasDerivAt (lockFace K) (K / (a + K) ^ 2) a := by
  have h := (hasDerivAt_id a).div ((hasDerivAt_id a).add_const K) (by simpa using haK)
  have e : (1 * (id a + K) - id a * 1) / (id a + K) ^ 2 = K / (a + K) ^ 2 := by simp [id]
  rw [e] at h
  exact h

/-- [proved-derived; formal-checked] **The lock's susceptibility** is `a ∂_a θ = θ(1 − θ)`. -/
theorem bias_susceptibility {K a : ℝ} (haK : a + K ≠ 0) :
    a * (K / (a + K) ^ 2) = lockFace K a * (1 - lockFace K a) := by
  unfold lockFace
  field_simp
  ring

/-- [proved-standard; formal-checked] `θ(1 − θ) ≤ 1/4` for every real `θ`. -/
theorem susceptibility_le_quarter (θ : ℝ) : θ * (1 - θ) ≤ 1 / 4 := by
  nlinarith [sq_nonneg (θ - 1 / 2)]

/-- [proved-derived; formal-checked] **The lock's susceptibility is at most a quarter**:
`a ∂_a θ ≤ 1/4`. -/
theorem lock_susceptibility_le_quarter {K a : ℝ} (haK : a + K ≠ 0) :
    a * (K / (a + K) ^ 2) ≤ 1 / 4 := by
  rw [bias_susceptibility haK]
  exact susceptibility_le_quarter _

end OneLock

/-! ## 2. Many locks and their pivots -/

section ManyLocks

/-- [definition] **The exchange polynomial of `N` independent locks**: `Π(a) = ∏_i (1 + a/K_i)`. -/
def exchangeN {N : ℕ} (K : Fin N → ℝ) (a : ℝ) : ℝ := ∏ i, (1 + a / K i)

/-- [proved-derived; formal-checked] **The zeros are the pivots**: `Π(a) = 0 ⇔ a = −K_i` for some
lock `i`. -/
theorem exchangeN_eq_zero_iff {N : ℕ} {K : Fin N → ℝ} (hK : ∀ i, K i ≠ 0) (a : ℝ) :
    exchangeN K a = 0 ↔ ∃ i, a = -K i := by
  unfold exchangeN
  rw [Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨i, -, hi⟩
    refine ⟨i, ?_⟩
    have hKi := hK i
    have : K i + a = 0 := by
      field_simp at hi
      linarith
    linarith
  · rintro ⟨i, rfl⟩
    refine ⟨i, Finset.mem_univ _, ?_⟩
    rw [neg_div, div_self (hK i)]
    ring

/-- [definition] **A pivot's ratio**: `(a₂ + K)/(a₁ + K)`, the cross ratio of the two biases
`a₂, a₁` about the pivot `−K` and `∞`. -/
def pivotRatio (K a₁ a₂ : ℝ) : ℝ := (a₂ + K) / (a₁ + K)

/-- [definition] **The selectivity** of `N` locks between two biases: the product of the pivots'
ratios. -/
def selectivity {N : ℕ} (K : Fin N → ℝ) (a₁ a₂ : ℝ) : ℝ := ∏ i, pivotRatio (K i) a₁ a₂

/-- [proved-derived; formal-checked] **Selectivity is the exchange ratio**:
`S = Π(a₂)/Π(a₁)`, a product of cross ratios about the pivots. -/
theorem selectivity_eq_exchange_ratio {N : ℕ} {K : Fin N → ℝ} (hK : ∀ i, 0 < K i) {a₁ : ℝ}
    (ha₁ : 0 < a₁) (a₂ : ℝ) :
    selectivity K a₁ a₂ = exchangeN K a₂ / exchangeN K a₁ := by
  unfold selectivity exchangeN
  rw [← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hKi := hK i
  have hKi' : K i ≠ 0 := hKi.ne'
  have h1 : a₁ + K i ≠ 0 := by positivity
  have e₂ : 1 + a₂ / K i = (a₂ + K i) / K i := by field_simp; ring
  have e₁ : 1 + a₁ / K i = (a₁ + K i) / K i := by field_simp; ring
  rw [e₂, e₁, pivotRatio, div_div_div_cancel_right₀ hKi']

/-- [proved-derived; formal-checked] **A pivot's ratio lies between one and the bias ratio**
(decreasing bias): for `K > 0` and `0 < a₂ < a₁`, `a₂/a₁ < (a₂ + K)/(a₁ + K) < 1`. -/
theorem pivotRatio_between {K a₁ a₂ : ℝ} (hK : 0 < K) (ha₂ : 0 < a₂) (h : a₂ < a₁) :
    a₂ / a₁ < pivotRatio K a₁ a₂ ∧ pivotRatio K a₁ a₂ < 1 := by
  have ha₁ : 0 < a₁ := ha₂.trans h
  have hd : 0 < a₁ + K := by positivity
  unfold pivotRatio
  constructor
  · rw [div_lt_div_iff₀ ha₁ hd]
    nlinarith
  · rw [div_lt_one hd]
    linarith

/-- [proved-derived; formal-checked] The mirror (increasing bias): for `K > 0` and `0 < a₁ < a₂`,
`1 < (a₂ + K)/(a₁ + K) < a₂/a₁`. -/
theorem pivotRatio_between' {K a₁ a₂ : ℝ} (hK : 0 < K) (ha₁ : 0 < a₁) (h : a₁ < a₂) :
    1 < pivotRatio K a₁ a₂ ∧ pivotRatio K a₁ a₂ < a₂ / a₁ := by
  have hd : 0 < a₁ + K := by positivity
  unfold pivotRatio
  constructor
  · rw [one_lt_div hd]
    linarith
  · rw [div_lt_div_iff₀ hd ha₁]
    nlinarith

/-- [proved-derived; formal-checked] **Capacity is lock count** (decreasing bias): for `N ≥ 1`
locks with positive resting weights and `0 < a₂ < a₁`, `(a₂/a₁)^N < S < 1`. The primary form
`(a₂/a₁)^N < S < (a₁/a₂)^N` is this case, with the sharper upper bound `1`. -/
theorem selectivity_lock_count_bound {N : ℕ} (hN : 1 ≤ N) {K : Fin N → ℝ} (hK : ∀ i, 0 < K i)
    {a₁ a₂ : ℝ} (ha₂ : 0 < a₂) (h : a₂ < a₁) :
    (a₂ / a₁) ^ N < selectivity K a₁ a₂ ∧ selectivity K a₁ a₂ < 1 := by
  have hne : (Finset.univ : Finset (Fin N)).Nonempty := ⟨⟨0, hN⟩, Finset.mem_univ _⟩
  have ha₁ : 0 < a₁ := ha₂.trans h
  constructor
  · have hc : (a₂ / a₁) ^ N = ∏ _i : Fin N, a₂ / a₁ := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [hc]
    exact Finset.prod_lt_prod_of_nonempty (fun _ _ => by positivity)
      (fun i _ => (pivotRatio_between (hK i) ha₂ h).1) hne
  · have hc : (1 : ℝ) = ∏ _i : Fin N, (1 : ℝ) := by simp
    rw [hc]
    refine Finset.prod_lt_prod_of_nonempty (fun i _ => ?_)
      (fun i _ => (pivotRatio_between (hK i) ha₂ h).2) hne
    have := hK i
    unfold pivotRatio
    positivity

/-- [proved-derived; formal-checked] **Capacity is lock count** (increasing bias): for `N ≥ 1`
locks and `0 < a₁ < a₂`, `1 < S < (a₂/a₁)^N`. -/
theorem selectivity_lock_count_bound' {N : ℕ} (hN : 1 ≤ N) {K : Fin N → ℝ} (hK : ∀ i, 0 < K i)
    {a₁ a₂ : ℝ} (ha₁ : 0 < a₁) (h : a₁ < a₂) :
    1 < selectivity K a₁ a₂ ∧ selectivity K a₁ a₂ < (a₂ / a₁) ^ N := by
  have hne : (Finset.univ : Finset (Fin N)).Nonempty := ⟨⟨0, hN⟩, Finset.mem_univ _⟩
  constructor
  · have hc : (1 : ℝ) = ∏ _i : Fin N, (1 : ℝ) := by simp
    rw [hc]
    exact Finset.prod_lt_prod_of_nonempty (fun _ _ => one_pos)
      (fun i _ => (pivotRatio_between' (hK i) ha₁ h).1) hne
  · have hc : (a₂ / a₁) ^ N = ∏ _i : Fin N, a₂ / a₁ := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [hc]
    refine Finset.prod_lt_prod_of_nonempty (fun i _ => ?_)
      (fun i _ => (pivotRatio_between' (hK i) ha₁ h).2) hne
    have := hK i
    have ha₂ : 0 < a₂ := ha₁.trans h
    unfold pivotRatio
    positivity

end ManyLocks

/-! ## 3. The winding is the carry -/

section Winding

/-- [definition] **The exchange polynomial over the complex bias**: `Π(z) = ∏_i (1 + z/K_i)`. -/
def exchangeC {N : ℕ} (K : Fin N → ℂ) (z : ℂ) : ℂ := ∏ i, (1 + z / K i)

/-- [proved-standard; formal-checked] **The logarithmic derivative of the locks' exchange
polynomial** is the sum over the pivots: `Π′/Π = Σ_i (z + K_i)⁻¹`, off the pivots. -/
theorem logDeriv_exchangeC {N : ℕ} {K : Fin N → ℂ} (hK : ∀ i, K i ≠ 0) {z : ℂ}
    (hz : ∀ i, z ≠ -K i) : logDeriv (exchangeC K) z = ∑ i, (z + K i)⁻¹ := by
  have hzK : ∀ i, z + K i ≠ 0 := fun i h => hz i (by linear_combination h)
  have key : ∀ i, logDeriv (fun w : ℂ => 1 + w / K i) z = (z + K i)⁻¹ := by
    intro i
    have hd : HasDerivAt (fun w : ℂ => 1 + w / K i) (1 / K i) z := by
      simpa using ((hasDerivAt_id z).div_const (K i)).const_add 1
    rw [logDeriv_apply, hd.deriv]
    have hKi := hK i
    have e : (z + K i) / K i = 1 + z / K i := by rw [add_div, div_self hKi, add_comm]
    rw [← e, div_div_div_cancel_right₀ hKi, one_div]
  have hf : ∀ i ∈ (Finset.univ : Finset (Fin N)), (fun w : ℂ => 1 + w / K i) z ≠ 0 := by
    intro i _
    have hKi := hK i
    have hzi := hzK i
    simp only
    intro h
    apply hzi
    field_simp at h
    linear_combination h
  have hd : ∀ i ∈ (Finset.univ : Finset (Fin N)),
      DifferentiableAt ℂ (fun w : ℂ => 1 + w / K i) z := by
    intro i _
    exact ((differentiableAt_id.div_const (K i)).const_add 1)
  have h := logDeriv_prod (s := Finset.univ) (f := fun i w => 1 + w / K i) (x := z) hf hd
  simp only [key] at h
  exact h

/-- [proved-standard; formal-checked] **A pivot inside the circle winds once**:
`∮_{|z| = r} (z − w)⁻¹ dz = 2πi` for `|w| < r`. -/
theorem pivot_winding_inside {w : ℂ} {r : ℝ} (hw : ‖w‖ < r) :
    (∮ z in C(0, r), (z - w)⁻¹) = 2 * π * I :=
  circleIntegral.integral_sub_inv_of_mem_ball (by simpa [Metric.mem_ball, dist_zero_right] using hw)

/-- [proved-standard; formal-checked] **A pivot outside the circle does not wind**:
`∮_{|z| = r} (z − w)⁻¹ dz = 0` for `r < |w|`. -/
theorem pivot_winding_outside {w : ℂ} {r : ℝ} (hr : 0 ≤ r) (hw : r < ‖w‖) :
    (∮ z in C(0, r), (z - w)⁻¹) = 0 := by
  have hne : ∀ z ∈ closedBall (0 : ℂ) r, z - w ≠ 0 := by
    intro z hz h
    have hz' : ‖z‖ ≤ r := by simpa [Metric.mem_closedBall, dist_zero_right] using hz
    rw [sub_eq_zero] at h
    rw [h] at hz'
    linarith
  refine Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hr
    Set.countable_empty ?_ ?_
  · exact ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const) hne
  · intro z hz
    exact (differentiableAt_id.sub_const w).inv
      (hne z (Metric.ball_subset_closedBall hz.1))

/-- [proved-standard; formal-checked] **The winding is the carry** (the argument principle on the
locks): on the circle `|a| = r`, with every pivot `−K_i` off it (`K_i ≠ r`),
`(2πi)⁻¹ ∮ Σ_i (a + K_i)⁻¹ da = #{i : K_i < r}`, the number of locks the bias has flipped. -/
theorem winding_is_carry {N : ℕ} {K : Fin N → ℝ} (hK : ∀ i, 0 < K i) {r : ℝ} (hr : 0 < r)
    (hKr : ∀ i, K i ≠ r) :
    (2 * π * I)⁻¹ * (∮ z in C(0, r), ∑ i, (z + (K i : ℂ))⁻¹) =
      ((Finset.univ.filter (fun i => K i < r)).card : ℂ) := by
  have hnorm : ∀ i, ‖-(K i : ℂ)‖ = K i := by
    intro i
    rw [norm_neg, Complex.norm_real, Real.norm_of_nonneg (hK i).le]
  have hfun : (fun z : ℂ => ∑ i, (z + (K i : ℂ))⁻¹) =
      fun z : ℂ => ∑ i, (z - (-(K i : ℂ)))⁻¹ := by
    funext z
    simp only [sub_neg_eq_add]
  have hint : ∀ i ∈ (Finset.univ : Finset (Fin N)),
      CircleIntegrable (fun z : ℂ => (z - (-(K i : ℂ)))⁻¹) 0 r := by
    intro i _
    rw [circleIntegrable_sub_inv_iff]
    right
    rw [Metric.mem_sphere, dist_zero_right, hnorm, abs_of_pos hr]
    exact hKr i
  have hterm : ∀ i, (∮ z in C(0, r), (z - (-(K i : ℂ)))⁻¹) =
      2 * π * I * (if K i < r then 1 else 0) := by
    intro i
    split_ifs with hlt
    · rw [mul_one]
      exact pivot_winding_inside (by rw [hnorm]; exact hlt)
    · rw [mul_zero]
      have hgt : r < K i := lt_of_le_of_ne (not_lt.mp hlt) (hKr i).symm
      exact pivot_winding_outside hr.le (by rw [hnorm]; exact hgt)
  rw [hfun, circleIntegral.integral_fun_sum hint]
  simp only [hterm]
  rw [← Finset.mul_sum, ← mul_assoc, inv_mul_cancel₀ Complex.two_pi_I_ne_zero, one_mul,
    Finset.sum_boole]

end Winding

/-! ## 4. Coupled locks move the pivots (Lee–Yang) -/

section Coupled

/-- [definition] **The exchange polynomial of two coupled locks** at the fugacity `a` with exchange
weight `y = e^{−2w}`: the sheet pairs `(+,+), (+,−), (−,+), (−,−)` carry the weights
`1, ya, ya, a²`, so `Π(a) = a² + 2ya + 1`. -/
def coupledExchange (y : ℝ) (a : ℂ) : ℂ := a ^ 2 + 2 * y * a + 1

/-- [proved-derived; formal-checked] **Uncoupled, the pair has a double pivot at `−1`**, on the
negative real axis: `Π(a) = (a + 1)²` at `y = 1`. -/
theorem uncoupled_double_pivot (a : ℂ) : coupledExchange 1 a = (a + 1) ^ 2 := by
  unfold coupledExchange
  push_cast
  ring

/-- [proved-derived; formal-checked] **Coupled locks leave the axis** (Lee–Yang for two sites):
with `|y| < 1` every zero of `a² + 2ya + 1` lies on the unit circle, off the real axis. -/
theorem coupled_zeros_leave_the_axis {y : ℝ} (hy : |y| < 1) {a : ℂ}
    (ha : coupledExchange y a = 0) : ‖a‖ = 1 ∧ a.im ≠ 0 := by
  have hre := congrArg Complex.re ha
  have him := congrArg Complex.im ha
  simp only [coupledExchange, pow_two, Complex.add_re, Complex.mul_re, Complex.one_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.zero_re, Complex.add_im, Complex.mul_im,
    Complex.one_im, Complex.zero_im, Complex.re_ofNat, Complex.im_ofNat] at hre him
  have hy2 : y ^ 2 < 1 := by
    have := abs_nonneg y
    nlinarith [sq_abs y]
  have hne : a.im ≠ 0 := by
    intro h0
    rw [h0] at hre
    nlinarith [sq_nonneg (a.re + y)]
  refine ⟨?_, hne⟩
  have hx : a.re = -y := by
    have : a.im * (2 * a.re + 2 * y) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hne
    · linarith
  have hsq : ‖a‖ ^ 2 = 1 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hx]
    rw [hx] at hre
    nlinarith
  have := norm_nonneg a
  nlinarith

end Coupled

/-! ## 5. Modal hearing is dormancy -/

section Hearing

variable {n : Type*} [Fintype n]

/-- [definition] **A mode's port coefficient**: the mode `v` carries the source `s` to the receiver
`r` with `c = ⟨s, M v⟩⟨r, v⟩`. -/
def modalCoefficient (M : Matrix n n ℝ) (s r v : n → ℝ) : ℝ := (s ⬝ᵥ (M *ᵥ v)) * (r ⬝ᵥ v)

/-- [proved-derived; formal-checked] **A mode is silent exactly when one of its couplings
vanishes.** -/
theorem modal_silent_iff (M : Matrix n n ℝ) (s r v : n → ℝ) :
    modalCoefficient M s r v = 0 ↔ s ⬝ᵥ (M *ᵥ v) = 0 ∨ r ⬝ᵥ v = 0 :=
  mul_eq_zero

/-- [proved-derived; formal-checked] **A dormant mode reopens after a constitutive change**: with
source and receiver at the first node, the mode `(0, 1)` is silent, and the mode `(1, 1)` that a
change of the constitution moves it to carries the coefficient `1`. -/
theorem dormant_mode_reopens :
    modalCoefficient (1 : Matrix (Fin 2) (Fin 2) ℝ) ![1, 0] ![1, 0] ![0, 1] = 0 ∧
      modalCoefficient (1 : Matrix (Fin 2) (Fin 2) ℝ) ![1, 0] ![1, 0] ![1, 1] = 1 := by
  simp [modalCoefficient, dotProduct, Fin.sum_univ_two]

end Hearing

section Audit

#print axioms exchange_hasDerivAt
#print axioms lockFace_eq_bias_logDeriv
#print axioms lockFace_logistic
#print axioms lockFace_hasDerivAt
#print axioms bias_susceptibility
#print axioms susceptibility_le_quarter
#print axioms lock_susceptibility_le_quarter
#print axioms exchangeN_eq_zero_iff
#print axioms selectivity_eq_exchange_ratio
#print axioms pivotRatio_between
#print axioms pivotRatio_between'
#print axioms selectivity_lock_count_bound
#print axioms selectivity_lock_count_bound'
#print axioms logDeriv_exchangeC
#print axioms pivot_winding_inside
#print axioms pivot_winding_outside
#print axioms winding_is_carry
#print axioms uncoupled_double_pivot
#print axioms coupled_zeros_leave_the_axis
#print axioms modal_silent_iff
#print axioms dormant_mode_reopens

end Audit

end Holonics.Objects.ParametronLock
