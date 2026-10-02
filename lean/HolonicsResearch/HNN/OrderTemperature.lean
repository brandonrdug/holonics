import Mathlib

/-!
# The commitment is read on the turn clock: a crossing read at its grain enters the first order

[proved-derived; formal-checked] for the theorems; [definition; derived in the record] for
`aheadShare`, `copresentShare` and `commitResidual` (the record
`research/records/2026-10-02_THE_COMMITMENT_IS_READ_ON_THE_TURN_CLOCK_ITS_ORDER_HAS_A_TEMPERATURE_OF_ONE_TURN_AND_A_CROSSING_ENTERS_THE_FIRST_ORDER.md`).

The release commits each station at zero temperature, so its released code length jumps where two
stations' commitments change order (`HNN/ExecutedComparison` §13). Read the order on the clock the
lock is read on instead: the incumbent's order `A` holds on a share `p` of the clock's origins and
the crossed order on the rest. This file states what that reading buys and what it costs.

1. **No jump** (`orderMixture_continuous`, `threeOrder_continuous`).
2. **The jump becomes a first-order term** (`orderMixture_hasDerivAt`): the slope is the two orders'
   slopes at their shares plus the anticipation `p′ μ′ (C_A − C_B)`.
3. **The anticipation pays the jump exactly** (`anticipation_integral`).
4. **A negative slope is adopted by some halving** (`halving_adopts_of_neg_slope`, from the right
   slope alone); at zero temperature a jump present at every small step refuses every halving
   (`jump_refuses_every_halving`).
5. **The anticipation pushes toward the cheaper order** (`anticipation_pos_iff`).
6. **Sharpening recovers the zero-temperature comparison off the crossing**
   (`occupation_sharpens_pos`, `occupation_sharpens_neg`, `orderMixture_sharpens`).
7. **The receiver's resolution bounds what is left unread** (`orderMixture_resolution`).
8. **The turn clock's partition** (`aheadShare`, `copresentShare`): with the commitment instants'
   difference `Δ` in turns and the clock's origin uniform on the circle, `A` is read a turn first on
   `clamp Δ`, both in one turn on `max 0 (1 − |Δ|)` (`copresentShare_eq`), `B` first on
   `clamp (−Δ)`; the arcs sum to one (`shares_sum`), read the whole order a turn apart
   (`aheadShare_of_one_le`), and move at rate one (`aheadShare_lipschitz`).
9. **The commitment instant** (`commitResidual`): a station commits where its top's code length
   over `n` turns reaches the grain; the residual falls strictly past the threshold
   (`commitResidual_strictAnti`), never reaches the grain below it (`commitResidual_ge_one`), and a
   pointwise smaller residual commits no later (`commit_instant_le`).
-/

namespace Holonics.HNN.OrderTemperature

open Real Set Filter Topology MeasureTheory intervalIntegral

/-! ## 1. The two orders' mixture along a step -/

/-- [definition] **The comparison read with the order at finite temperature**, along a step `η`:
the incumbent's order `A` at occupation `p (μ η)`, the crossed order `B` at the rest. -/
noncomputable def orderMixture (p μ CA CB : ℝ → ℝ) (η : ℝ) : ℝ :=
  p (μ η) * CA η + (1 - p (μ η)) * CB η

/-- [proved-derived; formal-checked] **No jump**: with a continuous kernel, margin and the two
orders' comparisons, the mixture is continuous. -/
theorem orderMixture_continuous {p μ CA CB : ℝ → ℝ} (hp : Continuous p) (hμ : Continuous μ)
    (hA : Continuous CA) (hB : Continuous CB) : Continuous (orderMixture p μ CA CB) := by
  unfold orderMixture
  fun_prop

/-- [proved-derived; formal-checked] **The jump becomes a first-order term.** The slope of the
mixture is each order's slope at its occupation plus the anticipation `p′ μ′ (C_A − C_B)`. -/
theorem orderMixture_hasDerivAt {p μ CA CB : ℝ → ℝ} {p' μ' a b η : ℝ}
    (hp : HasDerivAt p p' (μ η)) (hμ : HasDerivAt μ μ' η) (hA : HasDerivAt CA a η)
    (hB : HasDerivAt CB b η) :
    HasDerivAt (orderMixture p μ CA CB)
      (p (μ η) * a + (1 - p (μ η)) * b + p' * μ' * (CA η - CB η)) η := by
  have hpμ : HasDerivAt (fun x => p (μ x)) (p' * μ') η := hp.comp η hμ
  have h := (hpμ.mul hA).add (((hasDerivAt_const η (1 : ℝ)).sub hpμ).mul hB)
  unfold orderMixture
  exact h.congr_deriv (by simp only [Pi.sub_apply]; ring)

/-- [proved-derived; formal-checked] **The anticipation pays the jump exactly.** With a
continuously differentiable kernel and margin, the anticipation's integral along `[s, t]` at a
fixed cost `J` is `J` times the change in the incumbent order's occupation. -/
theorem anticipation_integral {p p' μ μ' : ℝ → ℝ} {s t J : ℝ}
    (hp : ∀ x, HasDerivAt p (p' x) x) (hp' : Continuous p')
    (hμ : ∀ x ∈ uIcc s t, HasDerivAt μ (μ' x) x) (hμ' : ContinuousOn μ' (uIcc s t)) :
    ∫ η in s..t, p' (μ η) * μ' η * J = J * (p (μ t) - p (μ s)) := by
  have h := integral_comp_mul_deriv (f := μ) (f' := μ') (g := p') hμ hμ' hp'
  have hFTC : ∫ x in μ s..μ t, p' x = p (μ t) - p (μ s) :=
    integral_eq_sub_of_hasDerivAt (fun x _ => hp x) (hp'.intervalIntegrable _ _)
  have hcomm : (∫ η in s..t, p' (μ η) * μ' η * J) = (∫ η in s..t, (p' ∘ μ) η * μ' η) * J := by
    rw [← intervalIntegral.integral_mul_const]
    rfl
  rw [hcomm, h, hFTC]
  ring

/-! ## 2. Adoption by halving: finite against zero temperature -/

/-- [proved-derived; formal-checked] **A negative slope is adopted at every small enough step.** Only
the slope from the right is used, so a kernel with corners (the turn clock's, §5) qualifies. -/
theorem eventually_lt_of_neg_slope {f : ℝ → ℝ} {d : ℝ} (hf : HasDerivWithinAt f d (Ioi 0) 0)
    (hd : d < 0) : ∀ᶠ η in 𝓝[>] (0 : ℝ), f η < f 0 := by
  have hs : Tendsto (slope f 0) (𝓝[>] (0 : ℝ)) (𝓝 d) := by
    have := hasDerivWithinAt_iff_tendsto_slope.mp hf
    simpa using this
  have hneg : ∀ᶠ t in 𝓝[>] (0 : ℝ), slope f 0 t < 0 := hs.eventually (gt_mem_nhds hd)
  filter_upwards [hneg, self_mem_nhdsWithin] with t ht htpos
  have htp : (0 : ℝ) < t := htpos
  rw [slope_def_field, sub_zero] at ht
  have : f t - f 0 < 0 := by
    by_contra hcon
    push Not at hcon
    have := div_nonneg hcon htp.le
    linarith
  linarith

/-- The halved steps `η₀ / 2^k` approach zero from above. -/
theorem halvings_tendsto {η₀ : ℝ} (h : 0 < η₀) :
    Tendsto (fun k : ℕ => η₀ / 2 ^ k) atTop (𝓝[>] (0 : ℝ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨?_, Eventually.of_forall fun k => ?_⟩
  · have : Tendsto (fun k : ℕ => η₀ * ((1 : ℝ) / 2) ^ k) atTop (𝓝 (η₀ * 0)) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).const_mul η₀
    simpa [div_eq_mul_inv, one_div, inv_pow, mul_zero] using this
  · exact div_pos h (pow_pos (by norm_num) k)

/-- [proved-derived; formal-checked] **At finite temperature some halving is adopted**: if the
mixture's slope at the incumbent is negative, some step `η₀ / 2^k` lowers it. -/
theorem halving_adopts_of_neg_slope {f : ℝ → ℝ} {d η₀ : ℝ} (hf : HasDerivWithinAt f d (Ioi 0) 0)
    (hd : d < 0)
    (hη : 0 < η₀) : ∃ k : ℕ, f (η₀ / 2 ^ k) < f 0 :=
  ((halvings_tendsto hη).eventually (eventually_lt_of_neg_slope hf hd)).exists

/-- [proved-derived; formal-checked] **At zero temperature a jump refuses every small halving**: if
the comparison is a continuous part `g` plus a jump `J > 0` at every positive step, with
`g 0 = f 0`, then every small enough step reads above the incumbent, whatever `g`'s slope. -/
theorem jump_refuses_every_halving {f g : ℝ → ℝ} {J : ℝ} (hJ : 0 < J)
    (hjump : ∀ η, 0 < η → f η = g η + J) (h0 : g 0 = f 0) (hg : ContinuousAt g 0) :
    ∀ᶠ η in 𝓝[>] (0 : ℝ), f 0 < f η := by
  have hnear : ∀ᶠ η in 𝓝 (0 : ℝ), g 0 - J < g η :=
    hg.eventually (lt_mem_nhds (by linarith))
  filter_upwards [nhdsWithin_le_nhds hnear, self_mem_nhdsWithin] with η hη hpos
  rw [hjump η hpos]
  linarith

/-! ## 3. The anticipation's sign and the sharpened limit -/

/-- [proved-derived; formal-checked] **The anticipation pushes toward the cheaper order**: with a
rising occupation `p′ > 0`, the anticipation raises the slope exactly when the step moves the
margin toward the costlier order (`μ′ J > 0`, `J = C_A − C_B`). -/
theorem anticipation_pos_iff {p' μ' J : ℝ} (hp' : 0 < p') : 0 < p' * μ' * J ↔ 0 < μ' * J := by
  rw [mul_assoc]
  exact ⟨fun h => (pos_iff_pos_of_mul_pos h).mp hp', fun h => mul_pos hp' h⟩

/-- [proved-derived; formal-checked] **Sharpening, ahead of the crossing.** A kernel read at inverse
temperature `β` on the margin, `k (β μ)`, tends to one as `β` grows wherever the margin favours
the incumbent's order. -/
theorem occupation_sharpens_pos {k : ℝ → ℝ} {m : ℝ} (hk : Tendsto k atTop (𝓝 1)) (hm : 0 < m) :
    Tendsto (fun β => k (β * m)) atTop (𝓝 1) :=
  hk.comp (tendsto_id.atTop_mul_const hm)

/-- [proved-derived; formal-checked] **Sharpening, past the crossing**: it tends to zero where the
margin favours the crossed order. -/
theorem occupation_sharpens_neg {k : ℝ → ℝ} {m : ℝ} (hk : Tendsto k atBot (𝓝 0)) (hm : 0 < m) :
    Tendsto (fun β => k (β * -m)) atTop (𝓝 0) := by
  have : Tendsto (fun β : ℝ => β * -m) atTop atBot :=
    tendsto_id.atTop_mul_const_of_neg (by linarith)
  exact hk.comp this

/-- [proved-derived; formal-checked] **The sharpened mixture is the zero-temperature comparison off
the crossing**: where the margin favours the incumbent's order the mixture tends to `C_A`. -/
theorem orderMixture_sharpens {k : ℝ → ℝ} {m cA cB : ℝ} (hk : Tendsto k atTop (𝓝 1)) (hm : 0 < m) :
    Tendsto (fun β => k (β * m) * cA + (1 - k (β * m)) * cB) atTop (𝓝 cA) := by
  have h := occupation_sharpens_pos hk hm
  have := (h.mul_const cA).add (((tendsto_const_nhds (x := (1 : ℝ))).sub h).mul_const cB)
  simpa using this

/-! ## 4. What the receiver's resolution leaves unread -/

/-- [proved-derived; formal-checked] **The resolution bound.** If the kernel moves by at most `L`
per unit of margin and the margin is known to within `w`, the mixture is known to within
`L · w · |C_A − C_B|`: the zero-temperature jump `|J|` is replaced by that width. -/
theorem orderMixture_resolution {p : ℝ → ℝ} {L w μ₁ μ₂ cA cB : ℝ}
    (hlip : ∀ x y, |p x - p y| ≤ L * |x - y|) (hw : |μ₁ - μ₂| ≤ w) (hL : 0 ≤ L) :
    |(p μ₁ * cA + (1 - p μ₁) * cB) - (p μ₂ * cA + (1 - p μ₂) * cB)| ≤ L * w * |cA - cB| := by
  have h : (p μ₁ * cA + (1 - p μ₁) * cB) - (p μ₂ * cA + (1 - p μ₂) * cB)
      = (p μ₁ - p μ₂) * (cA - cB) := by ring
  rw [h, abs_mul]
  exact mul_le_mul_of_nonneg_right ((hlip μ₁ μ₂).trans (mul_le_mul_of_nonneg_left hw hL))
    (abs_nonneg _)

/-! ## 5. The turn clock's kernel and the commitment instant -/

/-- [definition] The unit clamp, `min 1 (max 0 s)`. -/
noncomputable def clampUnit (s : ℝ) : ℝ := min 1 (max 0 s)

theorem clampUnit_continuous : Continuous clampUnit := by
  unfold clampUnit; fun_prop

theorem clampUnit_nonneg (s : ℝ) : 0 ≤ clampUnit s := by
  unfold clampUnit; exact le_min zero_le_one (le_max_left _ _)

theorem clampUnit_le_one (s : ℝ) : clampUnit s ≤ 1 := by
  unfold clampUnit; exact min_le_left _ _

theorem clampUnit_of_nonpos {s : ℝ} (h : s ≤ 0) : clampUnit s = 0 := by
  unfold clampUnit; rw [max_eq_left h]; simp

theorem clampUnit_of_one_le {s : ℝ} (h : 1 ≤ s) : clampUnit s = 1 := by
  unfold clampUnit; rw [max_eq_right (by linarith), min_eq_left h]

/-- [proved-derived; formal-checked] The clamp moves by at most the change in its argument. -/
theorem clampUnit_lipschitz (x y : ℝ) : |clampUnit x - clampUnit y| ≤ |x - y| := by
  unfold clampUnit
  exact (abs_min_sub_min_le_max _ _ _ _).trans
    (max_le (by simp) (by rw [max_comm 0 x, max_comm 0 y]; exact abs_max_sub_max_le_abs _ _ _))

/-- [definition; derived in the record] **The share of the gauge circle on which `A` commits a turn
before `B`**, `Δ = t_B − t_A` the commitment instants' difference in turns: the turn boundaries sit
at `φ + ℤ`, `φ` the clock's origin, and `A` is read first exactly when a boundary falls in
`(t_A, t_B]`, which happens on the share `min 1 Δ` of origins. -/
noncomputable def aheadShare (Δ : ℝ) : ℝ := clampUnit Δ

/-- [definition; derived in the record] **The share on which the two commit in one turn** (no
boundary between them): they are co-present for the clock and lock together. -/
noncomputable def copresentShare (Δ : ℝ) : ℝ := 1 - clampUnit Δ - clampUnit (-Δ)

/-- [proved-derived; formal-checked] **The three shares partition the gauge circle.** -/
theorem shares_sum (Δ : ℝ) : aheadShare Δ + copresentShare Δ + aheadShare (-Δ) = 1 := by
  unfold aheadShare copresentShare; ring

/-- [proved-derived; formal-checked] **The co-present share is `max 0 (1 − |Δ|)`**: nonnegative,
whole at a tie, and gone once the instants are a turn apart. -/
theorem copresentShare_eq (Δ : ℝ) : copresentShare Δ = max 0 (1 - |Δ|) := by
  unfold copresentShare
  rcases le_total Δ 0 with h | h
  · rw [clampUnit_of_nonpos h, abs_of_nonpos h]
    rcases le_total (-Δ) 1 with h' | h'
    · unfold clampUnit
      rw [max_eq_right (by linarith), min_eq_right h', max_eq_right (by linarith)]
      ring
    · rw [clampUnit_of_one_le h', max_eq_left (by linarith)]; ring
  · rw [clampUnit_of_nonpos (by linarith : -Δ ≤ 0), abs_of_nonneg h]
    rcases le_total Δ 1 with h' | h'
    · unfold clampUnit
      rw [max_eq_right h, min_eq_right h', max_eq_right (by linarith)]
      ring
    · rw [clampUnit_of_one_le h', max_eq_left (by linarith)]; ring

theorem copresentShare_nonneg (Δ : ℝ) : 0 ≤ copresentShare Δ := by
  rw [copresentShare_eq]; exact le_max_left _ _

/-- [proved-derived; formal-checked] **A turn apart, the order is read whole**: the earlier station
commits first on the whole circle. -/
theorem aheadShare_of_one_le {Δ : ℝ} (h : 1 ≤ Δ) :
    aheadShare Δ = 1 ∧ copresentShare Δ = 0 ∧ aheadShare (-Δ) = 0 := by
  unfold aheadShare copresentShare
  rw [clampUnit_of_one_le h, clampUnit_of_nonpos (by linarith)]
  norm_num

/-- [proved-derived; formal-checked] **The kernel's rate is one per turn**: each share moves by at
most the change in the instants' difference. -/
theorem aheadShare_lipschitz (x y : ℝ) : |aheadShare x - aheadShare y| ≤ |x - y| :=
  clampUnit_lipschitz x y

/-- [proved-derived; formal-checked] **The three-order comparison is continuous** in the step
wherever the instants' difference and the three orders' comparisons are. -/
theorem threeOrder_continuous {Δ CA CC CB : ℝ → ℝ} (hΔ : Continuous Δ) (hA : Continuous CA)
    (hC : Continuous CC) (hB : Continuous CB) :
    Continuous fun η => aheadShare (Δ η) * CA η + copresentShare (Δ η) * CC η
      + aheadShare (-Δ η) * CB η := by
  unfold aheadShare copresentShare
  have hc := clampUnit_continuous
  fun_prop

/-! ### The commitment instant -/

/-- [definition; derived in the record] **The commitment residual** of a station read over `n`
turns: `a_top^(−n) + Σ_y r_y^n`, `r_y = a_y/a_top` each rival's ratio to the top. The top's code
length at inverse temperature `n` is `log₂(1 + residual)`, and the station commits at the instant
`n` where that code length falls to the grain `τ`, i.e. the residual to `2^τ − 1`. -/
noncomputable def commitResidual {ι : Type*} (s : Finset ι) (aTop : ℝ) (r : ι → ℝ) (n : ℝ) : ℝ :=
  aTop⁻¹ ^ n + ∑ y ∈ s, r y ^ n

/-- [proved-derived; formal-checked] **The residual falls strictly with the turns read**, past the
threshold (`a_top > 1`) and with every rival below the top: the commitment instant is unique. -/
theorem commitResidual_strictAnti {ι : Type*} (s : Finset ι) {aTop : ℝ} {r : ι → ℝ}
    (ha : 1 < aTop) (hr0 : ∀ y ∈ s, 0 < r y) (hr1 : ∀ y ∈ s, r y < 1) :
    StrictAnti (commitResidual s aTop r) := by
  intro m n hmn
  unfold commitResidual
  have h1 : aTop⁻¹ ^ n < aTop⁻¹ ^ m :=
    Real.rpow_lt_rpow_of_exponent_gt (inv_pos.mpr (by linarith)) (inv_lt_one_of_one_lt₀ ha) hmn
  have h2 : ∑ y ∈ s, r y ^ n ≤ ∑ y ∈ s, r y ^ m :=
    Finset.sum_le_sum fun y hy => (Real.rpow_lt_rpow_of_exponent_gt (hr0 y hy) (hr1 y hy) hmn).le
  linarith

/-- [proved-derived; formal-checked] **A station whose residual lies below another's at every
instant commits no later**: with each reaching the level `c` at its instant, the first's instant
is at most the second's. -/
theorem commit_instant_le {RA RB : ℝ → ℝ} {c tA tB : ℝ} (hA : StrictAnti RA)
    (hle : ∀ n, RA n ≤ RB n) (htA : RA tA = c) (htB : RB tB = c) : tA ≤ tB := by
  by_contra h
  push Not at h
  have := hA h
  have := hle tB
  linarith

/-- [proved-derived; formal-checked] **Below the threshold no station commits**: with `a_top ≤ 1`
the residual stays at least one at every nonnegative instant, above every grain `2^τ − 1 < 1`. -/
theorem commitResidual_ge_one {ι : Type*} (s : Finset ι) {aTop : ℝ} {r : ι → ℝ}
    (ha0 : 0 < aTop) (ha : aTop ≤ 1) (hr0 : ∀ y ∈ s, 0 ≤ r y) {n : ℝ} (hn : 0 ≤ n) :
    1 ≤ commitResidual s aTop r n := by
  unfold commitResidual
  have h1 : 1 ≤ aTop⁻¹ ^ n := Real.one_le_rpow (one_le_inv₀ ha0 |>.mpr ha) hn
  have h2 : 0 ≤ ∑ y ∈ s, r y ^ n :=
    Finset.sum_nonneg fun y hy => Real.rpow_nonneg (hr0 y hy) n
  linarith

end Holonics.HNN.OrderTemperature
