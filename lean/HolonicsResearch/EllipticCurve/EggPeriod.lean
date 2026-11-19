import HolonicsResearch.EllipticCurve.EggFamily
import HolonicsResearch.Geometry.HypergeometricMonodromy
import Holonics.Objects.RatioPhase

/-!
# The egg's period is the oval's integral, and its two degenerate fibres move the periods by shears

Source: #410's box "The egg as an elliptic family" (the egg cubic equals the twisted Legendre form with
`λ = ((a − w)/(a + w))² = k⁻⁴`; its real components and degenerate fibres at `β = 0, 1`; rational eggs as elliptic
curves over `ℚ`; null monodromy and logarithmic period at the neck), part done in #1018 by
`EllipticCurve/EggFamily`, whose note ends "owed: the null monodromy, and the period as the oval's integral", and
whose "What is not claimed" leaves the identity `∫_egg ω = (2/(b(a + w))) K(√(1 − λ))` (the substitution on the
oval) and the monodromies `[[1, 4], [0, 1]]` at the neck and `[[1, 2], [0, 1]]` at the ellipse. The record
`research/records/2026-09-24_THE_EGG_IS_A_TORUS_WHOSE_SHAPE_IS_A_BOOST_AND_ITS_NECK_IS_THE_NULL_CONE.md` §3 states
both ("The period that grows", the two singular fibres, "What null means here") and lists them under its
"Obligations". Atlas rows: `egg.elliptic-family`, `egg.period-coefficients`, `lock.riemann-scheme-rigidity`.
Owners consumed: `EllipticCurve/EggFamily` (`eggEq`, `eggU`, `branchA`, `branchB`, `eggFy`, `neckRadicand`,
`ellipticK_complement`, `ellipticK_neck`, `egg_period_neck`, `egg_discr_orders`, `legendreCubicPoly`),
`Geometry/CompleteEllipticSeries` (`ellipticK`), `Geometry/HypergeometricMonodromy` (`shiftLog`, `legendreBasis`,
`shiftLog_legendreBasis`, `continuation_round_zero`, `toK`, `conjBy`, `exists_conj_shear`),
`Geometry/LegendreLevelTwo` (`A`, `B`, `coe_A_zpow`) and `Objects/RatioPhase` (`continuous_lift_unique`).

[definition] On the oval (`x ∈ [−a, a]`, where `u = eggU a w x > 0`) the upper arc is `y₊ = √(b²(a² − x²)/u)`
(`upperArc`). The period of `ω = dx/F_y`, `F_y = eggFy = 2uy`, round the oval is the sum of the integrals over its
two arcs, the upper read from `−a` to `a` and the lower (`y = −y₊`) read from `a` back to `−a`, the orientation for
which it is positive (`ovalPeriod`). Over `ℂ`, `λ(β) = ((1 − β)/(1 + β))²` (`lambdaC`); the loop round the neck is
`β = 1 + r e^(2πit)` and the loop round the ellipse `β = r e^(2πit)`, `t ∈ [0, 1]`, `0 < r < 1` (`turn`,
`neckLoop`, `ellipseLoop`).

[proved-derived; formal-checked] What is proved. The classical inputs (the change of variables on the open interval,
the Legendre chart's integral, the uniqueness of lifts, the composition of the formal moves and the shears'
conjugacy) are tagged `[proved-standard; formal-checked]` at their theorems.

1. **The substitution on the oval** (§1). `x = a cos φ` carries `(0, π)` onto `(−a, a)` (`image_cos_Ioo`), and every
   integral over `[−a, a]` is the integral over `(0, π)` with weight `a sin φ` (`integral_comp_cos`), by Mathlib's
   one-dimensional change of variables on the open interval, which asks neither integrability nor continuity at the
   ends, where the oval's integrand is unbounded. The composite of the two substitutions `x ↦ u` and
   `u = B cos²θ + A sin²θ` is `x = a cos 2θ`: `eggU a w (a cos 2θ) = B cos²θ + A sin²θ = B (cos²θ + λ sin²θ)`
   (`eggU_cos_two`, `eggU_cos_two_eq`), and `(u − A)(B − u) = 4w²(a² − x²)` (`oval_factor`). Along the oval
   `u > 0` (`eggU_pos_of_cos`, `eggU_pos`).
2. **The period as the oval's integral** (§1). For `0 ≤ w < a` and every `b`,
   `∫_(−a)^a dx/(b √(u (a² − x²))) = (2/(b(a + w))) K(√(1 − λ))`, `λ = A/B` (`integral_oval`). Both arcs lie on the
   egg (`upperArc_eggEq`); on the oval `2/F_y(x, y₊) = 1/(b √(u (a² − x²)))` for `b > 0`
   (`ovalPeriod_integrand`), so the oval's period is that integral (`ovalPeriod_eq_integral`) and equals the
   record's closed form (`ovalPeriod_eq`). In the Legendre chart, for `0 < w < a`,
   `∫_A^B du/√(u (u − A)(B − u)) = (2/√B) K(√(1 − λ))` (`integral_legendre_form`).
3. **The two ends of the family** (§1). At `w = 0` the oval is the ellipse and its period is `π/(ab)`
   (`ovalPeriod_ellipse`, with `K(0) = π/2`, `ellipticK_zero`). At the neck `λ → 0⁺` as `w → a⁻`
   (`lambda_tendsto_neck`), and the oval's own period minus `log(16/λ)/(b(a + w))` tends to `0` (`ovalPeriod_neck`,
   from `ellipticK_neck`). Joined to the owner: the oval's period minus `(1/(2ab)) log(1/λ)` tends to
   `2 log 2/(ab)` (`ovalPeriod_neck_log`, from `egg_period_neck`), so the owner's statement about the record's closed
   form is now a statement about the oval.
4. **The lifts round the degenerate fibres** (§2). `turn t = e^(2πit)` has norm one and closes at `t = 1`
   (`turn_zero`, `turn_one`, `norm_turn`, `continuous_turn`), and `c + r turn t` lies in the right half plane for
   `|r| < c` (`re_add_turn_pos`, `slitPlane_add_turn`, `add_turn_ne_zero`, `continuous_log_add_turn`). Two continuous
   lifts on `[0, 1]` gain the same amount (`lift_gain`, from `continuous_lift_unique`). The modulus is
   `λ = (β − 1)²/(1 + β)²` and `1 − λ = 4β/(1 + β)²` (`lambdaC_orders`, `one_sub_lambdaC`), and on the real line it
   is `EggModular.eggLambda` (`lambdaC_ofReal`). For `0 < r < 1`, round the neck the lift
   `2(log r + iπ + 2πit) − 2 Log(2 + r e^(2πit))` of `λ` (`neckLift`, `neckLift_spec`, `continuous_neckLift`) gains
   `4πi`, so every continuous lift of `λ` does (`neck_lambda_gain`), and every continuous lift of `1 − λ` gains `0`
   (`neck_one_sub_gain`, through `neckLiftOneSub`); round the ellipse every continuous lift of `1 − λ` gains `2πi`
   (`ellipse_one_sub_gain`, through `ellipseLift`) and every continuous lift of `λ` gains `0`
   (`ellipse_lambda_gain`, through `ellipseLiftLambda`). So the neck's loop is two Legendre loops round `λ = 0` and
   none round `λ = 1`, and the ellipse's loop is one round `λ = 1` and none round `λ = 0`.
5. **The null monodromy** (§3). `A² = [[1, 4], [0, 1]]` (`coe_A_sq`). The continuation adds
   (`shiftLog_add`: `ℓ ↦ ℓ + κ + κ'` is `ℓ ↦ ℓ + κ'` followed by `ℓ ↦ ℓ + κ`) and is linear (`shiftLog_sum_smul`), so
   two Legendre moves compose to `ℓ ↦ ℓ + 4κ`, which moves the owner's basis `(F, (Fℓ + G)/κ)` by `A²`
   (`shiftLog_legendreBasis_four`, composed from `shiftLog_legendreBasis`). Joined to the lifts: the formal logarithm
   shifted by the gain of any continuous lift of `λ` round the neck moves the basis `(F, (Fℓ + G)/(πi))` by `A²`
   (`neck_move`), and shifted by the gain of any continuous lift of `1 − λ` round the ellipse moves the same basis,
   read in the chart `μ = 1 − λ`, by `A` (`ellipse_move`). In the basis at `0` the owner's rigidity reads the move
   round `1` as `B⁻¹ = [[1, 0], [−2, 1]]` (`legendre_rigidity`), and `B⁻¹ = S A S⁻¹` in `SL(2, ℤ)`
   (`B_inv_eq_conj_A`): conjugate to `A`. Both moves are shears: trace `2`, not `1`, `(M − 1)² = 0`, and conjugate
   over `ℚ` to `T = [[1, 1], [0, 1]]` (`moves_are_shears`, from `exists_conj_shear`). Their off-diagonal entries `4`
   and `2` are the discriminant's orders at `w = a` and at `w = 0`, each with a nonzero cofactor there
   (`shear_entries_discriminant_orders`, from `egg_discr_orders`).
6. **A witness** (§4). The egg `a = 2, w = 1, b = 1` has `λ = 1/9`, and its oval integral and oval period are
   `(2/3) K(√(8/9))`; its neck move `A² = [[1, 4], [0, 1]]` has trace `2` (`egg_211_period`).

What the formal statement carries. Items 4 and 5 meet at the gain. Item 4 is a theorem about actual continuous lifts
of `λ` and `1 − λ` along actual loops of `β` in `ℂ`. Item 5 shifts the owner's formal logarithm, on pairs `A + Bℓ`
of power series with `θℓ = 1`, by that gain. That this `ℓ` is `log λ` continued along the loop, and that the owner's
series are the actual period functions continued there (`K(√λ) = (π/2) F(λ)` and its partner `Fℓ + G`), is the
owner's reading and is not proved here: no analytic continuation of `K` as a function of complex `λ` is proved, and
the convergence of `G` is left as `HypergeometricMonodromy` leaves it. In `ellipse_move` the series variable is read
as `μ = 1 − λ`: Legendre's operator is invariant under `λ ↦ 1 − λ` (`legendre_comp_one_sub`, on polynomials, since a
formal power series in `λ` admits no substitution `λ ↦ 1 − λ`), which is why the owner's basis read in `μ` is a
basis at `λ = 1`. The connection matrix between the bases at `0` and at `1` is not computed, so the conjugation of
the ellipse's move into the basis at `0` is read through the owner's rigidity and `B_inv_eq_conj_A`, not derived
from the periods.

What is not claimed. Kodaira's classification (`I₄` at the neck, `I₂` at the ellipse), the resolution of the total
surface and the Legendre fibre `I₂*` at `∞`. The analytic continuation of `K`, or of the oval's period, as a function
of complex `β` beyond the owner's formal logarithm, and the monodromy representation on `H₁` of the actual fibres:
`A²` and `A` are the moves of the formal basis by the lifts' gains, not computed on cycles of the curve. The
vanishing cycle's period (`iπ/(2ab)` in the record). The oval's period as a contour integral on the curve:
`ovalPeriod` is the sum of its two arc integrals in the `x` chart. The group `E(ℝ)`, ranks and Mordell–Weil groups
of rational eggs. For `−a < w < 0`, the mirror of `w > 0` under `x ↦ −x`, `integral_oval` is not stated (there
`λ > 1`, and Lean's `√` of a negative number is `0`).

The computational object is the helical pair interaction: de La Hire's two circles in relative motion, the inner one
displaced by `w`, whose face is the egg. The substitution that computes the period, `x = a cos 2θ`, reads the oval
as a turn: while `θ` runs a quarter turn `x` crosses the oval once, and the period `(2/(b(a + w))) K(√(1 − λ))` is
the record's time round the egg. At the two degenerate fibres the move of the periods is free fall: round the neck
the lift of `λ` carries two whole turns and the pair of solutions moves by the shear `A² = [[1, 4], [0, 1]]`; round
the ellipse the lift of `1 − λ` carries one and the move is conjugate to `A = [[1, 2], [0, 1]]`. Both are parabolic
(trace `2`), the shear factor of the swing's turn · boost · shear, which is the record's "null": an exchange at the
characteristic, not an absence. Of the winding guide's six general objects this touches the helix (the lift's carry:
two whole turns at the neck, one at the ellipse), the pair (the torus whose cycle the oval is, and the moves of its
two periods), faces and placement (the oval's period read between the placed branch points `A < u < B`, and the
Legendre face `K(√(1 − λ))`) and the cell holonomy (the moves on the declared circuits round `β = 1` and `β = 0`);
the tube and the tower thread stay attached.

Consumers: the #410 box "The egg as an elliptic family" and the atlas rows above.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.EllipticCurve.EggPeriod

open Real Filter Topology MeasureTheory Set
open Holonics.EllipticCurve.EggFamily
open Holonics.Geometry.CompleteEllipticSeries

/-! ## §1 The period as the oval's integral -/

section Period

/-- [proved-standard; formal-checked] `x = a cos φ` carries `(0, π)` onto `(−a, a)`. -/
theorem image_cos_Ioo {a : ℝ} (ha : 0 < a) : (fun φ => a * cos φ) '' Ioo 0 π = Ioo (-a) a := by
  ext x
  constructor
  · rintro ⟨φ, ⟨h0, hπ⟩, rfl⟩
    have h1 : cos φ < 1 := by
      have := strictAntiOn_cos ⟨le_rfl, pi_pos.le⟩ ⟨h0.le, hπ.le⟩ h0
      simpa using this
    have h2 : -1 < cos φ := by
      have := strictAntiOn_cos ⟨h0.le, hπ.le⟩ ⟨pi_pos.le, le_rfl⟩ hπ
      simpa using this
    constructor <;> nlinarith
  · rintro ⟨h1, h2⟩
    have hx1 : -1 < x / a := by rw [lt_div_iff₀ ha]; linarith
    have hx2 : x / a < 1 := by rw [div_lt_iff₀ ha]; linarith
    refine ⟨arccos (x / a), ⟨arccos_pos.mpr hx2, arccos_lt_pi.mpr hx1⟩, ?_⟩
    simp only
    rw [cos_arccos hx1.le hx2.le]
    field_simp

/-- [proved-standard; formal-checked] **The substitution on the oval**: `∫_(−a)^a g = ∫_(0,π) a sin φ · g(a cos φ)`
for every `g`, with no integrability asked at the ends. -/
theorem integral_comp_cos {a : ℝ} (ha : 0 < a) (g : ℝ → ℝ) :
    ∫ x in (-a)..a, g x = ∫ φ in Ioo 0 π, a * sin φ * g (a * cos φ) := by
  rw [intervalIntegral.integral_of_le (by linarith), integral_Ioc_eq_integral_Ioo, ← image_cos_Ioo ha,
    integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
      (fun φ _ => ((hasDerivAt_cos φ).const_mul a).hasDerivWithinAt)
      (fun x hx y hy h => injOn_cos (Ioo_subset_Icc_self hx) (Ioo_subset_Icc_self hy)
        (mul_left_cancel₀ ha.ne' h))]
  refine setIntegral_congr_fun measurableSet_Ioo fun φ hφ => ?_
  have hs : 0 < sin φ := sin_pos_of_pos_of_lt_pi hφ.1 hφ.2
  simp only [smul_eq_mul]
  rw [mul_neg, abs_neg, abs_of_pos (mul_pos ha hs)]

/-- [proved-derived; formal-checked] At `x = a cos 2θ` the Legendre abscissa is `u = B cos²θ + A sin²θ`. -/
theorem eggU_cos_two (a w θ : ℝ) :
    eggU a w (a * cos (2 * θ)) = branchB a w * cos θ ^ 2 + branchA a w * sin θ ^ 2 := by
  unfold eggU branchA branchB
  rw [cos_two_mul]
  linear_combination (-(a - w) ^ 2) * sin_sq_add_cos_sq θ

/-- [proved-derived; formal-checked] `u(a cos 2θ) = B (cos²θ + λ sin²θ)`, the owner's `neckRadicand` at `λ = A/B`. -/
theorem eggU_cos_two_eq {a w : ℝ} (hB : branchB a w ≠ 0) (θ : ℝ) :
    eggU a w (a * cos (2 * θ)) = branchB a w * EggFamily.neckRadicand (branchA a w / branchB a w) θ := by
  rw [eggU_cos_two]
  unfold EggFamily.neckRadicand
  field_simp

/-- [proved-derived; formal-checked] On the egg's abscissa, `(u − A)(B − u) = 4w²(a² − x²)`. -/
theorem oval_factor (a w x : ℝ) :
    (eggU a w x - branchA a w) * (branchB a w - eggU a w x) = 4 * w ^ 2 * (a ^ 2 - x ^ 2) := by
  rw [eggU_sub_branchA, show branchB a w - eggU a w x = -(eggU a w x - branchB a w) by ring, eggU_sub_branchB]
  ring

/-- [proved-derived; formal-checked] For `0 ≤ w < a`, `u(a cos φ) ≥ (a − w)² > 0`. -/
theorem eggU_pos_of_cos {a w : ℝ} (hw : 0 ≤ w) (hwa : w < a) (φ : ℝ) : 0 < eggU a w (a * cos φ) := by
  have ha : 0 < a := by linarith
  unfold eggU
  nlinarith [mul_nonneg (mul_nonneg hw ha.le) (by linarith [neg_one_le_cos φ] : 0 ≤ cos φ + 1),
    sq_pos_of_pos (sub_pos.mpr hwa)]

/-- [proved-derived; formal-checked] **The period integral**: for `0 ≤ w < a` and every `b`,
`∫_(−a)^a dx/(b √(u (a² − x²))) = (2/(b(a + w))) K(√(1 − λ))`. -/
theorem integral_oval {a w : ℝ} (hw : 0 ≤ w) (hwa : w < a) (b : ℝ) :
    ∫ x in (-a)..a, (b * √(eggU a w x * (a ^ 2 - x ^ 2)))⁻¹ =
      2 / (b * (a + w)) * ellipticK (√(1 - branchA a w / branchB a w)) := by
  have ha : 0 < a := by linarith
  have hp : 0 < a + w := by linarith
  have hB : 0 < branchB a w := by unfold branchB; positivity
  have hsB : √(branchB a w) = a + w := by unfold branchB; exact Real.sqrt_sq hp.le
  have hl : branchA a w / branchB a w ≤ 1 := by
    rw [div_le_one hB]; unfold branchA branchB; nlinarith
  have hu := eggU_pos_of_cos hw hwa
  rw [integral_comp_cos ha]
  have h1 : ∫ φ in Ioo 0 π, a * sin φ * (b * √(eggU a w (a * cos φ) * (a ^ 2 - (a * cos φ) ^ 2)))⁻¹ =
      ∫ φ in (0)..π, (b * √(eggU a w (a * cos φ)))⁻¹ := by
    rw [intervalIntegral.integral_of_le pi_pos.le, integral_Ioc_eq_integral_Ioo]
    refine setIntegral_congr_fun measurableSet_Ioo fun φ hφ => ?_
    have hs0 : 0 < sin φ := sin_pos_of_pos_of_lt_pi hφ.1 hφ.2
    have hs : 0 < a * sin φ := mul_pos ha hs0
    have hsq : a ^ 2 - (a * cos φ) ^ 2 = (a * sin φ) ^ 2 := by
      linear_combination (-a ^ 2) * sin_sq_add_cos_sq φ
    have hr : 0 < √(eggU a w (a * cos φ)) := Real.sqrt_pos.mpr (hu φ)
    rw [hsq, Real.sqrt_mul (hu φ).le, Real.sqrt_sq hs.le]
    by_cases hb : b = 0
    · simp [hb]
    have := hs0.ne'
    field_simp
  have h2 : ∫ φ in (0)..π, (b * √(eggU a w (a * cos φ)))⁻¹ =
      2 * ∫ θ in (0)..(π / 2), (b * √(eggU a w (a * cos (2 * θ))))⁻¹ := by
    rw [intervalIntegral.integral_comp_mul_left (fun φ => (b * √(eggU a w (a * cos φ)))⁻¹) two_ne_zero,
      smul_eq_mul, mul_zero, show 2 * (π / 2) = π by ring]
    field_simp
  have h3 : ∀ θ, (b * √(eggU a w (a * cos (2 * θ))))⁻¹ =
      (b * (a + w))⁻¹ * (√(EggFamily.neckRadicand (branchA a w / branchB a w) θ))⁻¹ := by
    intro θ
    rw [eggU_cos_two_eq hB.ne', Real.sqrt_mul hB.le, hsB, mul_inv, mul_inv, mul_inv]
    ring
  rw [h1, h2]
  simp only [h3]
  rw [intervalIntegral.integral_const_mul, ← EggFamily.ellipticK_complement hl]
  rw [div_eq_mul_inv]
  ring

/-- [definition] The oval's upper arc `y₊ = √(b²(a² − x²)/u)`. -/
noncomputable def upperArc (a b w x : ℝ) : ℝ := √(b ^ 2 * (a ^ 2 - x ^ 2) / eggU a w x)

/-- [definition] The period of `ω = dx/F_y` round the oval: the upper arc read from `−a` to `a`, then the lower arc
`y = −y₊` read from `a` back to `−a`. -/
noncomputable def ovalPeriod (a b w : ℝ) : ℝ :=
  (∫ x in (-a)..a, (eggFy a w x (upperArc a b w x))⁻¹) + ∫ x in a..(-a), (eggFy a w x (-upperArc a b w x))⁻¹

/-- [proved-derived; formal-checked] For `0 ≤ w < a`, `u > 0` over the whole oval `[−a, a]`. -/
theorem eggU_pos {a w x : ℝ} (hw : 0 ≤ w) (hwa : w < a) (hx : x ∈ Icc (-a) a) : 0 < eggU a w x := by
  have ha : 0 < a := by linarith
  unfold eggU
  nlinarith [mul_nonneg hw (by linarith [hx.1] : 0 ≤ x + a), sq_pos_of_pos (sub_pos.mpr hwa)]

/-- [proved-derived; formal-checked] Both arcs `y = ±y₊` lie on the egg over `[−a, a]`, and `y₊ ≥ 0`. -/
theorem upperArc_eggEq {a b w x : ℝ} (hw : 0 ≤ w) (hwa : w < a) (hx : x ∈ Icc (-a) a) :
    eggEq a b w x (upperArc a b w x) ∧ eggEq a b w x (-upperArc a b w x) ∧ 0 ≤ upperArc a b w x := by
  have hu := eggU_pos hw hwa hx
  have hx2 : 0 ≤ a ^ 2 - x ^ 2 := by nlinarith [hx.1, hx.2]
  have hnn : 0 ≤ b ^ 2 * (a ^ 2 - x ^ 2) / eggU a w x := div_nonneg (mul_nonneg (sq_nonneg b) hx2) hu.le
  have h : eggEq a b w x (upperArc a b w x) := by
    unfold eggEq upperArc
    rw [Real.sq_sqrt hnn]
    have : a ^ 2 + w ^ 2 + 2 * w * x = eggU a w x := by unfold eggU; ring
    rw [this]
    field_simp
  refine ⟨h, ?_, Real.sqrt_nonneg _⟩
  unfold eggEq at h ⊢
  rw [neg_sq]
  exact h

/-- [proved-derived; formal-checked] On the oval, `2/F_y(x, y₊) = 1/(b √(u (a² − x²)))` for `b > 0`. -/
theorem ovalPeriod_integrand {a b w x : ℝ} (hb : 0 < b) (hw : 0 ≤ w) (hwa : w < a) (hx : x ∈ Icc (-a) a) :
    2 * (eggFy a w x (upperArc a b w x))⁻¹ = (b * √(eggU a w x * (a ^ 2 - x ^ 2)))⁻¹ := by
  have hu := eggU_pos hw hwa hx
  have hx2 : 0 ≤ a ^ 2 - x ^ 2 := by nlinarith [hx.1, hx.2]
  have hF : eggFy a w x (upperArc a b w x) = 2 * (b * √(eggU a w x * (a ^ 2 - x ^ 2))) := by
    unfold eggFy upperArc
    have e1 : a ^ 2 + w ^ 2 + 2 * w * x = √(eggU a w x ^ 2) := by
      rw [Real.sqrt_sq hu.le]; unfold eggU; ring
    have e2 : b = √(b ^ 2) := (Real.sqrt_sq hb.le).symm
    rw [e1, mul_assoc, ← Real.sqrt_mul (sq_nonneg _), e2, ← Real.sqrt_mul (sq_nonneg _), ← e2]
    congr 2
    field_simp
  rw [hF, mul_inv, ← mul_assoc, mul_inv_cancel₀ two_ne_zero, one_mul]

/-- [proved-derived; formal-checked] The oval's period is `∫_(−a)^a dx/(b √(u (a² − x²)))`: the lower arc read
backwards repeats the upper. -/
theorem ovalPeriod_eq_integral {a b w : ℝ} (hb : 0 < b) (hw : 0 ≤ w) (hwa : w < a) :
    ovalPeriod a b w = ∫ x in (-a)..a, (b * √(eggU a w x * (a ^ 2 - x ^ 2)))⁻¹ := by
  have ha : 0 < a := by linarith
  have hlow : ∫ x in a..(-a), (eggFy a w x (-upperArc a b w x))⁻¹ =
      ∫ x in (-a)..a, (eggFy a w x (upperArc a b w x))⁻¹ := by
    rw [intervalIntegral.integral_symm, ← intervalIntegral.integral_neg]
    congr 1
    funext x
    unfold eggFy
    rw [mul_neg, inv_neg, neg_neg]
  unfold ovalPeriod
  rw [hlow, ← two_mul, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun x hx => ?_
  rw [uIcc_of_le (by linarith)] at hx
  exact ovalPeriod_integrand hb hw hwa hx

/-- [proved-derived; formal-checked] **The period as the oval's integral**: `∮ ω = (2/(b(a + w))) K(√(1 − λ))` for
`0 ≤ w < a`, `b > 0`. -/
theorem ovalPeriod_eq {a b w : ℝ} (hb : 0 < b) (hw : 0 ≤ w) (hwa : w < a) :
    ovalPeriod a b w = 2 / (b * (a + w)) * ellipticK (√(1 - branchA a w / branchB a w)) := by
  rw [ovalPeriod_eq_integral hb hw hwa, integral_oval hw hwa]

/-- [proved-standard; formal-checked] `K(0) = π/2`. -/
theorem ellipticK_zero : ellipticK 0 = π / 2 := by
  unfold ellipticK
  simp

/-- [proved-derived; formal-checked] **The ellipse fibre** `w = 0`: the oval's period is `π/(ab)`. -/
theorem ovalPeriod_ellipse {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : ovalPeriod a b 0 = π / (a * b) := by
  rw [ovalPeriod_eq hb le_rfl ha]
  have h1 : branchA a 0 / branchB a 0 = 1 := by
    unfold branchA branchB
    rw [sub_zero, add_zero, div_self (pow_ne_zero 2 ha.ne')]
  rw [h1, sub_self, Real.sqrt_zero, ellipticK_zero, add_zero]
  field_simp

/-- [proved-derived; formal-checked] `λ → 0⁺` as `w → a⁻`. -/
theorem lambda_tendsto_neck {a : ℝ} (ha : 0 < a) :
    Tendsto (fun w => branchA a w / branchB a w) (𝓝[<] a) (𝓝[>] 0) := by
  have h2a : (a + a) ^ 2 ≠ 0 := by positivity
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have hc : ContinuousAt (fun w => branchA a w / branchB a w) a := by
      unfold branchA branchB
      exact ContinuousAt.div (by fun_prop) (by fun_prop) h2a
    have h := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio a))
    simpa [branchA] using h
  · filter_upwards [Ioo_mem_nhdsLT ha] with w hw
    have : 0 < a - w := sub_pos.mpr hw.2
    have : 0 < a + w := by linarith [hw.1]
    show 0 < branchA a w / branchB a w
    unfold branchA branchB
    positivity

/-- [proved-derived; formal-checked] **The oval's logarithmic period at the neck**: its period minus
`log(16/λ)/(b(a + w))` tends to `0` as `w → a⁻`. -/
theorem ovalPeriod_neck {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun w => ovalPeriod a b w - log (16 / (branchA a w / branchB a w)) / (b * (a + w)))
      (𝓝[<] a) (𝓝 0) := by
  have hK := EggFamily.ellipticK_neck.comp (lambda_tendsto_neck ha)
  have hden : b * (a + a) ≠ 0 := by positivity
  have c1 : ContinuousAt (fun w : ℝ => 2 / (b * (a + w))) a := ContinuousAt.div (by fun_prop) (by fun_prop) hden
  have hc : Tendsto (fun w : ℝ => 2 / (b * (a + w))) (𝓝[<] a) (𝓝 (2 / (b * (a + a)))) :=
    c1.tendsto.mono_left nhdsWithin_le_nhds
  have h := hc.mul hK
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT ha] with w hw
  have hp : 0 < b * (a + w) := mul_pos hb (by linarith [hw.1])
  simp only [Function.comp]
  rw [ovalPeriod_eq hb hw.1.le hw.2]
  field_simp

/-- [proved-derived; formal-checked] Joined to the owner's `egg_period_neck`: the oval's period minus
`(1/(2ab)) log(1/λ)` tends to `2 log 2/(ab)` as `w → a⁻`. -/
theorem ovalPeriod_neck_log {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun w => ovalPeriod a b w - log (branchA a w / branchB a w)⁻¹ / (2 * a * b))
      (𝓝[<] a) (𝓝 (2 * log 2 / (a * b))) := by
  refine (EggFamily.egg_period_neck ha hb.ne').congr' ?_
  filter_upwards [Ioo_mem_nhdsLT ha] with w hw
  rw [ovalPeriod_eq hb hw.1.le hw.2]

/-- [proved-standard; formal-checked] **The Legendre chart**: for `0 < w < a`,
`∫_A^B du/√(u (u − A)(B − u)) = (2/√B) K(√(1 − A/B))`. -/
theorem integral_legendre_form {a w : ℝ} (hw : 0 < w) (hwa : w < a) :
    ∫ u in (branchA a w)..(branchB a w), (√(u * (u - branchA a w) * (branchB a w - u)))⁻¹ =
      2 / √(branchB a w) * ellipticK (√(1 - branchA a w / branchB a w)) := by
  have hp : 0 < a + w := by linarith
  have hsB : √(branchB a w) = a + w := by unfold branchB; exact Real.sqrt_sq hp.le
  have h2w : (2 * w : ℝ) ≠ 0 := by positivity
  have hsub := intervalIntegral.integral_comp_mul_add
    (fun u => (√(u * (u - branchA a w) * (branchB a w - u)))⁻¹) h2w (a ^ 2 + w ^ 2) (a := -a) (b := a)
  rw [show 2 * w * -a + (a ^ 2 + w ^ 2) = branchA a w by unfold branchA; ring,
    show 2 * w * a + (a ^ 2 + w ^ 2) = branchB a w by unfold branchB; ring] at hsub
  have hpt : ∀ x, (√((2 * w * x + (a ^ 2 + w ^ 2)) * ((2 * w * x + (a ^ 2 + w ^ 2)) - branchA a w) *
      (branchB a w - (2 * w * x + (a ^ 2 + w ^ 2)))))⁻¹ =
      (2 * w)⁻¹ * (1 * √(eggU a w x * (a ^ 2 - x ^ 2)))⁻¹ := by
    intro x
    have e : (2 * w * x + (a ^ 2 + w ^ 2)) * ((2 * w * x + (a ^ 2 + w ^ 2)) - branchA a w) *
        (branchB a w - (2 * w * x + (a ^ 2 + w ^ 2))) = (2 * w) ^ 2 * (eggU a w x * (a ^ 2 - x ^ 2)) := by
      have hf := oval_factor a w x
      unfold eggU at hf ⊢
      linear_combination (2 * w * x + a ^ 2 + w ^ 2) * hf
    rw [e, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity), one_mul, mul_inv]
  simp only [hpt] at hsub
  rw [intervalIntegral.integral_const_mul, integral_oval hw.le hwa, smul_eq_mul] at hsub
  rw [hsB]
  have := mul_left_cancel₀ (inv_ne_zero h2w) hsub
  rw [← this]
  ring

end Period

/-! ## §2 The lifts round the degenerate fibres -/

section Loops

open Complex

/-- [definition] The modulus over `ℂ`, `λ(β) = ((1 − β)/(1 + β))²`. -/
noncomputable def lambdaC (β : ℂ) : ℂ := ((1 - β) / (1 + β)) ^ 2

/-- [definition] One whole turn of the unit circle, `turn t = e^(2πit)`. -/
noncomputable def turn (t : ℝ) : ℂ := Complex.exp (2 * π * t * I)

/-- [definition] The loop round the neck `β = 1`: `β = 1 + r e^(2πit)`. -/
noncomputable def neckLoop (r t : ℝ) : ℂ := 1 + r * turn t

/-- [definition] The loop round the ellipse `β = 0`: `β = r e^(2πit)`. -/
noncomputable def ellipseLoop (r t : ℝ) : ℂ := r * turn t

/-- [proved-standard; formal-checked] `turn 0 = 1`. -/
theorem turn_zero : turn 0 = 1 := by simp [turn]

/-- [proved-standard; formal-checked] `turn 1 = e^(2πi) = 1`: the loop closes. -/
theorem turn_one : turn 1 = 1 := by simp [turn, Complex.exp_two_pi_mul_I]

/-- [proved-standard; formal-checked] `turn` is continuous. -/
theorem continuous_turn : Continuous turn := by unfold turn; fun_prop

/-- [proved-standard; formal-checked] `‖turn t‖ = 1`. -/
theorem norm_turn (t : ℝ) : ‖turn t‖ = 1 := by
  unfold turn
  rw [show (2 * π * t * I : ℂ) = ((2 * π * t : ℝ) : ℂ) * I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- [proved-standard; formal-checked] For `|r| < c`, `c + r e^(2πit)` has positive real part. -/
theorem re_add_turn_pos {c r : ℝ} (hrc : |r| < c) (t : ℝ) : 0 < ((c : ℂ) + r * turn t).re := by
  have h := Complex.abs_re_le_norm ((r : ℂ) * turn t)
  rw [norm_mul, norm_turn, mul_one, Complex.norm_real, Real.norm_eq_abs] at h
  rw [Complex.add_re, Complex.ofReal_re]
  linarith [(abs_le.mp h).1]

/-- [proved-standard; formal-checked] For `|r| < c`, `c + r e^(2πit)` lies in the slit plane. -/
theorem slitPlane_add_turn {c r : ℝ} (hrc : |r| < c) (t : ℝ) : (c : ℂ) + r * turn t ∈ slitPlane :=
  Complex.mem_slitPlane_iff.mpr (Or.inl (re_add_turn_pos hrc t))

/-- [proved-standard; formal-checked] For `|r| < c`, `t ↦ Log(c + r e^(2πit))` is continuous. -/
theorem continuous_log_add_turn {c r : ℝ} (hrc : |r| < c) :
    Continuous fun t : ℝ => Complex.log ((c : ℂ) + r * turn t) := by
  have hc : Continuous fun t : ℝ => (c : ℂ) + r * turn t := by have := continuous_turn; fun_prop
  exact hc.clog (slitPlane_add_turn hrc)

/-- [proved-standard; formal-checked] For `|r| < c`, `c + r e^(2πit) ≠ 0`. -/
theorem add_turn_ne_zero {c r : ℝ} (hrc : |r| < c) (t : ℝ) : (c : ℂ) + r * turn t ≠ 0 :=
  Complex.slitPlane_ne_zero (slitPlane_add_turn hrc t)

/-- [proved-standard; formal-checked] **Two continuous lifts gain the same amount** over `[0, 1]`
(from `RatioPhase.continuous_lift_unique`). -/
theorem lift_gain {R L L' : ℝ → ℂ} (hL : ContinuousOn L (Icc 0 1)) (hL' : ContinuousOn L' (Icc 0 1))
    (h : ∀ t ∈ Icc (0 : ℝ) 1, Complex.exp (L t) = R t) (h' : ∀ t ∈ Icc (0 : ℝ) 1, Complex.exp (L' t) = R t) :
    L' 1 - L' 0 = L 1 - L 0 := by
  obtain ⟨n, hn⟩ := Holonics.Objects.RatioPhase.continuous_lift_unique zero_le_one hL hL' h h'
    (fun t ht => by rw [← h t ht]; exact Complex.exp_ne_zero _)
  rw [hn 1 (right_mem_Icc.mpr zero_le_one), hn 0 (left_mem_Icc.mpr zero_le_one)]
  ring

/-- [proved-derived; formal-checked] `1 − λ = 4β/(1 + β)²`. -/
theorem one_sub_lambdaC {β : ℂ} (h : 1 + β ≠ 0) : 1 - lambdaC β = 4 * β / (1 + β) ^ 2 := by
  unfold lambdaC
  field_simp
  ring

/-- [proved-derived; formal-checked] **The local orders**: `λ = (β − 1)² · (1 + β)⁻²` has a double zero at the neck
`β = 1`, and `1 − λ = β · 4(1 + β)⁻²` a simple zero at the ellipse `β = 0`. -/
theorem lambdaC_orders {β : ℂ} (h : 1 + β ≠ 0) :
    lambdaC β = (β - 1) ^ 2 * ((1 + β) ^ 2)⁻¹ ∧ 1 - lambdaC β = β * (4 * ((1 + β) ^ 2)⁻¹) := by
  refine ⟨?_, ?_⟩
  · unfold lambdaC
    rw [div_pow, div_eq_mul_inv]
    ring
  · rw [one_sub_lambdaC h]
    ring

/-- [proved-derived; formal-checked] On the real line `lambdaC` is the owner's `EggModular.eggLambda`. -/
theorem lambdaC_ofReal (β : ℝ) : lambdaC (β : ℂ) = (Geometry.EggModular.eggLambda β : ℂ) := by
  unfold lambdaC Geometry.EggModular.eggLambda
  push_cast
  ring

/-- [definition] An explicit lift of `λ` round the neck, `2(log r + iπ + 2πit) − 2 Log(2 + r e^(2πit))`. -/
noncomputable def neckLift (r t : ℝ) : ℂ :=
  2 * ((Real.log r : ℂ) + π * I + 2 * π * t * I) - 2 * Complex.log (2 + r * turn t)

/-- [proved-standard; formal-checked] `e^(2z) = (e^z)²`. -/
theorem cexp_two_mul (z : ℂ) : Complex.exp (2 * z) = Complex.exp z ^ 2 := by
  rw [two_mul, Complex.exp_add, sq]

/-- [proved-derived; formal-checked] `neckLift` is a lift: `e^(neckLift r t) = λ(1 + r e^(2πit))`. -/
theorem neckLift_spec {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (t : ℝ) :
    Complex.exp (neckLift r t) = lambdaC (neckLoop r t) := by
  have h2 : (2 : ℂ) + r * turn t ≠ 0 := by
    exact_mod_cast add_turn_ne_zero (c := 2) (by rw [abs_of_pos hr0]; linarith) t
  unfold neckLift lambdaC neckLoop
  rw [Complex.exp_sub, cexp_two_mul, cexp_two_mul, Complex.exp_log h2, Complex.exp_add, Complex.exp_add,
    ← Complex.ofReal_exp, Real.exp_log hr0, Complex.exp_pi_mul_I]
  have : Complex.exp (2 * π * t * I) = turn t := rfl
  rw [this, div_pow]
  congr 1
  · ring
  · ring

/-- [proved-derived; formal-checked] `neckLift r` is continuous. -/
theorem continuous_neckLift {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) : Continuous (neckLift r) := by
  have hl := continuous_log_add_turn (c := 2) (r := r) (by rw [abs_of_pos hr0]; linarith)
  push_cast at hl
  unfold neckLift
  fun_prop

/-- [proved-derived; formal-checked] **Round the neck `λ` winds twice**: every continuous lift of `λ` along
`β = 1 + r e^(2πit)` gains `4πi`. -/
theorem neck_lambda_gain {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) {L : ℝ → ℂ} (hL : ContinuousOn L (Icc 0 1))
    (hlift : ∀ t ∈ Icc (0 : ℝ) 1, Complex.exp (L t) = lambdaC (neckLoop r t)) :
    L 1 - L 0 = 4 * π * I := by
  rw [lift_gain (continuous_neckLift hr0 hr1).continuousOn hL (fun t _ => neckLift_spec hr0 hr1 t) hlift]
  unfold neckLift
  rw [turn_one, turn_zero]
  push_cast
  ring

/-- [definition] An explicit lift of `1 − λ` round the neck, `Log 4 + Log β − 2 Log(1 + β)`. -/
noncomputable def neckLiftOneSub (r t : ℝ) : ℂ :=
  Complex.log 4 + Complex.log (1 + r * turn t) - 2 * Complex.log (2 + r * turn t)

/-- [proved-derived; formal-checked] `neckLiftOneSub` is a lift of `1 − λ` along the neck's loop. -/
theorem neckLiftOneSub_spec {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (t : ℝ) :
    Complex.exp (neckLiftOneSub r t) = 1 - lambdaC (neckLoop r t) := by
  have h1 : (1 : ℂ) + r * turn t ≠ 0 := by
    exact_mod_cast add_turn_ne_zero (c := 1) (by rw [abs_of_pos hr0]; linarith) t
  have h2 : (2 : ℂ) + r * turn t ≠ 0 := by
    exact_mod_cast add_turn_ne_zero (c := 2) (by rw [abs_of_pos hr0]; linarith) t
  have h2' : 1 + neckLoop r t ≠ 0 := by
    unfold neckLoop; rw [show (1 : ℂ) + (1 + r * turn t) = 2 + r * turn t by ring]; exact h2
  rw [one_sub_lambdaC h2']
  unfold neckLiftOneSub neckLoop
  rw [Complex.exp_sub, Complex.exp_add, cexp_two_mul, Complex.exp_log h1, Complex.exp_log h2,
    Complex.exp_log (by norm_num)]
  congr 1
  ring

/-- [proved-derived; formal-checked] Round the neck `1 − λ` does not wind: every continuous lift gains `0`. -/
theorem neck_one_sub_gain {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) {L : ℝ → ℂ} (hL : ContinuousOn L (Icc 0 1))
    (hlift : ∀ t ∈ Icc (0 : ℝ) 1, Complex.exp (L t) = 1 - lambdaC (neckLoop r t)) :
    L 1 - L 0 = 0 := by
  have c1 := continuous_log_add_turn (c := 1) (r := r) (by rw [abs_of_pos hr0]; linarith)
  have c2 := continuous_log_add_turn (c := 2) (r := r) (by rw [abs_of_pos hr0]; linarith)
  push_cast at c1 c2
  have hc : Continuous (neckLiftOneSub r) := by unfold neckLiftOneSub; fun_prop
  rw [lift_gain hc.continuousOn hL (fun t _ => neckLiftOneSub_spec hr0 hr1 t) hlift]
  unfold neckLiftOneSub
  rw [turn_one, turn_zero, sub_self]

/-- [definition] An explicit lift of `1 − λ` round the ellipse, `Log 4 + log r + 2πit − 2 Log(1 + r e^(2πit))`. -/
noncomputable def ellipseLift (r t : ℝ) : ℂ :=
  Complex.log 4 + ((Real.log r : ℂ) + 2 * π * t * I) - 2 * Complex.log (1 + r * turn t)

/-- [proved-derived; formal-checked] `ellipseLift` is a lift of `1 − λ` along the ellipse's loop. -/
theorem ellipseLift_spec {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (t : ℝ) :
    Complex.exp (ellipseLift r t) = 1 - lambdaC (ellipseLoop r t) := by
  have h1 : (1 : ℂ) + r * turn t ≠ 0 := by
    exact_mod_cast add_turn_ne_zero (c := 1) (by rw [abs_of_pos hr0]; linarith) t
  rw [one_sub_lambdaC (by unfold ellipseLoop; exact h1)]
  unfold ellipseLift ellipseLoop
  rw [Complex.exp_sub, Complex.exp_add, Complex.exp_add, cexp_two_mul, Complex.exp_log h1,
    Complex.exp_log (by norm_num), ← Complex.ofReal_exp, Real.exp_log hr0]
  rfl

/-- [proved-derived; formal-checked] **Round the ellipse `1 − λ` winds once**: every continuous lift of `1 − λ`
along `β = r e^(2πit)` gains `2πi`. -/
theorem ellipse_one_sub_gain {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) {L : ℝ → ℂ} (hL : ContinuousOn L (Icc 0 1))
    (hlift : ∀ t ∈ Icc (0 : ℝ) 1, Complex.exp (L t) = 1 - lambdaC (ellipseLoop r t)) :
    L 1 - L 0 = 2 * π * I := by
  have c1 := continuous_log_add_turn (c := 1) (r := r) (by rw [abs_of_pos hr0]; linarith)
  push_cast at c1
  have hc : Continuous (ellipseLift r) := by unfold ellipseLift; fun_prop
  rw [lift_gain hc.continuousOn hL (fun t _ => ellipseLift_spec hr0 hr1 t) hlift]
  unfold ellipseLift
  rw [turn_one, turn_zero]
  push_cast
  ring

/-- [definition] An explicit lift of `λ` round the ellipse, `2(Log(1 − β) − Log(1 + β))`. -/
noncomputable def ellipseLiftLambda (r t : ℝ) : ℂ :=
  2 * (Complex.log (1 + (-r : ℝ) * turn t) - Complex.log (1 + r * turn t))

/-- [proved-derived; formal-checked] Round the ellipse `λ` does not wind: every continuous lift gains `0`. -/
theorem ellipse_lambda_gain {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) {L : ℝ → ℂ} (hL : ContinuousOn L (Icc 0 1))
    (hlift : ∀ t ∈ Icc (0 : ℝ) 1, Complex.exp (L t) = lambdaC (ellipseLoop r t)) :
    L 1 - L 0 = 0 := by
  have hr : |r| < 1 := by rw [abs_of_pos hr0]; exact hr1
  have hr' : |-r| < 1 := by rw [abs_neg]; exact hr
  have c1 := continuous_log_add_turn (c := 1) hr
  have c2 := continuous_log_add_turn (c := 1) hr'
  push_cast at c1 c2
  have hc : Continuous (ellipseLiftLambda r) := by
    unfold ellipseLiftLambda; push_cast; fun_prop
  have hspec : ∀ t, Complex.exp (ellipseLiftLambda r t) = lambdaC (ellipseLoop r t) := by
    intro t
    have h1 := add_turn_ne_zero (c := 1) hr t
    have h2 := add_turn_ne_zero (c := 1) hr' t
    push_cast at h1 h2
    unfold ellipseLiftLambda lambdaC ellipseLoop
    push_cast
    rw [cexp_two_mul, Complex.exp_sub, Complex.exp_log h1, Complex.exp_log h2]
    ring
  rw [lift_gain hc.continuousOn hL (fun t _ => hspec t) hlift]
  unfold ellipseLiftLambda
  rw [turn_one, turn_zero, sub_self]

end Loops

/-! ## §3 The null monodromy -/

section Moves

open PowerSeries Holonics.Geometry Holonics.Geometry.HypergeometricMonodromy
open scoped MatrixGroups

variable {K : Type*} [Field K]

/-- [proved-standard; formal-checked] `A² = [[1, 4], [0, 1]]`. -/
theorem coe_A_sq : ((LegendreLevelTwo.A ^ 2 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 4; 0, 1] := by
  rw [← zpow_natCast, LegendreLevelTwo.coe_A_zpow]
  norm_num

/-- [proved-standard; formal-checked] The continuation adds: `ℓ ↦ ℓ + κ + κ'` is `ℓ ↦ ℓ + κ'` then `ℓ ↦ ℓ + κ`. -/
theorem shiftLog_add (κ κ' : K) (p : K⟦X⟧ × K⟦X⟧) : shiftLog (κ + κ') p = shiftLog κ (shiftLog κ' p) := by
  obtain ⟨A, B⟩ := p
  simp only [shiftLog, add_smul]
  refine Prod.ext ?_ rfl
  simp only
  abel

/-- [proved-standard; formal-checked] The continuation is linear on combinations of two pairs. -/
theorem shiftLog_sum_smul (κ : K) (c : Fin 2 → K) (p : Fin 2 → K⟦X⟧ × K⟦X⟧) :
    shiftLog κ (∑ i, c i • p i) = ∑ i, c i • shiftLog κ (p i) := by
  simp only [Fin.sum_univ_two, shiftLog, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    Prod.smul_mk, Prod.mk_add_mk, smul_add, smul_smul, mul_comm κ]
  exact Prod.ext (by abel_nf) rfl

/-- [proved-standard; formal-checked] **Two Legendre loops round `λ = 0`**: `ℓ ↦ ℓ + 4κ`, composed from two moves
`ℓ ↦ ℓ + 2κ`, moves the basis `(F, (Fℓ + G)/κ)` by `A² = [[1, 4], [0, 1]]` (column convention). -/
theorem shiftLog_legendreBasis_four {κ : K} (hκ : κ ≠ 0) (G : K⟦X⟧) (j : Fin 2) :
    shiftLog (4 * κ) (legendreBasis κ G j) =
      ∑ i, ((((LegendreLevelTwo.A ^ 2 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : K) •
        legendreBasis κ G i := by
  rw [show (4 : K) * κ = 2 * κ + 2 * κ by ring, shiftLog_add, shiftLog_legendreBasis hκ, shiftLog_sum_smul]
  simp only [shiftLog_legendreBasis hκ, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  rw [Matrix.SpecialLinearGroup.coe_pow, sq, Matrix.mul_apply]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- [proved-standard; formal-checked] `πi ≠ 0`. -/
theorem piI_ne_zero : (π * Complex.I : ℂ) ≠ 0 :=
  mul_ne_zero (Complex.ofReal_ne_zero.2 Real.pi_ne_zero) Complex.I_ne_zero

/-- [proved-derived; formal-checked] **The neck's move**: the formal logarithm shifted by the gain of any continuous
lift of `λ` round `β = 1` moves the basis `(F, (Fℓ + G)/(πi))` by `A² = [[1, 4], [0, 1]]`. -/
theorem neck_move {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) {L : ℝ → ℂ} (hL : ContinuousOn L (Icc 0 1))
    (hlift : ∀ t ∈ Icc (0 : ℝ) 1, Complex.exp (L t) = lambdaC (neckLoop r t)) (G : ℂ⟦X⟧) (j : Fin 2) :
    shiftLog (L 1 - L 0) (legendreBasis (π * Complex.I) G j) =
      ∑ i, ((((LegendreLevelTwo.A ^ 2 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ℂ) •
        legendreBasis (π * Complex.I) G i := by
  rw [neck_lambda_gain hr0 hr1 hL hlift, show (4 : ℂ) * π * Complex.I = 4 * (π * Complex.I) by ring]
  exact shiftLog_legendreBasis_four piI_ne_zero G j

/-- [proved-derived; formal-checked] **The ellipse's move**: the formal logarithm (read in `μ = 1 − λ`) shifted by
the gain of any continuous lift of `1 − λ` round `β = 0` moves the basis by `A = [[1, 2], [0, 1]]`. -/
theorem ellipse_move {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) {M : ℝ → ℂ} (hM : ContinuousOn M (Icc 0 1))
    (hlift : ∀ t ∈ Icc (0 : ℝ) 1, Complex.exp (M t) = 1 - lambdaC (ellipseLoop r t)) (G : ℂ⟦X⟧) (j : Fin 2) :
    shiftLog (M 1 - M 0) (legendreBasis (π * Complex.I) G j) =
      ∑ i, (((LegendreLevelTwo.A : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ℂ) • legendreBasis (π * Complex.I) G i := by
  rw [ellipse_one_sub_gain hr0 hr1 hM hlift]
  exact continuation_round_zero G j

/-- [proved-standard; formal-checked] `B⁻¹ = S A S⁻¹` in `SL(2, ℤ)`: the owner's move round `λ = 1` in the basis at
`0` is conjugate to `A`. -/
theorem B_inv_eq_conj_A :
    LegendreLevelTwo.B⁻¹ = ModularGroup.S * LegendreLevelTwo.A * ModularGroup.S⁻¹ := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.adjugate_fin_two, ModularGroup.coe_S,
    LegendreLevelTwo.coe_A, LegendreLevelTwo.coe_B]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

open Matrix (trace) in
/-- [proved-standard; formal-checked] **Both moves are shears**: `A` and `A²` have trace `2`, are not `1`, satisfy
`(M − 1)² = 0`, and are conjugate over `ℚ` to `T = [[1, 1], [0, 1]]`. -/
theorem moves_are_shears :
    trace (LegendreLevelTwo.A : Matrix (Fin 2) (Fin 2) ℤ) = 2 ∧
      trace ((LegendreLevelTwo.A ^ 2 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = 2 ∧
      LegendreLevelTwo.A ≠ 1 ∧ LegendreLevelTwo.A ^ 2 ≠ 1 ∧
      ((LegendreLevelTwo.A : Matrix (Fin 2) (Fin 2) ℤ) - 1) ^ 2 = 0 ∧
      (((LegendreLevelTwo.A ^ 2 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) - 1) ^ 2 = 0 ∧
      (∃ P : GL (Fin 2) ℚ, conjBy P (toK LegendreLevelTwo.A) = toK ModularGroup.T) ∧
      ∃ P : GL (Fin 2) ℚ, conjBy P (toK (LegendreLevelTwo.A ^ 2)) = toK ModularGroup.T := by
  have hA := LegendreLevelTwo.coe_A
  have hA2 := coe_A_sq
  have hne : ∀ g : SL(2, ℤ), (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 ≠ 0 → toK (K := ℚ) g ≠ 1 := by
    intro g hg h
    apply hg
    have := congrArg (fun g : SL(2, ℚ) => (g : Matrix (Fin 2) (Fin 2) ℚ) 0 1) h
    simp only [coe_toK_apply, Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1)]
      at this
    exact_mod_cast this
  have htr : ∀ g : SL(2, ℤ), trace (g : Matrix (Fin 2) (Fin 2) ℤ) = 2 →
      trace ((toK (K := ℚ) g : SL(2, ℚ)) : Matrix (Fin 2) (Fin 2) ℚ) = 2 := by
    intro g hg
    rw [Matrix.trace_fin_two] at hg ⊢
    simp only [coe_toK_apply]
    exact_mod_cast hg
  have t1 : trace (LegendreLevelTwo.A : Matrix (Fin 2) (Fin 2) ℤ) = 2 := by
    rw [hA, Matrix.trace_fin_two_of]; norm_num
  have t2 : trace ((LegendreLevelTwo.A ^ 2 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = 2 := by
    rw [hA2, Matrix.trace_fin_two_of]; norm_num
  have n1 : (LegendreLevelTwo.A : Matrix (Fin 2) (Fin 2) ℤ) 0 1 ≠ 0 := by rw [hA]; simp
  have n2 : ((LegendreLevelTwo.A ^ 2 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 ≠ 0 := by rw [hA2]; simp
  refine ⟨t1, t2, fun h => n1 (by rw [h]; simp), fun h => n2 (by rw [h]; simp), ?_, ?_,
    exists_conj_shear _ (htr _ t1) (hne _ n1), exists_conj_shear _ (htr _ t2) (hne _ n2)⟩
  · rw [hA]; ext i j; fin_cases i <;> fin_cases j <;> simp [sq, Matrix.mul_apply, Fin.sum_univ_two]
  · rw [hA2]; ext i j; fin_cases i <;> fin_cases j <;> simp [sq, Matrix.mul_apply, Fin.sum_univ_two]

/-- [proved-derived; formal-checked] **The shears' entries are the discriminant's orders**: `4` for `A²` at the neck,
where the discriminant is `(a − w)⁴` times a cofactor `256 a⁸ ≠ 0` at `w = a`, and `2` for `A` at the ellipse, where
it is `w²` times a cofactor `16 a¹⁰ ≠ 0` at `w = 0`. -/
theorem shear_entries_discriminant_orders {a : ℝ} (ha : a ≠ 0) :
    ((LegendreLevelTwo.A ^ 2 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = 4 ∧
      (LegendreLevelTwo.A : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = 2 ∧
      (∀ w : ℝ, (legendreCubicPoly (branchA a w) (branchB a w)).discr =
        (a - w) ^ 4 * (16 * a ^ 2 * w ^ 2 * (a + w) ^ 4)) ∧ 256 * a ^ 8 ≠ 0 ∧
      (∀ w : ℝ, (legendreCubicPoly (branchA a w) (branchB a w)).discr =
        w ^ 2 * (16 * a ^ 2 * (a ^ 2 - w ^ 2) ^ 4)) ∧ 16 * a ^ 10 ≠ 0 := by
  obtain ⟨h1, -, h3, h4, -, h6⟩ := egg_discr_orders (K := ℝ) two_ne_zero ha
  refine ⟨by rw [coe_A_sq]; rfl, by rw [LegendreLevelTwo.coe_A]; rfl, h4, h6, h1, h3⟩

end Moves

/-! ## §4 A witness: `a = 2`, `w = 1`, `b = 1` -/

open Holonics.Geometry in
open scoped MatrixGroups in
/-- [proved-derived; formal-checked] **The egg `a = 2, w = 1, b = 1`**: `λ = 1/9`, its oval integral and oval period
are `(2/3) K(√(8/9))`, and its neck move `A² = [[1, 4], [0, 1]]` has trace `2`. -/
theorem egg_211_period :
    branchA (2 : ℝ) 1 / branchB 2 1 = 1 / 9 ∧
      ∫ x in (-2 : ℝ)..2, (√(eggU 2 1 x * (2 ^ 2 - x ^ 2)))⁻¹ = 2 / 3 * ellipticK (√(8 / 9)) ∧
      ovalPeriod 2 1 1 = 2 / 3 * ellipticK (√(8 / 9)) ∧
      ((LegendreLevelTwo.A ^ 2 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 4; 0, 1] ∧
      Matrix.trace ((LegendreLevelTwo.A ^ 2 : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = 2 := by
  have hl : branchA (2 : ℝ) 1 / branchB 2 1 = 1 / 9 := by unfold branchA branchB; norm_num
  have hK : 2 / (1 * (2 + 1)) * ellipticK (√(1 - branchA (2 : ℝ) 1 / branchB 2 1)) =
      2 / 3 * ellipticK (√(8 / 9)) := by
    rw [hl]; norm_num
  have hI := integral_oval (a := 2) (w := 1) (by norm_num) (by norm_num) 1
  simp only [one_mul] at hI
  refine ⟨hl, ?_, ?_, coe_A_sq, (moves_are_shears).2.1⟩
  · rw [hI, ← hK, one_mul]
  · rw [ovalPeriod_eq (by norm_num) (by norm_num) (by norm_num), hK]

end Holonics.EllipticCurve.EggPeriod
