import HolonicsResearch.Zeta.ModularScatteringResidual

/-!
# The paired tail bound for the modular scattering residual

`ModularScatteringResidual` identifies the signed residual of the modular scattering current,
`phi'/phi - (polar + 2 comb_R(2w-1) - 2 comb_R(2w)) = 2 e_R(2w-1) - 2 e_R(2w)`, and on the
`R/2` half disc `2 e_R(s) = (log tail_R)'(s)`.  Its published estimate is separate: each
remainder is bounded alone by `2 |s - 1/2| tailInvSq`, so the two bounds are added at the two
pulled-back arguments `a = 2w-1` and `b = 2w` and the cancellation between them is not used.

This owner composes before it takes magnitudes.  The computational object is the helical pair
interaction.  The reflection `rho |-> 1 - rho` is the dyad's half-turn `U`: it pairs each zero
of the tail with its reflection, and the tank of an index (`FosterClassProduct.tank`) is already
the sum of the two members of the pair, which is why `e_R = (log tail_R)'/2`.  Read at two
arguments, the residual is a signed face of the xi current's remainder at two places
(faces and placement), and the pair term of one index is

```text
tank(a) - tank(b) = (b - a) [ 1/((a-rho)(b-rho)) + 1/((a-(1-rho))(b-(1-rho))) ]
                  = 2 (b - a) (r^2 + x y) / ((r^2 - x^2)(r^2 - y^2)),
```

with `x = a - 1/2`, `y = b - 1/2`, `r = rho - 1/2` (`pair_identity`, `tankC_sub_eq_pair`).  The
summands are `O(1/|rho - 1/2|^2)`, so the tail sum over the full reflection-invariant multiset,
the zeros repeated by multiplicity (`Idx f`), is absolutely summable.  It is never split into
the two sums of `1/(a-rho)` and `1/(b-rho)`, which are not absolutely convergent.  The reflection
of that multiset is the equivalence `reflectIdx` (`ctr (U i) = - ctr i`, fibres of equal size),
and `tailPair_eq_two_mul_tsum` writes the residual as `2 (b - a) sum 1/((a-rho)(b-rho))` over it;
`tailPair_eq_two_mul_tsum_zeros` reads the same sum over the zeros with `m_rho` explicit.

For the half-disc chart positions `alpha = |a-1/2|/(R/2)` and `beta = |b-1/2|/(R/2)`, both
`< 1`, and `S_R = tailInvSq f R`, this file proves

* the paired bound `|E| <= |b-a| * 2(1+alpha beta)/((1-alpha^2)(1-beta^2)) * S_R`;
* the sharper separate bound
  `|E| <= (2|a-1/2|/(1-alpha^2) + 2|b-1/2|/(1-beta^2)) * S_R`, kept beside it;
* their minimum where both hold;
* on the common closed `R/8` chart (`alpha, beta <= 1/4`) the paired coefficient is at most the
  rational `544/225` and the separate one at most `32/15 (|x| + |y|)`; the published coefficient
  is `4 (|x| + |y|)`, and `|x| + |y| >= |y - x| = 1`;
* the chart facts: the common closed `R/8` chart at both `2w-1` and `2w` is nonempty only for
  `R >= 4`, and with `w != 1/2` only for `R > 4` (at `R = 4` it leaves only `w = 1/2`).

Each theorem keeps its own endpoint hypotheses: the tail level needs only the ball memberships;
the residual level through `modularScattering_current_residual` needs `w != 0, 1/2, 1`,
`xi(2w-1) != 0`, `xi(2w) != 0` and the ball memberships.  No hypothesis is added.

This bounds a magnitude of the residual.  It says nothing about its sign, nothing about where
the zeros lie, and nothing about the Riemann hypothesis.  Refs #62, #63.
-/

noncomputable section

namespace Holonics.Zeta.ModularScatteringPairedTail

open Complex Metric Set Filter Topology
open Holonics.Zeta.RiemannXi
open Holonics.Zeta.FosterClassLandau
open Holonics.Zeta.FosterClassCount
open Holonics.Zeta.FosterClassProduct
open Holonics.Zeta.FosterClassSplit
open Holonics.Zeta.ModularScatteringResidual
open scoped Classical

/-! ## 1. The pair algebra, with no Foster hypothesis -/

/-- The tank of the centred zero `r` read at the centred point `x`: the value of the index tank
`FosterClassProduct.tank`, in the coordinates `x = z - 1/2`, `r = rho - 1/2`. -/
def tankC (r x : ℂ) : ℂ := 2 * x / (x ^ 2 - r ^ 2)

/-- One member of the pair `{rho, 1 - rho}` read at the two centred points `x`, `y`:
`1/((x - r)(y - r))`.  The other member is the same kernel at `-r`. -/
def pairKernel (x y r : ℂ) : ℂ := 1 / ((x - r) * (y - r))

/-- The coefficient of the paired bound, `2(1 + alpha beta) / ((1 - alpha^2)(1 - beta^2))`. -/
def pairedCoeff (α β : ℝ) : ℝ := 2 * (1 + α * β) / ((1 - α ^ 2) * (1 - β ^ 2))

/-- The coefficient of one argument in the separate bound, `2 / (1 - alpha^2)`. -/
def separateCoeff (α : ℝ) : ℝ := 2 / (1 - α ^ 2)

/-- The position of `s` in the half-disc chart of radius `R/2`: `alpha = |s - 1/2| / (R/2)`. -/
def chartRatio (R : ℝ) (s : ℂ) : ℝ := ‖s - 1 / 2‖ / (R / 2)

theorem pairedCoeff_nonneg {α β : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) : 0 ≤ pairedCoeff α β := by
  unfold pairedCoeff
  have h1 : 0 ≤ 1 - α ^ 2 := by nlinarith
  have h2 : 0 ≤ 1 - β ^ 2 := by nlinarith
  have h3 : 0 ≤ α * β := mul_nonneg hα0 hβ0
  exact div_nonneg (by linarith) (mul_nonneg h1 h2)

theorem separateCoeff_nonneg {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) : 0 ≤ separateCoeff α := by
  unfold separateCoeff
  have h1 : 0 ≤ 1 - α ^ 2 := by nlinarith
  exact div_nonneg (by norm_num) h1

/-- **The pair identity, composed.**  The difference of two tanks at one centred zero. -/
theorem tankC_sub_tankC {x y r : ℂ} (hx : x ^ 2 ≠ r ^ 2) (hy : y ^ 2 ≠ r ^ 2) :
    tankC r x - tankC r y =
      2 * (y - x) * (r ^ 2 + x * y) / ((r ^ 2 - x ^ 2) * (r ^ 2 - y ^ 2)) := by
  have hx' : x ^ 2 - r ^ 2 ≠ 0 := sub_ne_zero.mpr hx
  have hy' : y ^ 2 - r ^ 2 ≠ 0 := sub_ne_zero.mpr hy
  have hx'' : r ^ 2 - x ^ 2 ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  have hy'' : r ^ 2 - y ^ 2 ≠ 0 := sub_ne_zero.mpr (Ne.symm hy)
  unfold tankC
  rw [div_sub_div _ _ hx' hy', div_eq_div_iff (mul_ne_zero hx' hy') (mul_ne_zero hx'' hy'')]
  ring

/-- **The pair identity.**  The two members of a reflection pair, read at two points, add to
one rational function of `r^2`:
`1/((x-r)(y-r)) + 1/((x+r)(y+r)) = 2 (r^2 + x y) / ((r^2 - x^2)(r^2 - y^2))`. -/
theorem pair_identity {x y r : ℂ} (hxm : x - r ≠ 0) (hxp : x + r ≠ 0) (hym : y - r ≠ 0)
    (hyp : y + r ≠ 0) :
    1 / ((x - r) * (y - r)) + 1 / ((x + r) * (y + r)) =
      2 * (r ^ 2 + x * y) / ((r ^ 2 - x ^ 2) * (r ^ 2 - y ^ 2)) := by
  have h1 : (x - r) * (y - r) ≠ 0 := mul_ne_zero hxm hym
  have h2 : (x + r) * (y + r) ≠ 0 := mul_ne_zero hxp hyp
  have h3 : (r ^ 2 - x ^ 2) * (r ^ 2 - y ^ 2) ≠ 0 := by
    have e : (r ^ 2 - x ^ 2) * (r ^ 2 - y ^ 2) = ((x - r) * (x + r)) * ((y - r) * (y + r)) := by
      ring
    rw [e]
    exact mul_ne_zero (mul_ne_zero hxm hxp) (mul_ne_zero hym hyp)
  rw [div_add_div _ _ h1 h2, div_eq_div_iff (mul_ne_zero h1 h2) h3]
  ring

/-- The tank difference of one index is `(y - x)` times the sum of the two members of its pair. -/
theorem tankC_sub_eq_pair {x y r : ℂ} (hxm : x - r ≠ 0) (hxp : x + r ≠ 0) (hym : y - r ≠ 0)
    (hyp : y + r ≠ 0) :
    tankC r x - tankC r y =
      (y - x) * (1 / ((x - r) * (y - r)) + 1 / ((x + r) * (y + r))) := by
  have hx : x ^ 2 ≠ r ^ 2 := by
    intro h
    have h0 : (x - r) * (x + r) = 0 := by linear_combination h
    exact mul_ne_zero hxm hxp h0
  have hy : y ^ 2 ≠ r ^ 2 := by
    intro h
    have h0 : (y - r) * (y + r) = 0 := by linear_combination h
    exact mul_ne_zero hym hyp h0
  rw [tankC_sub_tankC hx hy, pair_identity hxm hxp hym hyp]
  ring

theorem sub_ne_zero_of_norm_lt {x r : ℂ} (h : ‖x‖ < ‖r‖) : x - r ≠ 0 := by
  intro h0
  have : x = r := sub_eq_zero.mp h0
  rw [this] at h
  exact lt_irrefl _ h

theorem add_ne_zero_of_norm_lt {x r : ℂ} (h : ‖x‖ < ‖r‖) : x + r ≠ 0 := by
  intro h0
  have : x = -r := eq_neg_of_add_eq_zero_left h0
  rw [this, norm_neg] at h
  exact lt_irrefl _ h

/-- **The paired bound for one index.**  With `|x| <= alpha |r|` and `|y| <= beta |r|`,
`alpha, beta < 1`, the pair term is at most `|y - x| * 2(1+alpha beta)/((1-alpha^2)(1-beta^2))`
times `1/|r|^2`. -/
theorem norm_tankC_sub_le {x y r : ℂ} {α β : ℝ} (hr : r ≠ 0)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hx : ‖x‖ ≤ α * ‖r‖) (hy : ‖y‖ ≤ β * ‖r‖) :
    ‖tankC r x - tankC r y‖ ≤ ‖y - x‖ * pairedCoeff α β * (‖r‖ ^ 2)⁻¹ := by
  have hrn : 0 < ‖r‖ := norm_pos_iff.mpr hr
  have hm0 : 0 < ‖r‖ ^ 2 := by positivity
  have hα2 : α ^ 2 < 1 := by nlinarith
  have hβ2 : β ^ 2 < 1 := by nlinarith
  have hxn : 0 ≤ ‖x‖ := norm_nonneg _
  have hyn : 0 ≤ ‖y‖ := norm_nonneg _
  have hx2 : ‖x ^ 2‖ ≤ α ^ 2 * ‖r‖ ^ 2 := by
    rw [norm_pow]
    calc ‖x‖ ^ 2 ≤ (α * ‖r‖) ^ 2 := pow_le_pow_left₀ hxn hx 2
      _ = α ^ 2 * ‖r‖ ^ 2 := by ring
  have hy2 : ‖y ^ 2‖ ≤ β ^ 2 * ‖r‖ ^ 2 := by
    rw [norm_pow]
    calc ‖y‖ ^ 2 ≤ (β * ‖r‖) ^ 2 := pow_le_pow_left₀ hyn hy 2
      _ = β ^ 2 * ‖r‖ ^ 2 := by ring
  have hr2 : ‖r ^ 2‖ = ‖r‖ ^ 2 := norm_pow r 2
  have hxne : x ^ 2 ≠ r ^ 2 := by
    intro h
    have h1 : ‖x ^ 2‖ = ‖r‖ ^ 2 := by rw [h, hr2]
    nlinarith [mul_pos hm0 (sub_pos.mpr hα2)]
  have hyne : y ^ 2 ≠ r ^ 2 := by
    intro h
    have h1 : ‖y ^ 2‖ = ‖r‖ ^ 2 := by rw [h, hr2]
    nlinarith [mul_pos hm0 (sub_pos.mpr hβ2)]
  have hDx : ‖r‖ ^ 2 * (1 - α ^ 2) ≤ ‖r ^ 2 - x ^ 2‖ := by
    have h := norm_sub_norm_le (r ^ 2) (x ^ 2)
    nlinarith [h, hr2, hx2]
  have hDy : ‖r‖ ^ 2 * (1 - β ^ 2) ≤ ‖r ^ 2 - y ^ 2‖ := by
    have h := norm_sub_norm_le (r ^ 2) (y ^ 2)
    nlinarith [h, hr2, hy2]
  have hDxpos : 0 < ‖r‖ ^ 2 * (1 - α ^ 2) := mul_pos hm0 (sub_pos.mpr hα2)
  have hDypos : 0 < ‖r‖ ^ 2 * (1 - β ^ 2) := mul_pos hm0 (sub_pos.mpr hβ2)
  have hD : (‖r‖ ^ 2 * (1 - α ^ 2)) * (‖r‖ ^ 2 * (1 - β ^ 2)) ≤
      ‖r ^ 2 - x ^ 2‖ * ‖r ^ 2 - y ^ 2‖ :=
    mul_le_mul hDx hDy hDypos.le (norm_nonneg _)
  have hDpos : 0 < ‖r ^ 2 - x ^ 2‖ * ‖r ^ 2 - y ^ 2‖ :=
    lt_of_lt_of_le (mul_pos hDxpos hDypos) hD
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  have hnum : ‖2 * (y - x) * (r ^ 2 + x * y)‖ ≤ 2 * ‖y - x‖ * ((1 + α * β) * ‖r‖ ^ 2) := by
    rw [norm_mul, norm_mul, h2]
    have h1 : ‖r ^ 2 + x * y‖ ≤ (1 + α * β) * ‖r‖ ^ 2 := by
      calc ‖r ^ 2 + x * y‖ ≤ ‖r ^ 2‖ + ‖x * y‖ := norm_add_le _ _
        _ = ‖r‖ ^ 2 + ‖x‖ * ‖y‖ := by rw [hr2, norm_mul]
        _ ≤ ‖r‖ ^ 2 + (α * ‖r‖) * (β * ‖r‖) :=
            add_le_add_right (mul_le_mul hx hy hyn (mul_nonneg hα0 hrn.le)) _
        _ = (1 + α * β) * ‖r‖ ^ 2 := by ring
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  have hα' : 1 - α ^ 2 ≠ 0 := (sub_pos.mpr hα2).ne'
  have hβ' : 1 - β ^ 2 ≠ 0 := (sub_pos.mpr hβ2).ne'
  have hr0 : ‖r‖ ≠ 0 := hrn.ne'
  have hcoeff : 0 ≤ ‖y - x‖ * pairedCoeff α β * (‖r‖ ^ 2)⁻¹ :=
    mul_nonneg (mul_nonneg (norm_nonneg _) (pairedCoeff_nonneg hα0 hα1 hβ0 hβ1))
      (inv_nonneg.mpr hm0.le)
  rw [tankC_sub_tankC hxne hyne, norm_div, norm_mul (r ^ 2 - x ^ 2) (r ^ 2 - y ^ 2),
    div_le_iff₀ hDpos]
  calc ‖2 * (y - x) * (r ^ 2 + x * y)‖ ≤ 2 * ‖y - x‖ * ((1 + α * β) * ‖r‖ ^ 2) := hnum
    _ = ‖y - x‖ * pairedCoeff α β * (‖r‖ ^ 2)⁻¹ *
          ((‖r‖ ^ 2 * (1 - α ^ 2)) * (‖r‖ ^ 2 * (1 - β ^ 2))) := by
        unfold pairedCoeff
        field_simp
    _ ≤ ‖y - x‖ * pairedCoeff α β * (‖r‖ ^ 2)⁻¹ * (‖r ^ 2 - x ^ 2‖ * ‖r ^ 2 - y ^ 2‖) :=
        mul_le_mul_of_nonneg_left hD hcoeff

/-- **The separate bound for one index.**  `|tank| <= 2|x|/(1-alpha^2) * 1/|r|^2`. -/
theorem norm_tankC_le {x r : ℂ} {α : ℝ} (hr : r ≠ 0) (hα0 : 0 ≤ α) (hα1 : α < 1)
    (hx : ‖x‖ ≤ α * ‖r‖) :
    ‖tankC r x‖ ≤ separateCoeff α * ‖x‖ * (‖r‖ ^ 2)⁻¹ := by
  have hrn : 0 < ‖r‖ := norm_pos_iff.mpr hr
  have hm0 : 0 < ‖r‖ ^ 2 := by positivity
  have hα2 : α ^ 2 < 1 := by nlinarith
  have hxn : 0 ≤ ‖x‖ := norm_nonneg _
  have hx2 : ‖x ^ 2‖ ≤ α ^ 2 * ‖r‖ ^ 2 := by
    rw [norm_pow]
    calc ‖x‖ ^ 2 ≤ (α * ‖r‖) ^ 2 := pow_le_pow_left₀ hxn hx 2
      _ = α ^ 2 * ‖r‖ ^ 2 := by ring
  have hr2 : ‖r ^ 2‖ = ‖r‖ ^ 2 := norm_pow r 2
  have hDx : ‖r‖ ^ 2 * (1 - α ^ 2) ≤ ‖x ^ 2 - r ^ 2‖ := by
    have h := norm_sub_norm_le (r ^ 2) (x ^ 2)
    have e : ‖x ^ 2 - r ^ 2‖ = ‖r ^ 2 - x ^ 2‖ := norm_sub_rev _ _
    nlinarith [h, hr2, hx2, e]
  have hDpos : 0 < ‖r‖ ^ 2 * (1 - α ^ 2) := mul_pos hm0 (sub_pos.mpr hα2)
  have hDpos' : 0 < ‖x ^ 2 - r ^ 2‖ := lt_of_lt_of_le hDpos hDx
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  have hα' : 1 - α ^ 2 ≠ 0 := (sub_pos.mpr hα2).ne'
  have hr0 : ‖r‖ ≠ 0 := hrn.ne'
  have hsc : 0 ≤ separateCoeff α := separateCoeff_nonneg hα0 hα1
  unfold tankC
  rw [norm_div, norm_mul, h2, div_le_iff₀ hDpos']
  calc 2 * ‖x‖ = separateCoeff α * ‖x‖ * (‖r‖ ^ 2)⁻¹ * (‖r‖ ^ 2 * (1 - α ^ 2)) := by
        unfold separateCoeff
        field_simp
    _ ≤ separateCoeff α * ‖x‖ * (‖r‖ ^ 2)⁻¹ * ‖x ^ 2 - r ^ 2‖ :=
        mul_le_mul_of_nonneg_left hDx
          (mul_nonneg (mul_nonneg hsc hxn) (inv_nonneg.mpr hm0.le))

/-- One member of the pair is absolutely small: `|1/((x-r)(y-r))| <= C / |r|^2`. -/
theorem norm_pairKernel_le {x y r : ℂ} {α β : ℝ} (hr : r ≠ 0)
    (hα1 : α < 1) (hβ1 : β < 1)
    (hx : ‖x‖ ≤ α * ‖r‖) (hy : ‖y‖ ≤ β * ‖r‖) :
    ‖pairKernel x y r‖ ≤ (1 / ((1 - α) * (1 - β))) * (‖r‖ ^ 2)⁻¹ := by
  have hrn : 0 < ‖r‖ := norm_pos_iff.mpr hr
  have hm0 : 0 < ‖r‖ ^ 2 := by positivity
  have h1 : ‖r‖ * (1 - α) ≤ ‖x - r‖ := by
    have h := norm_sub_norm_le r x
    have e : ‖r - x‖ = ‖x - r‖ := norm_sub_rev r x
    nlinarith [h, e, hx]
  have h2 : ‖r‖ * (1 - β) ≤ ‖y - r‖ := by
    have h := norm_sub_norm_le r y
    have e : ‖r - y‖ = ‖y - r‖ := norm_sub_rev r y
    nlinarith [h, e, hy]
  have hα' : 0 < 1 - α := sub_pos.mpr hα1
  have hβ' : 0 < 1 - β := sub_pos.mpr hβ1
  have hpx : 0 < ‖r‖ * (1 - α) := mul_pos hrn hα'
  have hpy : 0 < ‖r‖ * (1 - β) := mul_pos hrn hβ'
  have hprod : (‖r‖ * (1 - α)) * (‖r‖ * (1 - β)) ≤ ‖x - r‖ * ‖y - r‖ :=
    mul_le_mul h1 h2 hpy.le (norm_nonneg _)
  have hprodpos : 0 < ‖x - r‖ * ‖y - r‖ := lt_of_lt_of_le (mul_pos hpx hpy) hprod
  have hc : 0 ≤ (1 / ((1 - α) * (1 - β))) * (‖r‖ ^ 2)⁻¹ :=
    mul_nonneg (one_div_nonneg.mpr (mul_pos hα' hβ').le) (inv_nonneg.mpr hm0.le)
  have h1a : (1 - α) ≠ 0 := hα'.ne'
  have h1b : (1 - β) ≠ 0 := hβ'.ne'
  have hr0 : ‖r‖ ≠ 0 := hrn.ne'
  unfold pairKernel
  rw [norm_div, norm_one, norm_mul, div_le_iff₀ hprodpos]
  calc (1 : ℝ) = (1 / ((1 - α) * (1 - β))) * (‖r‖ ^ 2)⁻¹ *
          ((‖r‖ * (1 - α)) * (‖r‖ * (1 - β))) := by
        field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hprod hc

/-! ### The chart ratios and the exact rational coefficients on the closed `R/8` chart -/

theorem norm_lt_of_mem_ball {R : ℝ} {s : ℂ} (hs : s ∈ ball (1 / 2 : ℂ) (R / 2)) :
    ‖s - 1 / 2‖ < R / 2 := by
  rw [mem_ball, Complex.dist_eq] at hs
  exact hs

theorem chartRatio_nonneg {R : ℝ} (hR : 0 < R) (s : ℂ) : 0 ≤ chartRatio R s := by
  unfold chartRatio
  positivity

theorem chartRatio_lt_one {R : ℝ} (hR : 0 < R) {s : ℂ} (hs : s ∈ ball (1 / 2 : ℂ) (R / 2)) :
    chartRatio R s < 1 := by
  have h := norm_lt_of_mem_ball hs
  unfold chartRatio
  rw [div_lt_one (by positivity)]
  exact h

theorem norm_le_chartRatio_mul {R : ℝ} (hR : 0 < R) (s : ℂ) {ρ : ℂ} (h : R / 2 ≤ ‖ρ‖) :
    ‖s - 1 / 2‖ ≤ chartRatio R s * ‖ρ‖ := by
  have hα := chartRatio_nonneg hR s
  have hR0 : R ≠ 0 := hR.ne'
  have e : ‖s - 1 / 2‖ = chartRatio R s * (R / 2) := by
    unfold chartRatio
    field_simp
  calc ‖s - 1 / 2‖ = chartRatio R s * (R / 2) := e
    _ ≤ chartRatio R s * ‖ρ‖ := mul_le_mul_of_nonneg_left h hα

theorem chartRatio_le_quarter {R : ℝ} (hR : 0 < R) {s : ℂ}
    (hs : s ∈ closedBall (1 / 2 : ℂ) (R / 8)) : chartRatio R s ≤ 1 / 4 := by
  rw [mem_closedBall, Complex.dist_eq] at hs
  unfold chartRatio
  rw [div_le_iff₀ (by positivity)]
  linarith

theorem closedBall_eighth_subset {R : ℝ} (hR : 0 < R) :
    closedBall (1 / 2 : ℂ) (R / 8) ⊆ ball (1 / 2 : ℂ) (R / 2) :=
  closedBall_subset_ball (by linarith)

/-- On the closed `R/8` chart (`alpha, beta <= 1/4`) the paired coefficient is at most the exact
rational `544/225`; the value at `alpha = beta = 1/4` is `544/225`. -/
theorem pairedCoeff_le_of_quarter {α β : ℝ} (hα0 : 0 ≤ α) (hα : α ≤ 1 / 4) (hβ0 : 0 ≤ β)
    (hβ : β ≤ 1 / 4) : pairedCoeff α β ≤ 544 / 225 := by
  unfold pairedCoeff
  have h1 : 15 / 16 ≤ 1 - α ^ 2 := by nlinarith
  have h2 : 15 / 16 ≤ 1 - β ^ 2 := by nlinarith
  have h3 : 225 / 256 ≤ (1 - α ^ 2) * (1 - β ^ 2) := by
    have := mul_le_mul h1 h2 (by norm_num) (by linarith)
    norm_num at this
    linarith
  have h4 : α * β ≤ 1 / 16 := by
    have := mul_le_mul hα hβ hβ0 (by norm_num)
    norm_num at this
    linarith
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-- On the closed `R/8` chart the separate coefficient of one argument is at most `32/15`. -/
theorem separateCoeff_le_of_quarter {α : ℝ} (hα0 : 0 ≤ α) (hα : α ≤ 1 / 4) :
    separateCoeff α ≤ 32 / 15 := by
  unfold separateCoeff
  have h : 15 / 16 ≤ 1 - α ^ 2 := by nlinarith
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-- A complex number whose norm and whose translate by one have norm at most `1/2` is `-1/2`:
the equality case of the triangle inequality for the unit segment. -/
theorem eq_neg_half_of_norm_le {X : ℂ} (h1 : ‖X‖ ≤ 1 / 2) (h2 : ‖X + 1‖ ≤ 1 / 2) :
    X = ((-1 / 2 : ℝ) : ℂ) := by
  have e1 : ‖X‖ ^ 2 ≤ 1 / 4 := by nlinarith [norm_nonneg X]
  have e2 : ‖X + 1‖ ^ 2 ≤ 1 / 4 := by nlinarith [norm_nonneg (X + 1)]
  rw [Complex.sq_norm, Complex.normSq_apply] at e1 e2
  have hr : (X + 1).re = X.re + 1 := by simp
  have hi : (X + 1).im = X.im := by simp
  rw [hr, hi] at e2
  have hre : X.re = -1 / 2 := by
    nlinarith [sq_nonneg (X.re + 1 / 2), sq_nonneg X.im]
  have him : X.im = 0 := by
    nlinarith [sq_nonneg (X.re + 1 / 2), sq_nonneg X.im]
  apply Complex.ext
  · simpa using hre
  · simpa using him

/-- The common closed `R/8` chart at both `2w - 1` and `2w` is nonempty only for `R >= 4`:
the two arguments are `1` apart. -/
theorem four_le_of_charts {R : ℝ} {w : ℂ}
    (hm : 2 * w - 1 ∈ closedBall (1 / 2 : ℂ) (R / 8))
    (hp : 2 * w ∈ closedBall (1 / 2 : ℂ) (R / 8)) : 4 ≤ R := by
  rw [mem_closedBall, Complex.dist_eq] at hm hp
  have h : ‖(2 * w - 1 / 2) - (2 * w - 1 - 1 / 2)‖ ≤ ‖2 * w - 1 / 2‖ + ‖2 * w - 1 - 1 / 2‖ :=
    norm_sub_le _ _
  have e : (2 * w - 1 / 2) - (2 * w - 1 - 1 / 2) = (1 : ℂ) := by ring
  rw [e, norm_one] at h
  linarith

/-- With `w != 1/2` the common closed `R/8` chart needs `R > 4`: at `R = 4` it leaves only
`2w - 1 = 0`, `2w = 1`, that is `w = 1/2`, which the literal ratio excludes. -/
theorem four_lt_of_charts {R : ℝ} {w : ℂ} (hwHalf : w ≠ 1 / 2)
    (hm : 2 * w - 1 ∈ closedBall (1 / 2 : ℂ) (R / 8))
    (hp : 2 * w ∈ closedBall (1 / 2 : ℂ) (R / 8)) : 4 < R := by
  have h4 := four_le_of_charts hm hp
  by_contra hlt
  have hR4 : R ≤ 4 := not_lt.mp hlt
  rw [mem_closedBall, Complex.dist_eq] at hm hp
  have h1 : ‖2 * w - 1 - 1 / 2‖ ≤ 1 / 2 := by linarith
  have h2 : ‖2 * w - 1 - 1 / 2 + 1‖ ≤ 1 / 2 := by
    have e : 2 * w - 1 - 1 / 2 + 1 = 2 * w - 1 / 2 := by ring
    rw [e]
    linarith
  have hX := eq_neg_half_of_norm_le h1 h2
  have hc : (((-1 / 2 : ℝ)) : ℂ) = -1 / 2 := by push_cast; ring
  rw [hc] at hX
  exact hwHalf (by linear_combination (1 / 2 : ℂ) * hX)

/-! ## 2. The tail of the Foster product, read at two arguments -/

section Tail

variable {f : ℂ → ℂ} {A B σ : ℝ} [hf : FosterClass f A B σ]
include hf

/-- The tail multiset: the zeros outside the closed half disc of radius `R/2`, repeated by
multiplicity (the index of `FosterClassSplit.tail`). -/
abbrev TailIdx {R : ℝ} (hR : 0 < R) : Type := ↥((↑(T (f := f) hR) : Set (Idx f))ᶜ)

omit hf in
theorem invSq_eq_ctr (i : Idx f) : invSq ((i.1 : Zero f) : ℂ) = (‖ctr i‖ ^ 2)⁻¹ := rfl

theorem tail_norm_ctr {R : ℝ} (hR : 0 < R) (i : TailIdx (f := f) hR) :
    R / 2 < ‖ctr (i : Idx f)‖ :=
  norm_ctr_of_notMem (f := f) hR i.2

theorem summable_invSq_tail {R : ℝ} (hR : 0 < R) :
    Summable (fun i : TailIdx (f := f) hR => invSq (((i : Idx f).1 : Zero f) : ℂ)) :=
  ((summable_majorant_disc (f := f) 1).subtype _).congr
    (fun i => by simp only [Function.comp]; ring)

theorem tsum_invSq_tail {R : ℝ} (hR : 0 < R) :
    ∑' i : TailIdx (f := f) hR, invSq (((i : Idx f).1 : Zero f) : ℂ) = tailInvSq f R := by
  unfold tailInvSq
  exact tsum_congr_set_coe (fun i : Idx f => invSq ((i.1 : Zero f) : ℂ)) (compl_T_eq (f := f) hR)

/-- A tail sum whose terms are bounded by `C / |rho - 1/2|^2` is at most `C * tailInvSq`. -/
theorem norm_tsum_tail_le {R : ℝ} (hR : 0 < R) {g : TailIdx (f := f) hR → ℂ} {C : ℝ}
    (h : ∀ i, ‖g i‖ ≤ C * invSq (((i : Idx f).1 : Zero f) : ℂ)) :
    ‖∑' i, g i‖ ≤ C * tailInvSq f R := by
  have hsum : HasSum (fun i : TailIdx (f := f) hR => C * invSq (((i : Idx f).1 : Zero f) : ℂ))
      (C * tailInvSq f R) := by
    rw [← tsum_invSq_tail (f := f) hR]
    exact (summable_invSq_tail (f := f) hR).hasSum.mul_left C
  exact tsum_of_norm_bounded hsum h

/-! ### The reflection of the tail multiset: the dyad's half-turn -/

/-- The reflection `rho |-> 1 - rho` on the zeros (the multiplicity is preserved). -/
def reflectZero : Zero f ≃ Zero f where
  toFun u := ⟨1 - (u : ℂ), by rw [mult_one_sub (f := f)]; exact u.2⟩
  invFun u := ⟨1 - (u : ℂ), by rw [mult_one_sub (f := f)]; exact u.2⟩
  left_inv u := Subtype.ext (sub_sub_cancel 1 (u : ℂ))
  right_inv u := Subtype.ext (sub_sub_cancel 1 (u : ℂ))

/-- The reflection on the zeros repeated by multiplicity: each copy of `rho` goes to a copy of
`1 - rho`, the fibres having the same size. -/
def reflectIdx : Idx f ≃ Idx f :=
  Equiv.sigmaCongr (reflectZero (f := f))
    (fun u => finCongr (congrArg Int.toNat (mult_one_sub (f := f) (u : ℂ)).symm))

theorem coe_reflectIdx (i : Idx f) :
    (((reflectIdx (f := f) i).1 : Zero f) : ℂ) = 1 - ((i.1 : Zero f) : ℂ) := by
  rfl

/-- The reflection negates the centred zero: `ctr (U i) = - ctr i`. -/
theorem ctr_reflectIdx (i : Idx f) : ctr (reflectIdx (f := f) i) = -ctr i := by
  unfold ctr
  rw [coe_reflectIdx]
  ring

/-- The tail is closed under the reflection. -/
def reflectTail {R : ℝ} (hR : 0 < R) : TailIdx (f := f) hR ≃ TailIdx (f := f) hR :=
  Equiv.subtypeEquiv (reflectIdx (f := f)) (fun i => by
    simp only [mem_compl_iff, Finset.mem_coe, mem_T_iff_norm, ctr_reflectIdx, norm_neg])

/-- Summing a function of the centred zero over the tail multiset is the same as summing it at
the reflected centred zero. -/
theorem tsum_reflect_tail {R : ℝ} (hR : 0 < R) (g : ℂ → ℂ) :
    ∑' i : TailIdx (f := f) hR, g (-ctr (i : Idx f)) =
      ∑' i : TailIdx (f := f) hR, g (ctr (i : Idx f)) := by
  have h := (reflectTail (f := f) hR).tsum_eq
    (fun i : TailIdx (f := f) hR => g (ctr (i : Idx f)))
  refine (tsum_congr fun i => ?_).trans h
  show g (-ctr (i : Idx f)) = g (ctr (reflectIdx (f := f) (i : Idx f)))
  rw [ctr_reflectIdx]

/-! ### The tail residual as a sum of pair terms -/

/-- **The tail residual is the sum of the index tank differences.** -/
theorem tailPair_eq_tsum {R : ℝ} (hR : 0 < R) {s t : ℂ}
    (hs : s ∈ ball (1 / 2 : ℂ) (R / 2)) (ht : t ∈ ball (1 / 2 : ℂ) (R / 2)) :
    logDeriv (tail (f := f) hR) s - logDeriv (tail (f := f) hR) t =
      ∑' i : TailIdx (f := f) hR, (tank (i : Idx f) s - tank (i : Idx f) t) := by
  rw [logDeriv_tail (f := f) hR hs, logDeriv_tail (f := f) hR ht]
  exact ((((summable_tank (f := f) s).subtype _).hasSum).sub
    (((summable_tank (f := f) t).subtype _).hasSum)).tsum_eq.symm

/-- **The pair term of one index** (the pair identity at the index): the tank difference is
`(t - s)` times the two members of the pair `{rho, 1 - rho}`. -/
theorem tank_sub_eq_pair {R : ℝ} (hR : 0 < R) {s t : ℂ}
    (hs : s ∈ ball (1 / 2 : ℂ) (R / 2)) (ht : t ∈ ball (1 / 2 : ℂ) (R / 2))
    (i : TailIdx (f := f) hR) :
    tank (i : Idx f) s - tank (i : Idx f) t =
      (t - s) * (pairKernel (s - 1 / 2) (t - 1 / 2) (ctr (i : Idx f)) +
        pairKernel (s - 1 / 2) (t - 1 / 2) (-ctr (i : Idx f))) := by
  have hc := tail_norm_ctr (f := f) hR i
  have hxr : ‖s - 1 / 2‖ < ‖ctr (i : Idx f)‖ := lt_trans (norm_lt_of_mem_ball hs) hc
  have hyr : ‖t - 1 / 2‖ < ‖ctr (i : Idx f)‖ := lt_trans (norm_lt_of_mem_ball ht) hc
  have h := tankC_sub_eq_pair (sub_ne_zero_of_norm_lt hxr) (add_ne_zero_of_norm_lt hxr)
    (sub_ne_zero_of_norm_lt hyr) (add_ne_zero_of_norm_lt hyr)
  have e1 : (t - 1 / 2) - (s - 1 / 2) = t - s := by ring
  rw [e1] at h
  unfold pairKernel
  simp only [sub_neg_eq_add]
  exact h

theorem norm_pairKernel_tail_le {R : ℝ} (hR : 0 < R) {s t : ℂ}
    (hs : s ∈ ball (1 / 2 : ℂ) (R / 2)) (ht : t ∈ ball (1 / 2 : ℂ) (R / 2))
    (i : TailIdx (f := f) hR) {c : ℂ} (hc : ‖c‖ = ‖ctr (i : Idx f)‖) :
    ‖pairKernel (s - 1 / 2) (t - 1 / 2) c‖ ≤
      (1 / ((1 - chartRatio R s) * (1 - chartRatio R t))) *
        invSq (((i : Idx f).1 : Zero f) : ℂ) := by
  have hcr := tail_norm_ctr (f := f) hR i
  have hcn : c ≠ 0 := by
    intro h0
    have : ‖c‖ = 0 := by rw [h0, norm_zero]
    have hpos := norm_ctr_pos (f := f) (i : Idx f)
    linarith
  have hR2 : R / 2 ≤ ‖c‖ := by rw [hc]; exact hcr.le
  have h := norm_pairKernel_le (x := s - 1 / 2) (y := t - 1 / 2) (r := c) hcn
    (chartRatio_lt_one hR hs) (chartRatio_lt_one hR ht)
    (norm_le_chartRatio_mul hR s hR2) (norm_le_chartRatio_mul hR t hR2)
  rw [invSq_eq_ctr, ← hc]
  exact h

/-- Any choice of one member of each pair has an absolutely summable kernel. -/
theorem summable_pairKernel_tail {R : ℝ} (hR : 0 < R) {s t : ℂ}
    (hs : s ∈ ball (1 / 2 : ℂ) (R / 2)) (ht : t ∈ ball (1 / 2 : ℂ) (R / 2))
    {c : TailIdx (f := f) hR → ℂ} (hc : ∀ i, ‖c i‖ = ‖ctr (i : Idx f)‖) :
    Summable (fun i => pairKernel (s - 1 / 2) (t - 1 / 2) (c i)) :=
  Summable.of_norm_bounded
    ((summable_invSq_tail (f := f) hR).mul_left
      (1 / ((1 - chartRatio R s) * (1 - chartRatio R t))))
    (fun i => norm_pairKernel_tail_le hR hs ht i (hc i))

/-- **The tail residual over the full reflection-invariant multiset.**  With the zeros of the
tail repeated by multiplicity, the residual is twice `(t - s)` times the sum of
`1/((s - rho)(t - rho))`.  The two members of each pair have already been composed: the sum is
absolutely summable (its terms are `O(1/|rho - 1/2|^2)`), and it is not split into the sums of
`1/(s - rho)` and `1/(t - rho)`. -/
theorem tailPair_eq_two_mul_tsum {R : ℝ} (hR : 0 < R) {s t : ℂ}
    (hs : s ∈ ball (1 / 2 : ℂ) (R / 2)) (ht : t ∈ ball (1 / 2 : ℂ) (R / 2)) :
    logDeriv (tail (f := f) hR) s - logDeriv (tail (f := f) hR) t =
      2 * (t - s) * ∑' i : TailIdx (f := f) hR,
        1 / ((s - ((i : Idx f).1 : ℂ)) * (t - ((i : Idx f).1 : ℂ))) := by
  have hsum1 : Summable (fun i : TailIdx (f := f) hR =>
      pairKernel (s - 1 / 2) (t - 1 / 2) (ctr (i : Idx f))) :=
    summable_pairKernel_tail (f := f) hR hs ht (c := fun i => ctr (i : Idx f)) (fun i => rfl)
  have hsum2 : Summable (fun i : TailIdx (f := f) hR =>
      pairKernel (s - 1 / 2) (t - 1 / 2) (-ctr (i : Idx f))) :=
    summable_pairKernel_tail (f := f) hR hs ht (c := fun i => -ctr (i : Idx f))
      (fun i => norm_neg _)
  have hrefl := tsum_reflect_tail (f := f) hR (fun r => pairKernel (s - 1 / 2) (t - 1 / 2) r)
  have hconv : ∀ i : TailIdx (f := f) hR,
      pairKernel (s - 1 / 2) (t - 1 / 2) (ctr (i : Idx f)) =
        1 / ((s - ((i : Idx f).1 : ℂ)) * (t - ((i : Idx f).1 : ℂ))) := by
    intro i
    unfold pairKernel ctr
    ring
  have e1 : ∑' i : TailIdx (f := f) hR, (tank (i : Idx f) s - tank (i : Idx f) t) =
      (t - s) * (∑' i : TailIdx (f := f) hR,
          pairKernel (s - 1 / 2) (t - 1 / 2) (ctr (i : Idx f)) +
        ∑' i : TailIdx (f := f) hR,
          pairKernel (s - 1 / 2) (t - 1 / 2) (-ctr (i : Idx f))) := by
    rw [tsum_congr (tank_sub_eq_pair (f := f) hR hs ht), tsum_mul_left, hsum1.tsum_add hsum2]
  rw [tailPair_eq_tsum (f := f) hR hs ht, e1, hrefl, tsum_congr hconv]
  ring

/-! ### The same sum, with the multiplicities read separately -/

omit hf in
/-- A sum over the zeros repeated by multiplicity is the multiplicity-weighted sum over the zeros. -/
theorem tsum_idx_eq_tsum_zero {H : Zero f → ℂ} (hH : Summable (fun i : Idx f => H i.1)) :
    ∑' i : Idx f, H i.1 = ∑' u : Zero f, ((mult f (u : ℂ)).toNat : ℂ) * H u := by
  rw [hH.tsum_sigma]
  apply tsum_congr
  intro u
  rw [tsum_fintype]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The tail multiset summed through its zeros: each zero outside the closed half disc enters
with its multiplicity. -/
theorem tsum_tail_idx_eq_tsum_tail_zero {R : ℝ} (hR : 0 < R) (G : Zero f → ℂ)
    (hH : Summable (fun i : Idx f =>
      (if R / 2 < ‖((i.1 : Zero f) : ℂ) - 1 / 2‖ then G i.1 else 0))) :
    ∑' i : TailIdx (f := f) hR, G ((i : Idx f).1) =
      ∑' u : ↥{u : Zero f | R / 2 < ‖(u : ℂ) - 1 / 2‖},
        ((mult f ((u : Zero f) : ℂ)).toNat : ℂ) * G (u : Zero f) := by
  have step1 : ∑' i : TailIdx (f := f) hR, G ((i : Idx f).1) =
      ∑' i : Idx f, (if R / 2 < ‖((i.1 : Zero f) : ℂ) - 1 / 2‖ then G i.1 else 0) := by
    rw [tsum_subtype ((↑(T (f := f) hR) : Set (Idx f))ᶜ) (fun i : Idx f => G i.1)]
    refine tsum_congr fun i => ?_
    by_cases h : R / 2 < ‖((i.1 : Zero f) : ℂ) - 1 / 2‖
    · have hi : i ∈ ((↑(T (f := f) hR) : Set (Idx f))ᶜ) := by
        rw [compl_T_eq (f := f) hR]
        exact h
      rw [Set.indicator_of_mem hi, if_pos h]
    · have hi : i ∉ ((↑(T (f := f) hR) : Set (Idx f))ᶜ) := by
        rw [compl_T_eq (f := f) hR]
        exact h
      rw [Set.indicator_of_notMem hi, if_neg h]
  rw [step1, tsum_idx_eq_tsum_zero (H := fun u : Zero f =>
    (if R / 2 < ‖(u : ℂ) - 1 / 2‖ then G u else 0)) hH]
  refine Eq.trans (tsum_congr fun u => ?_)
    (tsum_subtype {u : Zero f | R / 2 < ‖(u : ℂ) - 1 / 2‖}
      (fun u : Zero f => ((mult f (u : ℂ)).toNat : ℂ) * G u)).symm
  by_cases h : R / 2 < ‖(u : ℂ) - 1 / 2‖
  · rw [if_pos h, Set.indicator_of_mem (show u ∈ {u : Zero f | R / 2 < ‖(u : ℂ) - 1 / 2‖} from h)]
  · rw [if_neg h, mul_zero,
      Set.indicator_of_notMem (show u ∉ {u : Zero f | R / 2 < ‖(u : ℂ) - 1 / 2‖} from h)]

/-- The zero-indexed kernel of the tail is absolutely summable over the repeated index. -/
theorem summable_tail_zero_kernel {R : ℝ} (hR : 0 < R) {s t : ℂ}
    (hs : s ∈ ball (1 / 2 : ℂ) (R / 2)) (ht : t ∈ ball (1 / 2 : ℂ) (R / 2)) :
    Summable (fun i : Idx f =>
      (if R / 2 < ‖((i.1 : Zero f) : ℂ) - 1 / 2‖ then
        1 / ((s - ((i.1 : Zero f) : ℂ)) * (t - ((i.1 : Zero f) : ℂ))) else 0)) := by
  have hC0 : 0 ≤ 1 / ((1 - chartRatio R s) * (1 - chartRatio R t)) :=
    one_div_nonneg.mpr (mul_pos (sub_pos.mpr (chartRatio_lt_one hR hs))
      (sub_pos.mpr (chartRatio_lt_one hR ht))).le
  refine Summable.of_norm_bounded
    ((summable_majorant_disc (f := f) 1).mul_left
      (1 / ((1 - chartRatio R s) * (1 - chartRatio R t)))) (fun i => ?_)
  by_cases h : R / 2 < ‖((i.1 : Zero f) : ℂ) - 1 / 2‖
  · rw [if_pos h]
    have hr : ((i.1 : Zero f) : ℂ) - 1 / 2 ≠ 0 := sub_ne_zero.mpr (Zero.ne_half i.1)
    have hk := norm_pairKernel_le (x := s - 1 / 2) (y := t - 1 / 2)
      (r := ((i.1 : Zero f) : ℂ) - 1 / 2) hr
      (chartRatio_lt_one hR hs) (chartRatio_lt_one hR ht)
      (norm_le_chartRatio_mul hR s h.le) (norm_le_chartRatio_mul hR t h.le)
    have e : 1 / ((s - ((i.1 : Zero f) : ℂ)) * (t - ((i.1 : Zero f) : ℂ))) =
        pairKernel (s - 1 / 2) (t - 1 / 2) (((i.1 : Zero f) : ℂ) - 1 / 2) := by
      unfold pairKernel
      ring
    rw [e]
    refine hk.trans (le_of_eq ?_)
    rw [one_pow, one_mul]
    rfl
  · rw [if_neg h, norm_zero]
    exact mul_nonneg hC0 (mul_nonneg (by positivity) (invSq_nonneg _))

/-- **The tail residual with the multiplicities explicit.**  Over the zeros outside the closed
half disc of radius `R/2`, each counted `m_rho` times, the residual is
`2 (t - s) sum_rho m_rho / ((s - rho)(t - rho))`, an absolutely summable sum. -/
theorem tailPair_eq_two_mul_tsum_zeros {R : ℝ} (hR : 0 < R) {s t : ℂ}
    (hs : s ∈ ball (1 / 2 : ℂ) (R / 2)) (ht : t ∈ ball (1 / 2 : ℂ) (R / 2)) :
    logDeriv (tail (f := f) hR) s - logDeriv (tail (f := f) hR) t =
      2 * (t - s) * ∑' u : ↥{u : Zero f | R / 2 < ‖(u : ℂ) - 1 / 2‖},
        ((mult f ((u : Zero f) : ℂ)).toNat : ℂ) /
          ((s - ((u : Zero f) : ℂ)) * (t - ((u : Zero f) : ℂ))) := by
  rw [tailPair_eq_two_mul_tsum (f := f) hR hs ht]
  congr 1
  have h := tsum_tail_idx_eq_tsum_tail_zero (f := f) hR
    (fun u : Zero f => 1 / ((s - (u : ℂ)) * (t - (u : ℂ))))
    (summable_tail_zero_kernel (f := f) hR hs ht)
  rw [h]
  refine tsum_congr fun u => ?_
  ring

/-! ### The bounds -/

theorem norm_tank_sub_le_paired {R : ℝ} (hR : 0 < R) {s t : ℂ}
    (hs : s ∈ ball (1 / 2 : ℂ) (R / 2)) (ht : t ∈ ball (1 / 2 : ℂ) (R / 2))
    (i : TailIdx (f := f) hR) :
    ‖tank (i : Idx f) s - tank (i : Idx f) t‖ ≤
      ‖t - s‖ * pairedCoeff (chartRatio R s) (chartRatio R t) *
        invSq (((i : Idx f).1 : Zero f) : ℂ) := by
  have hc := tail_norm_ctr (f := f) hR i
  have h := norm_tankC_sub_le (x := s - 1 / 2) (y := t - 1 / 2) (r := ctr (i : Idx f))
    (ctr_ne_zero (f := f) _)
    (chartRatio_nonneg hR s) (chartRatio_lt_one hR hs)
    (chartRatio_nonneg hR t) (chartRatio_lt_one hR ht)
    (norm_le_chartRatio_mul hR s hc.le) (norm_le_chartRatio_mul hR t hc.le)
  have e : (t - 1 / 2) - (s - 1 / 2) = t - s := by ring
  rw [e] at h
  rw [invSq_eq_ctr]
  exact h

theorem norm_tank_sub_le_separate {R : ℝ} (hR : 0 < R) {s t : ℂ}
    (hs : s ∈ ball (1 / 2 : ℂ) (R / 2)) (ht : t ∈ ball (1 / 2 : ℂ) (R / 2))
    (i : TailIdx (f := f) hR) :
    ‖tank (i : Idx f) s - tank (i : Idx f) t‖ ≤
      (separateCoeff (chartRatio R s) * ‖s - 1 / 2‖ +
          separateCoeff (chartRatio R t) * ‖t - 1 / 2‖) *
        invSq (((i : Idx f).1 : Zero f) : ℂ) := by
  have hc := tail_norm_ctr (f := f) hR i
  have h1 := norm_tankC_le (x := s - 1 / 2) (r := ctr (i : Idx f)) (ctr_ne_zero (f := f) _)
    (chartRatio_nonneg hR s) (chartRatio_lt_one hR hs) (norm_le_chartRatio_mul hR s hc.le)
  have h2 := norm_tankC_le (x := t - 1 / 2) (r := ctr (i : Idx f)) (ctr_ne_zero (f := f) _)
    (chartRatio_nonneg hR t) (chartRatio_lt_one hR ht) (norm_le_chartRatio_mul hR t hc.le)
  rw [invSq_eq_ctr]
  calc ‖tank (i : Idx f) s - tank (i : Idx f) t‖
      ≤ ‖tank (i : Idx f) s‖ + ‖tank (i : Idx f) t‖ := norm_sub_le _ _
    _ ≤ separateCoeff (chartRatio R s) * ‖s - 1 / 2‖ * (‖ctr (i : Idx f)‖ ^ 2)⁻¹ +
          separateCoeff (chartRatio R t) * ‖t - 1 / 2‖ * (‖ctr (i : Idx f)‖ ^ 2)⁻¹ :=
        add_le_add h1 h2
    _ = _ := by ring

/-- **The paired tail bound.**  For two arguments in the half-disc chart (`alpha, beta < 1`),
the difference of the tail-product log derivatives is at most
`|t - s| * 2(1 + alpha beta)/((1 - alpha^2)(1 - beta^2)) * tailInvSq`. -/
theorem norm_tailPair_le_paired {R : ℝ} (hR : 0 < R) {s t : ℂ}
    (hs : s ∈ ball (1 / 2 : ℂ) (R / 2)) (ht : t ∈ ball (1 / 2 : ℂ) (R / 2)) :
    ‖logDeriv (tail (f := f) hR) s - logDeriv (tail (f := f) hR) t‖ ≤
      ‖t - s‖ * pairedCoeff (chartRatio R s) (chartRatio R t) * tailInvSq f R := by
  rw [tailPair_eq_tsum (f := f) hR hs ht]
  exact norm_tsum_tail_le (f := f) hR (fun i => norm_tank_sub_le_paired (f := f) hR hs ht i)

/-- **The sharper separate tail bound**, kept beside the paired one: each argument alone,
`2|s - 1/2|/(1 - alpha^2) + 2|t - 1/2|/(1 - beta^2)`, times `tailInvSq`. -/
theorem norm_tailPair_le_separate {R : ℝ} (hR : 0 < R) {s t : ℂ}
    (hs : s ∈ ball (1 / 2 : ℂ) (R / 2)) (ht : t ∈ ball (1 / 2 : ℂ) (R / 2)) :
    ‖logDeriv (tail (f := f) hR) s - logDeriv (tail (f := f) hR) t‖ ≤
      (separateCoeff (chartRatio R s) * ‖s - 1 / 2‖ +
          separateCoeff (chartRatio R t) * ‖t - 1 / 2‖) * tailInvSq f R := by
  rw [tailPair_eq_tsum (f := f) hR hs ht]
  exact norm_tsum_tail_le (f := f) hR (fun i => norm_tank_sub_le_separate (f := f) hR hs ht i)

/-- **The minimum of the two tail bounds**, where both hypotheses hold (both arguments in the
half-disc chart). -/
theorem norm_tailPair_le_min {R : ℝ} (hR : 0 < R) {s t : ℂ}
    (hs : s ∈ ball (1 / 2 : ℂ) (R / 2)) (ht : t ∈ ball (1 / 2 : ℂ) (R / 2)) :
    ‖logDeriv (tail (f := f) hR) s - logDeriv (tail (f := f) hR) t‖ ≤
      min (‖t - s‖ * pairedCoeff (chartRatio R s) (chartRatio R t))
        (separateCoeff (chartRatio R s) * ‖s - 1 / 2‖ +
          separateCoeff (chartRatio R t) * ‖t - 1 / 2‖) * tailInvSq f R := by
  have h1 := norm_tailPair_le_paired (f := f) hR hs ht
  have h2 := norm_tailPair_le_separate (f := f) hR hs ht
  rcases le_total (‖t - s‖ * pairedCoeff (chartRatio R s) (chartRatio R t))
      (separateCoeff (chartRatio R s) * ‖s - 1 / 2‖ +
        separateCoeff (chartRatio R t) * ‖t - 1 / 2‖) with h | h
  · rw [min_eq_left h]
    exact h1
  · rw [min_eq_right h]
    exact h2

/-- The paired tail bound at two arguments one apart (`t - s = 1`), the form the pulled-back
arguments `2w - 1` and `2w` take. -/
theorem norm_tailPair_le_paired_of_sub_eq_one {R : ℝ} (hR : 0 < R) {s t : ℂ}
    (hs : s ∈ ball (1 / 2 : ℂ) (R / 2)) (ht : t ∈ ball (1 / 2 : ℂ) (R / 2))
    (hts : t - s = 1) :
    ‖logDeriv (tail (f := f) hR) s - logDeriv (tail (f := f) hR) t‖ ≤
      pairedCoeff (chartRatio R s) (chartRatio R t) * tailInvSq f R := by
  have h := norm_tailPair_le_paired (f := f) hR hs ht
  rw [hts, norm_one, one_mul] at h
  exact h

/-- On the common closed `R/8` chart the paired tail bound has the exact rational coefficient
`544/225` (times `|t - s|`). -/
theorem norm_tailPair_le_eighth {R : ℝ} (hR : 0 < R) {s t : ℂ}
    (hs : s ∈ closedBall (1 / 2 : ℂ) (R / 8)) (ht : t ∈ closedBall (1 / 2 : ℂ) (R / 8)) :
    ‖logDeriv (tail (f := f) hR) s - logDeriv (tail (f := f) hR) t‖ ≤
      ‖t - s‖ * (544 / 225) * tailInvSq f R := by
  have h := norm_tailPair_le_paired (f := f) hR (closedBall_eighth_subset hR hs)
    (closedBall_eighth_subset hR ht)
  have hc : pairedCoeff (chartRatio R s) (chartRatio R t) ≤ 544 / 225 :=
    pairedCoeff_le_of_quarter (chartRatio_nonneg hR s) (chartRatio_le_quarter hR hs)
      (chartRatio_nonneg hR t) (chartRatio_le_quarter hR ht)
  refine h.trans ?_
  have hS : 0 ≤ tailInvSq f R := tailInvSq_nonneg R
  have hn : 0 ≤ ‖t - s‖ := norm_nonneg _
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc hn) hS

/-- On the common closed `R/8` chart the separate tail bound has coefficient `32/15` on each
`|s - 1/2|`, `|t - 1/2|`. -/
theorem norm_tailPair_le_eighth_separate {R : ℝ} (hR : 0 < R) {s t : ℂ}
    (hs : s ∈ closedBall (1 / 2 : ℂ) (R / 8)) (ht : t ∈ closedBall (1 / 2 : ℂ) (R / 8)) :
    ‖logDeriv (tail (f := f) hR) s - logDeriv (tail (f := f) hR) t‖ ≤
      (32 / 15) * (‖s - 1 / 2‖ + ‖t - 1 / 2‖) * tailInvSq f R := by
  have h := norm_tailPair_le_separate (f := f) hR (closedBall_eighth_subset hR hs)
    (closedBall_eighth_subset hR ht)
  have hcs : separateCoeff (chartRatio R s) ≤ 32 / 15 :=
    separateCoeff_le_of_quarter (chartRatio_nonneg hR s) (chartRatio_le_quarter hR hs)
  have hct : separateCoeff (chartRatio R t) ≤ 32 / 15 :=
    separateCoeff_le_of_quarter (chartRatio_nonneg hR t) (chartRatio_le_quarter hR ht)
  refine h.trans ?_
  have hS : 0 ≤ tailInvSq f R := tailInvSq_nonneg R
  have hsn : 0 ≤ ‖s - 1 / 2‖ := norm_nonneg _
  have htn : 0 ≤ ‖t - 1 / 2‖ := norm_nonneg _
  refine mul_le_mul_of_nonneg_right ?_ hS
  nlinarith [mul_le_mul_of_nonneg_right hcs hsn, mul_le_mul_of_nonneg_right hct htn]

end Tail

/-! ## 3. The modular scattering residual -/

section Xi

/-- **The paired bound for the xi remainder pair.**  `2 e_R(s) - 2 e_R(t)` is the difference of
the tail-product log derivatives; it keeps its own endpoint hypotheses, the ball memberships and
`xi(s), xi(t) != 0`. -/
theorem norm_xiRemainderPair_le_paired {R : ℝ} (hR : 0 < R) {s t : ℂ}
    (hs : s ∈ ball (1 / 2 : ℂ) (R / 2)) (ht : t ∈ ball (1 / 2 : ℂ) (R / 2))
    (hξs : riemannXi s ≠ 0) (hξt : riemannXi t ≠ 0) :
    ‖2 * xiCurrentRemainder hR s - 2 * xiCurrentRemainder hR t‖ ≤
      ‖t - s‖ * pairedCoeff (chartRatio R s) (chartRatio R t) * tailInvSq riemannXi R := by
  have h := norm_tailPair_le_paired (f := riemannXi) hR hs ht
  have e : 2 * xiCurrentRemainder hR s - 2 * xiCurrentRemainder hR t =
      logDeriv (tail (f := riemannXi) hR) s - logDeriv (tail (f := riemannXi) hR) t := by
    rw [xiCurrentRemainder_eq_tail hR hs hξs, xiCurrentRemainder_eq_tail hR ht hξt]
    ring
  rw [e]
  exact h

theorem norm_xiRemainderPair_le_separate {R : ℝ} (hR : 0 < R) {s t : ℂ}
    (hs : s ∈ ball (1 / 2 : ℂ) (R / 2)) (ht : t ∈ ball (1 / 2 : ℂ) (R / 2))
    (hξs : riemannXi s ≠ 0) (hξt : riemannXi t ≠ 0) :
    ‖2 * xiCurrentRemainder hR s - 2 * xiCurrentRemainder hR t‖ ≤
      (separateCoeff (chartRatio R s) * ‖s - 1 / 2‖ +
          separateCoeff (chartRatio R t) * ‖t - 1 / 2‖) * tailInvSq riemannXi R := by
  have h := norm_tailPair_le_separate (f := riemannXi) hR hs ht
  have e : 2 * xiCurrentRemainder hR s - 2 * xiCurrentRemainder hR t =
      logDeriv (tail (f := riemannXi) hR) s - logDeriv (tail (f := riemannXi) hR) t := by
    rw [xiCurrentRemainder_eq_tail hR hs hξs, xiCurrentRemainder_eq_tail hR ht hξt]
    ring
  rw [e]
  exact h

/-- The two pulled-back arguments are one apart. -/
theorem norm_pulled_sub (w : ℂ) : ‖(2 * w) - (2 * w - 1)‖ = 1 := by
  have e : (2 * w) - (2 * w - 1) = (1 : ℂ) := by ring
  rw [e, norm_one]

/-- **The paired bound for the modular scattering residual.**  On the common half-disc chart at
`2w - 1` and `2w`, the residual of the literal Lambda scalar against its finite current is
bounded by the paired coefficient times `tailInvSq`.  Endpoint hypotheses as in
`modularScattering_current_residual_eq_tail`: `w != 0, 1/2, 1`, `xi != 0` at both arguments, the
two ball memberships.  A bound on the magnitude only. -/
theorem norm_modularScattering_residual_le_paired {R : ℝ} (hR : 0 < R) {w : ℂ}
    (hw0 : w ≠ 0) (hwHalf : w ≠ 1 / 2) (hw1 : w ≠ 1)
    (hξm : riemannXi (2 * w - 1) ≠ 0) (hξp : riemannXi (2 * w) ≠ 0)
    (hm : 2 * w - 1 ∈ ball (1 / 2 : ℂ) (R / 2)) (hp : 2 * w ∈ ball (1 / 2 : ℂ) (R / 2)) :
    ‖logDeriv modularScattering w - finiteScatteringCurrent hR w‖ ≤
      pairedCoeff (chartRatio R (2 * w - 1)) (chartRatio R (2 * w)) * tailInvSq riemannXi R := by
  rw [modularScattering_current_residual hR hw0 hwHalf hw1 hξm hξp]
  have h := norm_xiRemainderPair_le_paired hR hm hp hξm hξp
  rw [norm_pulled_sub, one_mul] at h
  exact h

/-- **The sharper separate bound for the modular scattering residual.** -/
theorem norm_modularScattering_residual_le_separate {R : ℝ} (hR : 0 < R) {w : ℂ}
    (hw0 : w ≠ 0) (hwHalf : w ≠ 1 / 2) (hw1 : w ≠ 1)
    (hξm : riemannXi (2 * w - 1) ≠ 0) (hξp : riemannXi (2 * w) ≠ 0)
    (hm : 2 * w - 1 ∈ ball (1 / 2 : ℂ) (R / 2)) (hp : 2 * w ∈ ball (1 / 2 : ℂ) (R / 2)) :
    ‖logDeriv modularScattering w - finiteScatteringCurrent hR w‖ ≤
      (separateCoeff (chartRatio R (2 * w - 1)) * ‖(2 * w - 1) - 1 / 2‖ +
          separateCoeff (chartRatio R (2 * w)) * ‖2 * w - 1 / 2‖) * tailInvSq riemannXi R := by
  rw [modularScattering_current_residual hR hw0 hwHalf hw1 hξm hξp]
  exact norm_xiRemainderPair_le_separate hR hm hp hξm hξp

/-- **Both bounds, and their minimum**, where both hypotheses hold. -/
theorem norm_modularScattering_residual_le_min {R : ℝ} (hR : 0 < R) {w : ℂ}
    (hw0 : w ≠ 0) (hwHalf : w ≠ 1 / 2) (hw1 : w ≠ 1)
    (hξm : riemannXi (2 * w - 1) ≠ 0) (hξp : riemannXi (2 * w) ≠ 0)
    (hm : 2 * w - 1 ∈ ball (1 / 2 : ℂ) (R / 2)) (hp : 2 * w ∈ ball (1 / 2 : ℂ) (R / 2)) :
    ‖logDeriv modularScattering w - finiteScatteringCurrent hR w‖ ≤
      min (pairedCoeff (chartRatio R (2 * w - 1)) (chartRatio R (2 * w)))
        (separateCoeff (chartRatio R (2 * w - 1)) * ‖(2 * w - 1) - 1 / 2‖ +
          separateCoeff (chartRatio R (2 * w)) * ‖2 * w - 1 / 2‖) *
        tailInvSq riemannXi R := by
  have h1 := norm_modularScattering_residual_le_paired hR hw0 hwHalf hw1 hξm hξp hm hp
  have h2 := norm_modularScattering_residual_le_separate hR hw0 hwHalf hw1 hξm hξp hm hp
  rcases le_total (pairedCoeff (chartRatio R (2 * w - 1)) (chartRatio R (2 * w)))
      (separateCoeff (chartRatio R (2 * w - 1)) * ‖(2 * w - 1) - 1 / 2‖ +
        separateCoeff (chartRatio R (2 * w)) * ‖2 * w - 1 / 2‖) with h | h
  · rw [min_eq_left h]
    exact h1
  · rw [min_eq_right h]
    exact h2

/-- **The published separate enclosures, summed.**  From `xiCurrentRemainder_pullback_enclosures`:
the residual is at most `4 (|2w - 3/2| + |2w - 1/2|) tailInvSq` on the common closed `R/8`
chart.  This is the bound the paired and sharper separate bounds are compared with. -/
theorem norm_modularScattering_residual_le_published {R : ℝ} (hR : 0 < R) {w : ℂ}
    (hw0 : w ≠ 0) (hwHalf : w ≠ 1 / 2) (hw1 : w ≠ 1)
    (hξm : riemannXi (2 * w - 1) ≠ 0) (hξp : riemannXi (2 * w) ≠ 0)
    (hm : 2 * w - 1 ∈ closedBall (1 / 2 : ℂ) (R / 8))
    (hp : 2 * w ∈ closedBall (1 / 2 : ℂ) (R / 8)) :
    ‖logDeriv modularScattering w - finiteScatteringCurrent hR w‖ ≤
      4 * (‖(2 * w - 1) - 1 / 2‖ + ‖2 * w - 1 / 2‖) * tailInvSq riemannXi R := by
  rw [modularScattering_current_residual hR hw0 hwHalf hw1 hξm hξp]
  obtain ⟨h1, h2⟩ := xiCurrentRemainder_pullback_enclosures hR hm hp hξm hξp
  have e : ‖2 * xiCurrentRemainder hR (2 * w - 1) - 2 * xiCurrentRemainder hR (2 * w)‖ ≤
      2 * ‖xiCurrentRemainder hR (2 * w - 1)‖ + 2 * ‖xiCurrentRemainder hR (2 * w)‖ := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have h2' : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [h2']
  refine e.trans ?_
  nlinarith [h1, h2]

/-- **The paired bound on the common closed `R/8` chart.**  The coefficient is the exact
rational `544/225`. -/
theorem norm_modularScattering_residual_le_eighth_paired {R : ℝ} (hR : 0 < R) {w : ℂ}
    (hw0 : w ≠ 0) (hwHalf : w ≠ 1 / 2) (hw1 : w ≠ 1)
    (hξm : riemannXi (2 * w - 1) ≠ 0) (hξp : riemannXi (2 * w) ≠ 0)
    (hm : 2 * w - 1 ∈ closedBall (1 / 2 : ℂ) (R / 8))
    (hp : 2 * w ∈ closedBall (1 / 2 : ℂ) (R / 8)) :
    ‖logDeriv modularScattering w - finiteScatteringCurrent hR w‖ ≤
      (544 / 225) * tailInvSq riemannXi R := by
  have h := norm_modularScattering_residual_le_paired hR hw0 hwHalf hw1 hξm hξp
    (closedBall_eighth_subset hR hm) (closedBall_eighth_subset hR hp)
  have hc : pairedCoeff (chartRatio R (2 * w - 1)) (chartRatio R (2 * w)) ≤ 544 / 225 :=
    pairedCoeff_le_of_quarter (chartRatio_nonneg hR _) (chartRatio_le_quarter hR hm)
      (chartRatio_nonneg hR _) (chartRatio_le_quarter hR hp)
  exact h.trans (mul_le_mul_of_nonneg_right hc (tailInvSq_nonneg (f := riemannXi) R))

/-- **The sharper separate bound on the common closed `R/8` chart**: coefficient `32/15` on
`|2w - 3/2| + |2w - 1/2|`. -/
theorem norm_modularScattering_residual_le_eighth_separate {R : ℝ} (hR : 0 < R) {w : ℂ}
    (hw0 : w ≠ 0) (hwHalf : w ≠ 1 / 2) (hw1 : w ≠ 1)
    (hξm : riemannXi (2 * w - 1) ≠ 0) (hξp : riemannXi (2 * w) ≠ 0)
    (hm : 2 * w - 1 ∈ closedBall (1 / 2 : ℂ) (R / 8))
    (hp : 2 * w ∈ closedBall (1 / 2 : ℂ) (R / 8)) :
    ‖logDeriv modularScattering w - finiteScatteringCurrent hR w‖ ≤
      (32 / 15) * (‖(2 * w - 1) - 1 / 2‖ + ‖2 * w - 1 / 2‖) * tailInvSq riemannXi R := by
  rw [modularScattering_current_residual hR hw0 hwHalf hw1 hξm hξp]
  have h := norm_xiRemainderPair_le_separate hR (closedBall_eighth_subset hR hm)
    (closedBall_eighth_subset hR hp) hξm hξp
  have hcs : separateCoeff (chartRatio R (2 * w - 1)) ≤ 32 / 15 :=
    separateCoeff_le_of_quarter (chartRatio_nonneg hR _) (chartRatio_le_quarter hR hm)
  have hct : separateCoeff (chartRatio R (2 * w)) ≤ 32 / 15 :=
    separateCoeff_le_of_quarter (chartRatio_nonneg hR _) (chartRatio_le_quarter hR hp)
  refine h.trans ?_
  have hS : 0 ≤ tailInvSq riemannXi R := tailInvSq_nonneg (f := riemannXi) R
  have hsn : 0 ≤ ‖(2 * w - 1) - 1 / 2‖ := norm_nonneg _
  have htn : 0 ≤ ‖2 * w - 1 / 2‖ := norm_nonneg _
  refine mul_le_mul_of_nonneg_right ?_ hS
  nlinarith [mul_le_mul_of_nonneg_right hcs hsn, mul_le_mul_of_nonneg_right hct htn]

/-- **Both bounds and their minimum on the common closed `R/8` chart.** -/
theorem norm_modularScattering_residual_le_eighth_min {R : ℝ} (hR : 0 < R) {w : ℂ}
    (hw0 : w ≠ 0) (hwHalf : w ≠ 1 / 2) (hw1 : w ≠ 1)
    (hξm : riemannXi (2 * w - 1) ≠ 0) (hξp : riemannXi (2 * w) ≠ 0)
    (hm : 2 * w - 1 ∈ closedBall (1 / 2 : ℂ) (R / 8))
    (hp : 2 * w ∈ closedBall (1 / 2 : ℂ) (R / 8)) :
    ‖logDeriv modularScattering w - finiteScatteringCurrent hR w‖ ≤
      min (544 / 225) ((32 / 15) * (‖(2 * w - 1) - 1 / 2‖ + ‖2 * w - 1 / 2‖)) *
        tailInvSq riemannXi R := by
  have h1 := norm_modularScattering_residual_le_eighth_paired hR hw0 hwHalf hw1 hξm hξp hm hp
  have h2 := norm_modularScattering_residual_le_eighth_separate hR hw0 hwHalf hw1 hξm hξp hm hp
  rcases le_total (544 / 225 : ℝ) ((32 / 15) * (‖(2 * w - 1) - 1 / 2‖ + ‖2 * w - 1 / 2‖)) with h | h
  · rw [min_eq_left h]
    exact h1
  · rw [min_eq_right h]
    exact h2

/-- The sum `|2w - 3/2| + |2w - 1/2|` is at least `1`: the two arguments are one apart. -/
theorem one_le_norm_pulled_sum (w : ℂ) :
    1 ≤ ‖(2 * w - 1) - 1 / 2‖ + ‖2 * w - 1 / 2‖ := by
  have h : ‖(2 * w - 1 / 2) - ((2 * w - 1) - 1 / 2)‖ ≤
      ‖2 * w - 1 / 2‖ + ‖(2 * w - 1) - 1 / 2‖ := norm_sub_le _ _
  have e : (2 * w - 1 / 2) - ((2 * w - 1) - 1 / 2) = (1 : ℂ) := by ring
  rw [e, norm_one] at h
  linarith

/-- **The comparison with the published coefficient.**  On the closed `R/8` chart the paired
coefficient `544/225` is below `4`, and `4 <= 4 (|2w - 3/2| + |2w - 1/2|)`: the paired bound is
at most the published one, with the exact rational slack `4 - 544/225 = 356/225` times
`tailInvSq` at the least.  The paired coefficient does not depend on how large the arguments
are in the chart; the published one grows with them. -/
theorem eighth_paired_le_published (R : ℝ) (w : ℂ) :
    (544 / 225 : ℝ) * tailInvSq riemannXi R ≤
      4 * (‖(2 * w - 1) - 1 / 2‖ + ‖2 * w - 1 / 2‖) * tailInvSq riemannXi R := by
  have h := one_le_norm_pulled_sum w
  have hS : 0 ≤ tailInvSq riemannXi R := tailInvSq_nonneg (f := riemannXi) R
  refine mul_le_mul_of_nonneg_right ?_ hS
  linarith

end Xi

end Holonics.Zeta.ModularScatteringPairedTail

#print axioms Holonics.Zeta.ModularScatteringPairedTail.tankC_sub_tankC
#print axioms Holonics.Zeta.ModularScatteringPairedTail.pair_identity
#print axioms Holonics.Zeta.ModularScatteringPairedTail.tankC_sub_eq_pair
#print axioms Holonics.Zeta.ModularScatteringPairedTail.norm_tankC_sub_le
#print axioms Holonics.Zeta.ModularScatteringPairedTail.norm_tankC_le
#print axioms Holonics.Zeta.ModularScatteringPairedTail.norm_pairKernel_le
#print axioms Holonics.Zeta.ModularScatteringPairedTail.pairedCoeff_le_of_quarter
#print axioms Holonics.Zeta.ModularScatteringPairedTail.separateCoeff_le_of_quarter
#print axioms Holonics.Zeta.ModularScatteringPairedTail.four_le_of_charts
#print axioms Holonics.Zeta.ModularScatteringPairedTail.four_lt_of_charts
#print axioms Holonics.Zeta.ModularScatteringPairedTail.tsum_reflect_tail
#print axioms Holonics.Zeta.ModularScatteringPairedTail.tailPair_eq_tsum
#print axioms Holonics.Zeta.ModularScatteringPairedTail.tank_sub_eq_pair
#print axioms Holonics.Zeta.ModularScatteringPairedTail.tailPair_eq_two_mul_tsum
#print axioms Holonics.Zeta.ModularScatteringPairedTail.tsum_idx_eq_tsum_zero
#print axioms Holonics.Zeta.ModularScatteringPairedTail.tsum_tail_idx_eq_tsum_tail_zero
#print axioms Holonics.Zeta.ModularScatteringPairedTail.summable_tail_zero_kernel
#print axioms Holonics.Zeta.ModularScatteringPairedTail.tailPair_eq_two_mul_tsum_zeros
#print axioms Holonics.Zeta.ModularScatteringPairedTail.norm_tailPair_le_paired
#print axioms Holonics.Zeta.ModularScatteringPairedTail.norm_tailPair_le_separate
#print axioms Holonics.Zeta.ModularScatteringPairedTail.norm_tailPair_le_min
#print axioms Holonics.Zeta.ModularScatteringPairedTail.norm_tailPair_le_paired_of_sub_eq_one
#print axioms Holonics.Zeta.ModularScatteringPairedTail.norm_tailPair_le_eighth
#print axioms Holonics.Zeta.ModularScatteringPairedTail.norm_tailPair_le_eighth_separate
#print axioms Holonics.Zeta.ModularScatteringPairedTail.norm_xiRemainderPair_le_paired
#print axioms Holonics.Zeta.ModularScatteringPairedTail.norm_xiRemainderPair_le_separate
#print axioms Holonics.Zeta.ModularScatteringPairedTail.norm_modularScattering_residual_le_paired
#print axioms Holonics.Zeta.ModularScatteringPairedTail.norm_modularScattering_residual_le_separate
#print axioms Holonics.Zeta.ModularScatteringPairedTail.norm_modularScattering_residual_le_min
#print axioms Holonics.Zeta.ModularScatteringPairedTail.norm_modularScattering_residual_le_published
#print axioms Holonics.Zeta.ModularScatteringPairedTail.norm_modularScattering_residual_le_eighth_paired
#print axioms Holonics.Zeta.ModularScatteringPairedTail.norm_modularScattering_residual_le_eighth_separate
#print axioms Holonics.Zeta.ModularScatteringPairedTail.norm_modularScattering_residual_le_eighth_min
#print axioms Holonics.Zeta.ModularScatteringPairedTail.eighth_paired_le_published
