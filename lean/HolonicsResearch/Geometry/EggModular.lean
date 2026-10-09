import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-!
# The egg's modular face: the Legendre `j` and the square lattice

[definition] `research/records/2026-09-27_EGG_PACKING_THE_MOIRE_OF_TWO_HELICES_IS_A_TORUS_KNOT_AND_THE_TREFOIL_IS_THE_HALF_TURN_WITH_THE_THIRD_TURN.md`
and the September 27 probability derivation (§5). The Hügelschäffer egg with semi-axis `a` and
displacement `w` carries the Legendre parameter `λ = ((a − w)/(a + w))²`; with `β = w/a` it is
`λ(β) = ((1 − β)/(1 + β))²` (`eggLambda`). The modular invariant of the Legendre curve
`y² = x(x − 1)(x − λ)` is

`j(λ) = 256 (1 − λ + λ²)³ / (λ² (1 − λ)²)` (`legendreJ`).

[proved-derived; formal-checked] What is proved, over any field for `j` and over `ℝ` for the egg.

1. **`j` forgets the labelling of the three finite branch points.** It is invariant under the six
   anharmonic images `λ, 1 − λ, 1/λ, 1/(1 − λ), (λ − 1)/λ, λ/(λ − 1)` (`legendreJ_anharmonic`):
   the half-turn `λ ↦ 1 − λ` and the inversion `λ ↦ 1/λ` generate the cross-ratio action of the
   permutations of the branch points.
2. **The square lattice.** `j − 1728 = 64 (λ + 1)² (λ − 2)² (2λ − 1)² / (λ² (1 − λ)²)`
   (`legendreJ_sub_1728`), so `j = 1728` exactly on the orbit `{−1, 1/2, 2}`, and
   `j(1/2) = 1728` (`legendreJ_half`).
3. **The egg reaches it at one displacement** (`egg_j_of_legendre_lambda`): for `0 < β < 1`,
   `λ(β) = 1/2` exactly when `β² − 6β + 1 = 0`, exactly when `β = 3 − 2√2`; there the egg's
   Legendre curve has `j = 1728`. The irrational displacement is carried as its constraint
   identity `β² − 6β + 1 = 0`, and `√2` as the root of `x² = 2`.

4. **The hyperbolic face** (`hyperbolic_circle_euclidean_equation`): in the upper half-plane with
   Mathlib's hyperbolic distance, the points at distance `r ≥ 0` from `(x₀, y₀)` are exactly the
   Euclidean circle `(x − x₀)² + (y − y₀ cosh r)² = y₀² sinh² r`; its top and bottom are
   `y₀ eʳ` and `y₀ e⁻ʳ` (`hyperbolic_circle_vertical_extent`). A Gaussian's Fisher form is
   `2(dx² + dy²)/y²` at `x = μ/√2`, `y = σ`, so a Fisher radius `R` is the hyperbolic radius
   `r = R/√2`. The lopsided circle is egg-like by interpretation only: no receiver map or
   preserved flux joins it to the Hügelschäffer egg.
5. **The period's hypergeometric coefficients** (`egg_hypergeometric_coefficient`,
   `egg_period_coefficient`): `₂F₁(½, ½; 1; λ)` has coefficients `((½)_j/j!)² = (C(2j, j)/4ʲ)²`
   (`halfPochhammer_div_factorial`), and `(π/2)` times the `j`-th is the `j`-th term of
   `K(k) = ∫₀^(π/2) (1 − k² sin²θ)^(−1/2) dθ` expanded in `k²`: the binomial coefficient
   `C(2j, j)/4ʲ` of `(1 − x)^(−1/2)` times the Wallis integral `½∫₀^π sin^(2j)`
   (Mathlib's `integral_sin_pow_even`, `wallis_centralBinom`).

[open] Mathlib has no complete elliptic integral `K`, so the analytic join
`K(√λ) = (π/2) ₂F₁(½, ½; 1; λ)` (the termwise integration of the binomial series) is stated here
only term by term. The Schwarz map of the `(½, ⅓, 0)` triangle whose inverse is `1728/j` and the
identification of its monodromy with `PSL(2, ℤ)` remain named analytic obligations in #62.
-/

namespace Holonics.Geometry.EggModular

section Field

variable {K : Type*} [Field K]

/-- [definition] **The modular invariant of the Legendre curve** `y² = x(x − 1)(x − λ)`. -/
def legendreJ (l : K) : K :=
  256 * (1 - l + l ^ 2) ^ 3 / (l ^ 2 * (1 - l) ^ 2)

/-- [proved-derived; formal-checked] **`j` is invariant under the six anharmonic images.** -/
theorem legendreJ_anharmonic {l : K} (h0 : l ≠ 0) (h1 : l ≠ 1) :
    legendreJ (1 - l) = legendreJ l ∧ legendreJ l⁻¹ = legendreJ l ∧
      legendreJ (1 - l)⁻¹ = legendreJ l ∧ legendreJ ((l - 1) / l) = legendreJ l ∧
        legendreJ (l / (l - 1)) = legendreJ l := by
  have h1' : 1 - l ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have h1'' : l - 1 ≠ 0 := sub_ne_zero.mpr h1
  have e2 : 1 - l⁻¹ = (l - 1) / l := by field_simp
  have e3 : 1 - (1 - l)⁻¹ = -l / (1 - l) := by field_simp; ring
  have e4 : 1 - (l - 1) / l = 1 / l := by field_simp; ring
  have e5 : 1 - l / (l - 1) = -1 / (l - 1) := by field_simp; ring
  unfold legendreJ
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [sub_sub_cancel]
    ring
  · rw [e2]
    field_simp
    ring
  · rw [e3]
    field_simp
    ring
  · rw [e4]
    field_simp
    ring
  · rw [e5]
    field_simp
    ring

/-- [proved-derived; formal-checked] **The distance from the square lattice is a square.** -/
theorem legendreJ_sub_1728 {l : K} (h0 : l ≠ 0) (h1 : l ≠ 1) :
    legendreJ l - 1728 =
      64 * (l + 1) ^ 2 * (l - 2) ^ 2 * (2 * l - 1) ^ 2 / (l ^ 2 * (1 - l) ^ 2) := by
  have h1' : 1 - l ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  unfold legendreJ
  field_simp
  ring

end Field

/-- [proved-derived; formal-checked] **`j(1/2) = 1728`**, the square lattice. -/
theorem legendreJ_half : legendreJ (1 / 2 : ℚ) = 1728 := by
  norm_num [legendreJ]

/-- [definition] **The egg's Legendre parameter** at displacement ratio `β = w/a`. -/
noncomputable def eggLambda (β : ℝ) : ℝ := ((1 - β) / (1 + β)) ^ 2

/-- [proved-derived; formal-checked] **`egg_j_of_legendre_lambda`.** For `0 < β < 1` the egg's
Legendre parameter is `1/2` exactly when `β² − 6β + 1 = 0`, exactly when `β = 3 − 2√2`; there its
`j` is `1728`. -/
theorem egg_j_of_legendre_lambda {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    (eggLambda β = 1 / 2 ↔ β ^ 2 - 6 * β + 1 = 0) ∧
      (β ^ 2 - 6 * β + 1 = 0 ↔ β = 3 - 2 * Real.sqrt 2) ∧
      (eggLambda β = 1 / 2 → legendreJ (eggLambda β) = 1728) := by
  have hpos : 1 + β ≠ 0 := by linarith
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hquad : eggLambda β = 1 / 2 ↔ β ^ 2 - 6 * β + 1 = 0 := by
    unfold eggLambda
    rw [div_pow, div_eq_div_iff (pow_ne_zero 2 hpos) two_ne_zero]
    constructor
    · intro h
      linear_combination h
    · intro h
      linear_combination h
  refine ⟨hquad, ?_, fun h => ?_⟩
  · constructor
    · intro h
      have hprod : (β - (3 - 2 * Real.sqrt 2)) * (β - (3 + 2 * Real.sqrt 2)) = 0 := by
        linear_combination h - 4 * hs
      rcases mul_eq_zero.mp hprod with h1 | h1
      · linarith
      · exfalso
        nlinarith
    · intro h
      rw [h]
      linear_combination 4 * hs
  · rw [h]
    norm_num [legendreJ]

/-! ## The hyperbolic face: an information circle is a lopsided Euclidean circle -/

section Hyperbolic

open UpperHalfPlane

/-- [proved-derived; formal-checked] **`hyperbolic_circle_euclidean_equation`.** In the upper
half-plane with its hyperbolic distance (`cosh d = 1 + |z − w|²/(2 Im z Im w)`, Mathlib's
`UpperHalfPlane.cosh_dist`), the circle of radius `r ≥ 0` about `w = (x₀, y₀)` is exactly the
Euclidean circle `(x − x₀)² + (y − y₀ cosh r)² = y₀² sinh² r`, through Mathlib's
`dist_eq_iff_dist_coe_center_eq`. -/
theorem hyperbolic_circle_euclidean_equation (z w : ℍ) {r : ℝ} (hr : 0 ≤ r) :
    dist z w = r ↔
      (z.re - w.re) ^ 2 + (z.im - w.im * Real.cosh r) ^ 2 = w.im ^ 2 * Real.sinh r ^ 2 := by
  rw [dist_eq_iff_dist_coe_center_eq]
  have hR : 0 ≤ w.im * Real.sinh r := mul_nonneg w.im_pos.le (Real.sinh_nonneg_iff.mpr hr)
  rw [← sq_eq_sq₀ dist_nonneg hR, Complex.dist_eq, Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, coe_re, coe_im, center_re, center_im]
  constructor <;> intro h <;> nlinarith [h]

/-- [proved-derived; formal-checked] The circle's top and bottom heights are `y₀ eʳ` and
`y₀ e⁻ʳ`: its Euclidean centre `y₀ cosh r` is their arithmetic mean and `y₀` their geometric
mean. -/
theorem hyperbolic_circle_vertical_extent (w : ℍ) (r : ℝ) :
    w.im * Real.cosh r + w.im * Real.sinh r = w.im * Real.exp r ∧
      w.im * Real.cosh r - w.im * Real.sinh r = w.im * Real.exp (-r) := by
  constructor
  · rw [← mul_add, Real.cosh_add_sinh]
  · rw [← mul_sub, Real.cosh_sub_sinh]

end Hyperbolic

/-! ## The period chart: the coefficients of `(π/2) ₂F₁(½, ½; 1; λ)` -/

section Period

open Polynomial

variable {K : Type*} [Field K] [CharZero K]

/-- [proved-derived; formal-checked] `(½)_j/j! = C(2j, j)/4ʲ`, the coefficient of `xʲ` in
`(1 − x)^(−1/2)`. -/
theorem halfPochhammer_div_factorial (j : ℕ) :
    (ascPochhammer K j).eval (1 / 2 : K) / (j.factorial : K) = (j.centralBinom : K) / 4 ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h' : ((j : K) + 1) * ((j + 1).centralBinom : K) =
        2 * (2 * j + 1) * (j.centralBinom : K) := by
      exact_mod_cast Nat.succ_mul_centralBinom_succ j
    have hf : (j.factorial : K) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
    have hj : (j : K) + 1 ≠ 0 := by exact_mod_cast j.succ_ne_zero
    rw [ascPochhammer_succ_eval, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
    have hcb : ((j + 1).centralBinom : K) =
        2 * (2 * j + 1) * (j.centralBinom : K) / ((j : K) + 1) := by
      rw [eq_div_iff hj, mul_comm]; exact h'
    have h4 : (4 : K) ^ j ≠ 0 := pow_ne_zero _ (by norm_num)
    have ih' : (ascPochhammer K j).eval (1 / 2 : K) =
        (j.centralBinom : K) * (j.factorial : K) / 4 ^ j := by
      rw [div_eq_div_iff hf h4] at ih
      rw [eq_div_iff h4, ih]
    rw [hcb, pow_succ, ih']
    field_simp
    ring

/-- [proved-derived; formal-checked] **The coefficients of `₂F₁(½, ½; 1; λ)`** (Mathlib's
`ordinaryHypergeometricCoefficient`) are `((½)_j/j!)² = (C(2j, j)/4ʲ)²`. -/
theorem egg_hypergeometric_coefficient (j : ℕ) :
    ordinaryHypergeometricCoefficient (1 / 2 : K) (1 / 2) 1 j =
      ((j.centralBinom : K) / 4 ^ j) ^ 2 := by
  have hf : (j.factorial : K) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
  rw [ordinaryHypergeometricCoefficient, ascPochhammer_eval_one, ← halfPochhammer_div_factorial]
  field_simp

/-- [proved-derived; formal-checked] Wallis's product is the central binomial ratio:
`∏_(i<n) (2i + 1)/(2i + 2) = C(2n, n)/4ⁿ`. -/
theorem wallis_centralBinom (n : ℕ) :
    ∏ i ∈ Finset.range n, (2 * (i : ℝ) + 1) / (2 * i + 2) = (n.centralBinom : ℝ) / 4 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ih]
    have h' : ((n : ℝ) + 1) * ((n + 1).centralBinom : ℝ) =
        2 * (2 * n + 1) * (n.centralBinom : ℝ) := by
      exact_mod_cast Nat.succ_mul_centralBinom_succ n
    have hn : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    rw [pow_succ]
    linear_combination (-(4 : ℝ) ^ n * 2) * h'

/-- [proved-derived; formal-checked] **The period's coefficients, term by term.** `(π/2)` times the
`j`-th coefficient of `₂F₁(½, ½; 1; λ)` is the `j`-th term of `K` expanded in `k² = λ`: the binomial
coefficient `C(2j, j)/4ʲ` of `(1 − k² sin²θ)^(−1/2)` times `∫₀^(π/2) sin^(2j) θ dθ`, carried as
`½∫₀^π` (Mathlib's `integral_sin_pow_even`). -/
theorem egg_period_coefficient (j : ℕ) :
    (Real.pi / 2) * ordinaryHypergeometricCoefficient (1 / 2 : ℝ) (1 / 2) 1 j =
      (j.centralBinom : ℝ) / 4 ^ j *
        ((1 / 2) * ∫ x in (0 : ℝ)..Real.pi, Real.sin x ^ (2 * j)) := by
  rw [egg_hypergeometric_coefficient, integral_sin_pow_even, wallis_centralBinom]
  ring

end Period

/-! ## The actual rational egg, with its arithmetic twist retained

[agent-inferred] The September 24 egg equation gives a full-two-torsion cubic,
not merely its `j` invariant. With `u = a²+w²+2wx`, put `X = -u` and
`V = (2w/b)uy`. Then `V² = X(X+(a-w)²)(X+(a+w)²)`. Thus the actual rational
egg enters `EllipticCurve/GeneralFace.E (-(a-w)²) (-(a+w)²)`. The negative
Legendre twist is carried by this equation; it is not discarded by labelling.

The equation transport below needs only `b ≠ 0`. A birational inverse also needs
`w ≠ 0` and `X ≠ 0`; nonsingular projective/group transport requires distinct
roots and a declared rational origin. Those stronger claims are not inferred
from this polynomial identity. The dated October 9 egg/arithmetic record names
the existing descent consumer and the remaining group/source obligations (#62).
-/

/-- The actual Hügelschäffer equation transports to the full-two-torsion cubic.
This retains the arithmetic twist which the modular invariant alone forgets. -/
theorem egg_to_fullTwoTorsion (a b w x y : ℚ) (hb : b ≠ 0)
    (hegg : (a ^ 2 + w ^ 2 + 2 * w * x) * y ^ 2 = b ^ 2 * (a ^ 2 - x ^ 2)) :
    ((2 * w / b) * (a ^ 2 + w ^ 2 + 2 * w * x) * y) ^ 2 =
      (-(a ^ 2 + w ^ 2 + 2 * w * x)) *
        (-(a ^ 2 + w ^ 2 + 2 * w * x) + (a - w) ^ 2) *
        (-(a ^ 2 + w ^ 2 + 2 * w * x) + (a + w) ^ 2) := by
  field_simp [hb]
  linear_combination (4 * w ^ 2 * (a ^ 2 + w ^ 2 + 2 * w * x)) * hegg

/-- A concrete consuming equation: the egg `a=3,b=2,w=1` enters the integral
model `GeneralFace.E (-4) (-16)`, with all producing operands retained. -/
theorem egg_321_fullTwoTorsion (x y : ℚ)
    (hegg : (10 + 2 * x) * y ^ 2 = 4 * (9 - x ^ 2)) :
    ((2 * x + 10) * y) ^ 2 =
      (-2 * x - 10) * (-2 * x - 10 + 4) * (-2 * x - 10 + 16) := by
  have h : ((3 : ℚ) ^ 2 + 1 ^ 2 + 2 * 1 * x) * y ^ 2 =
      2 ^ 2 * (3 ^ 2 - x ^ 2) := by
    convert hegg using 1 <;> ring
  have transported := egg_to_fullTwoTorsion 3 2 1 x y (by norm_num) h
  convert transported using 1 <;> ring

end Holonics.Geometry.EggModular

section Audit
open Holonics.Geometry.EggModular
#print axioms legendreJ_anharmonic
#print axioms legendreJ_sub_1728
#print axioms legendreJ_half
#print axioms egg_j_of_legendre_lambda
#print axioms hyperbolic_circle_euclidean_equation
#print axioms hyperbolic_circle_vertical_extent
#print axioms egg_hypergeometric_coefficient
#print axioms wallis_centralBinom
#print axioms egg_period_coefficient
#print axioms egg_to_fullTwoTorsion
#print axioms egg_321_fullTwoTorsion
end Audit
