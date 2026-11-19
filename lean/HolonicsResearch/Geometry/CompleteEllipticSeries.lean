import Mathlib
import HolonicsResearch.Geometry.EggModular

/-!
# The complete elliptic integral is a hypergeometric series: `K(√λ) = (π/2) ₂F₁(½, ½; 1; λ)`

Source: #410's box "Monodromy as a group of moves", its clause on `K(√λ) = (π/2) ₂F₁(½, ½; 1; λ)` (the record of
November 18 on the modular group, §3, "The free product"). `Geometry/ModularFreeProduct` and
`Geometry/LegendreLevelTwo` give the group that the monodromy of Legendre's family `y² = x(x − 1)(x − λ)` is claimed
to be; this file gives the period that the monodromy moves, as a series in `λ`. `Geometry/EggModular` proved the
identity coefficient by coefficient (`egg_period_coefficient`: each coefficient is a binomial coefficient times a
Wallis integral) and left the analytic interchange and `K` itself owed (atlas `egg.period-coefficients`); this
file proves both, reusing that module's coefficient algebra.

[proved-standard; formal-checked] What is proved.

1. **The Wallis weight** (§1). `w_n = ∏_(i<n) (2i + 1)/(2i + 2)` (`wallis`) lies in `[0, 1]` (`wallis_nonneg`,
   `wallis_le_one`), is `C(2n, n)/4ⁿ` and `(½)_n / n!` (`wallis_eq_centralBinom`, `wallis_eq_pochhammer`, from
   `EggModular.wallis_centralBinom` and `EggModular.halfPochhammer_div_factorial`), and is the binomial
   coefficient `Ring.choose (½ + n − 1) n` of the series of `(1 − x)^(−1/2)` (`choose_eq_wallis`).
2. **The binomial series** (§2). `(1 − x)^(−1/2) = Σ w_n xⁿ` for `0 ≤ x < 1` (`hasSum_inv_sqrt_one_sub`), read
   from Mathlib's power series of `1/(1 − x)^a` on the unit ball.
3. **Wallis's quarter turn** (§3). `∫₀^(π/2) sin^(2n) θ dθ = (π/2) w_n` (`integral_sin_pow_even_half`): Mathlib's
   half-turn integral split at `π/2` and folded by `θ ↦ π − θ`.
4. **The period as a series** (§4). With `K(k) = ∫₀^(π/2) (1 − k² sin²θ)^(−1/2) dθ` (`ellipticK`),
   `K(√λ) = Σ (π/2) w_n² λⁿ` for `0 ≤ λ < 1` (`hasSum_ellipticK`), integrating the binomial series of
   `(1 − λ sin²θ)^(−1/2)` term by term under the dominating geometric series `λⁿ`.
5. **The hypergeometric form** (§5). The coefficient of `₂F₁(½, ½; 1; ·)` is `w_n²`, because `(1)_n = n!`
   (`hypergeometric_coefficient`, from `EggModular.egg_hypergeometric_coefficient`), so
   `K(√λ) = (π/2) ₂F₁(½, ½; 1; λ)` (`ellipticK_eq_hypergeometric`). The `₂F₁` is Mathlib's
   `ordinaryHypergeometric` over `ℝ`, not a series of this file's.

Limits. Only `0 ≤ λ < 1` is stated (negative `λ` down to `−1` is the same argument with an alternating dominating
series and is not written). The continuation of `K` round `λ = 0` and `λ = 1`, whose moves are claimed to generate
`Γ(2)/±1` (`Geometry/LegendreLevelTwo`; the local data and their rigidity are `Geometry/HypergeometricMonodromy`'s),
and the Schwarz map of the `(½, ⅓, 0)` triangle are not proved here; nor is the second
period `K′(√λ) = K(√(1 − λ))` or Legendre's relation between the two.

The computational object is the helical pair interaction: `K` is the quarter period of the pendulum in units of
`√(ℓ/g)`, the time a swing takes from its lowest point to its turning point, and the series reads that period as a
sum over the even powers `sin^(2n)` of the swing's phase, each weighted by a squared Wallis weight. Of the winding
guide's six general objects this touches the helix (the period of one turn) and the cell holonomy (the period
that Legendre's monodromy moves); the pair, faces and placement, the tube and the tower thread stay attached.

Consumers: the #410 box "Monodromy as a group of moves" and the atlas row `egg.period-coefficients`, whose owed
clause (the interchange and `K`) this file answers.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Geometry.CompleteEllipticSeries

open Real Finset Filter Topology intervalIntegral MeasureTheory

/-! ## §1 The Wallis weight -/

/-- [definition] The Wallis weight `w_n = ∏_(i<n) (2i + 1)/(2i + 2)`. -/
noncomputable def wallis (n : ℕ) : ℝ := ∏ i ∈ range n, (2 * (i : ℝ) + 1) / (2 * i + 2)

/-- [proved-standard; formal-checked] `w_0 = 1`. -/
theorem wallis_zero : wallis 0 = 1 := by simp [wallis]

/-- [proved-standard; formal-checked] `w_(n+1) = w_n (2n + 1)/(2n + 2)`. -/
theorem wallis_succ (n : ℕ) : wallis (n + 1) = wallis n * ((2 * (n : ℝ) + 1) / (2 * n + 2)) := by
  rw [wallis, wallis, prod_range_succ]

/-- [proved-standard; formal-checked] `0 ≤ w_n`. -/
theorem wallis_nonneg (n : ℕ) : 0 ≤ wallis n :=
  prod_nonneg fun i _ => by positivity

/-- [proved-standard; formal-checked] `w_n ≤ 1`. -/
theorem wallis_le_one (n : ℕ) : wallis n ≤ 1 := by
  induction n with
  | zero => simp [wallis_zero]
  | succ n ih =>
    rw [wallis_succ]
    have h1 : (2 * (n : ℝ) + 1) / (2 * n + 2) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    have h0 : 0 ≤ (2 * (n : ℝ) + 1) / (2 * n + 2) := by positivity
    calc wallis n * ((2 * (n : ℝ) + 1) / (2 * n + 2)) ≤ 1 * 1 :=
          mul_le_mul ih h1 h0 zero_le_one
      _ = 1 := by norm_num

/-- [proved-standard; formal-checked] `w_n = C(2n, n)/4ⁿ`, `Geometry/EggModular.wallis_centralBinom`. -/
theorem wallis_eq_centralBinom (n : ℕ) : wallis n = (n.centralBinom : ℝ) / 4 ^ n :=
  EggModular.wallis_centralBinom n

/-- [proved-standard; formal-checked] `w_n = (½)_n / n!`, through `C(2n, n)/4ⁿ`
(`Geometry/EggModular.halfPochhammer_div_factorial`). -/
theorem wallis_eq_pochhammer (n : ℕ) :
    wallis n = (ascPochhammer ℝ n).eval (1 / 2 : ℝ) / (n.factorial : ℝ) := by
  rw [EggModular.halfPochhammer_div_factorial, wallis_eq_centralBinom]

/-- [proved-standard; formal-checked] `Ring.choose (½ + n − 1) n = w_n`: the binomial coefficient of the series
of `(1 − x)^(−1/2)`. -/
theorem choose_eq_wallis (n : ℕ) : Ring.choose ((1 / 2 : ℝ) + n - 1) n = wallis n := by
  rw [← Ring.multichoose_eq, wallis_eq_pochhammer]
  have h := Ring.factorial_nsmul_multichoose_eq_ascPochhammer (1 / 2 : ℝ) n
  rw [Polynomial.ascPochhammer_smeval_eq_eval, nsmul_eq_mul] at h
  have hf : (n.factorial : ℝ) ≠ 0 := by positivity
  rw [← h]
  field_simp

/-! ## §2 The binomial series -/

/-- [proved-standard; formal-checked] `(1 − x)^(−1/2) = Σ w_n xⁿ` on `0 ≤ x < 1`. -/
theorem hasSum_inv_sqrt_one_sub {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    HasSum (fun n => wallis n * x ^ n) (Real.sqrt (1 - x))⁻¹ := by
  have hmem : x ∈ Metric.eball (0 : ℝ) 1 := by
    rw [Metric.mem_eball, edist_dist, Real.dist_eq, sub_zero, abs_of_nonneg hx0]
    exact ENNReal.ofReal_lt_one.mpr hx1
  have h := (one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero (1 / 2 : ℝ)).hasSum hmem
  simp only [FormalMultilinearSeries.ofScalars_apply_eq, choose_eq_wallis, smul_eq_mul,
    zero_add] at h
  have e : (Real.sqrt (1 - x))⁻¹ = 1 / (1 - x) ^ (1 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, inv_eq_one_div]
  rw [e]
  exact h

/-! ## §3 Wallis's quarter turn -/

/-- [proved-standard; formal-checked] Wallis's integral on the quarter turn: `∫₀^(π/2) sin^(2n) = (π/2) w_n`. -/
theorem integral_sin_pow_even_half (n : ℕ) :
    ∫ θ in (0)..(π / 2), sin θ ^ (2 * n) = π / 2 * wallis n := by
  have hfull : ∫ θ in (0)..π, sin θ ^ (2 * n) = π * wallis n := by
    rw [integral_sin_pow_even]; rfl
  have hc : Continuous fun θ : ℝ => sin θ ^ (2 * n) := by fun_prop
  have hsplit := integral_add_adjacent_intervals (hc.intervalIntegrable (μ := volume) 0 (π / 2))
    (hc.intervalIntegrable (μ := volume) (π / 2) π)
  have hsymm : ∫ θ in (π / 2)..π, sin θ ^ (2 * n) = ∫ θ in (0)..(π / 2), sin θ ^ (2 * n) := by
    have h := intervalIntegral.integral_comp_sub_left (fun θ => sin θ ^ (2 * n)) (a := 0)
      (b := π / 2) π
    simp only [Real.sin_pi_sub] at h
    rw [show π - π / 2 = π / 2 by ring, sub_zero] at h
    exact h.symm
  rw [hsymm, hfull] at hsplit
  linarith

/-! ## §4 The period as a series -/

/-- [definition] The complete elliptic integral of the first kind,
`K(k) = ∫₀^(π/2) (1 − k² sin²θ)^(−1/2) dθ`. -/
noncomputable def ellipticK (k : ℝ) : ℝ := ∫ θ in (0)..(π / 2), (Real.sqrt (1 - k ^ 2 * sin θ ^ 2))⁻¹

/-- [proved-standard; formal-checked] `K(√λ) = Σ (π/2) w_n² λⁿ` for `0 ≤ λ < 1`, integrated term by term. -/
theorem hasSum_ellipticK {l : ℝ} (h0 : 0 ≤ l) (h1 : l < 1) :
    HasSum (fun n => π / 2 * wallis n ^ 2 * l ^ n) (ellipticK (Real.sqrt l)) := by
  have hk : Real.sqrt l ^ 2 = l := Real.sq_sqrt h0
  unfold ellipticK
  rw [hk]
  have hterm : ∀ n : ℕ, ∫ θ in (0)..(π / 2), wallis n * l ^ n * sin θ ^ (2 * n) =
      π / 2 * wallis n ^ 2 * l ^ n := by
    intro n
    rw [intervalIntegral.integral_const_mul, integral_sin_pow_even_half]
    ring
  have hsum := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume) (a := 0)
    (b := π / 2) (F := fun n θ => wallis n * l ^ n * sin θ ^ (2 * n))
    (f := fun θ => (Real.sqrt (1 - l * sin θ ^ 2))⁻¹) (fun n _ => l ^ n)
    (fun n => (by fun_prop : Continuous fun θ : ℝ => wallis n * l ^ n * sin θ ^ (2 * n)).aestronglyMeasurable)
    (fun n => Filter.Eventually.of_forall fun θ _ => by
      have hw := wallis_le_one n
      have hs : sin θ ^ (2 * n) ≤ 1 := by
        rw [pow_mul]
        exact pow_le_one₀ (sq_nonneg _) (sin_sq_le_one θ)
      have hl : 0 ≤ l ^ n := pow_nonneg h0 n
      have hs0 : 0 ≤ sin θ ^ (2 * n) := by rw [pow_mul]; exact pow_nonneg (sq_nonneg _) n
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (wallis_nonneg n) hl) hs0)]
      calc wallis n * l ^ n * sin θ ^ (2 * n) ≤ 1 * l ^ n * 1 := by
            apply mul_le_mul (mul_le_mul_of_nonneg_right hw hl) hs hs0 (by positivity)
        _ = l ^ n := by ring)
    (Filter.Eventually.of_forall fun θ _ => summable_geometric_of_lt_one h0 h1)
    intervalIntegrable_const
    (Filter.Eventually.of_forall fun θ _ => by
      have hx0 : 0 ≤ l * sin θ ^ 2 := by positivity
      have hx1 : l * sin θ ^ 2 < 1 := by nlinarith [sin_sq_le_one θ]
      have hs := hasSum_inv_sqrt_one_sub hx0 hx1
      have e : (fun n : ℕ => wallis n * l ^ n * sin θ ^ (2 * n)) =
          fun n => wallis n * (l * sin θ ^ 2) ^ n := by
        funext n
        rw [mul_pow, ← pow_mul]
        ring
      show HasSum (fun n : ℕ => wallis n * l ^ n * sin θ ^ (2 * n)) (Real.sqrt (1 - l * sin θ ^ 2))⁻¹
      rw [e]
      exact hs)
  rw [show (fun n => π / 2 * wallis n ^ 2 * l ^ n) =
    fun n => ∫ θ in (0)..(π / 2), wallis n * l ^ n * sin θ ^ (2 * n) from funext fun n => (hterm n).symm]
  exact hsum

/-! ## §5 The hypergeometric form -/

/-- [proved-standard; formal-checked] The coefficient of `₂F₁(½, ½; 1; ·)` is `w_n²`, from
`Geometry/EggModular.egg_hypergeometric_coefficient`. -/
theorem hypergeometric_coefficient (n : ℕ) :
    ordinaryHypergeometricCoefficient (1 / 2 : ℝ) (1 / 2) 1 n = wallis n ^ 2 := by
  rw [EggModular.egg_hypergeometric_coefficient, wallis_eq_centralBinom]

/-- [proved-standard; formal-checked] **`K(√λ) = (π/2) ₂F₁(½, ½; 1; λ)`** for `0 ≤ λ < 1`, with Mathlib's
`ordinaryHypergeometric`. -/
theorem ellipticK_eq_hypergeometric {l : ℝ} (h0 : 0 ≤ l) (h1 : l < 1) :
    ellipticK (Real.sqrt l) = π / 2 * ordinaryHypergeometric (𝔸 := ℝ) (1 / 2 : ℝ) (1 / 2) 1 l := by
  rw [ordinaryHypergeometric, ordinaryHypergeometric_sum_eq]
  have h := hasSum_ellipticK h0 h1
  rw [← h.tsum_eq, ← tsum_mul_left]
  congr 1
  funext n
  have hc := hypergeometric_coefficient n
  rw [ordinaryHypergeometricCoefficient] at hc
  rw [hc, smul_eq_mul]
  ring

end Holonics.Geometry.CompleteEllipticSeries
