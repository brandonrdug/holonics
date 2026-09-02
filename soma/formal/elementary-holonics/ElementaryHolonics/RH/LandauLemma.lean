import ElementaryHolonics.RH.LogDerivativeRemainder

/-!
# Landau's lemma given a zero factorization

Suppose `f = P · unit` on a disc of radius `r`, where `P` is the monic polynomial of the zeros of
`f` in the half disc (with multiplicity, total count `N`) and `unit` is analytic and nonvanishing
on the disc.  If `‖f‖ ≤ ‖f z₀‖ e^M` on the disc, the maximum principle transfers the bound to the
unit on the three-quarter disc at the cost of `2^N` (each zero factor loses at most one halving
of the radius), and Landau's remainder bound then gives, on the `r/8` disc off the zeros,

    ‖ f′/f (z) − Σ_ρ m_ρ /(z − ρ) ‖ ≤ 16 (M + N log 2) / r.

The log-derivative of `f` is the Coulomb flux of its zero comb plus a bounded background.
The constant is the product expansion `16 = 2⁴`, from `8 · 2`.  The unit need only avoid
zero on the half disc, so zeros of `f` in the outer annulus may stay inside the unit.
-/

noncomputable section

namespace Soma.Holonics.RH.LandauLemma

open Complex Metric Set Finset
open Soma.Holonics.RH.LogDerivativeRemainder

/-- A zero factorization of `f` on the disc `ball z₀ r`: the zeros of the half disc, their
multiplicities, and the nonvanishing analytic unit. -/
structure ZeroFactorization (f : ℂ → ℂ) (z₀ : ℂ) (r : ℝ) where
  zeros : Finset ℂ
  mult : ℂ → ℕ
  unit : ℂ → ℂ
  zeros_mem : ∀ ρ ∈ zeros, ρ ∈ closedBall z₀ (r / 2)
  mult_pos : ∀ ρ ∈ zeros, 0 < mult ρ
  unit_diff : DifferentiableOn ℂ unit (ball z₀ r)
  unit_ne : ∀ z ∈ ball z₀ (r / 2), unit z ≠ 0
  factor : ∀ z ∈ ball z₀ r, f z = (∏ ρ ∈ zeros, (z - ρ) ^ mult ρ) * unit z

namespace ZeroFactorization

variable {f : ℂ → ℂ} {z₀ : ℂ} {r : ℝ} (Z : ZeroFactorization f z₀ r)

/-- The total multiplicity. -/
def count : ℕ := ∑ ρ ∈ Z.zeros, Z.mult ρ

/-- The polynomial of the zeros. -/
def poly (z : ℂ) : ℂ := ∏ ρ ∈ Z.zeros, (z - ρ) ^ Z.mult ρ

theorem norm_poly_ge {z : ℂ} (hz : z ∈ sphere z₀ (3 * r / 4)) (hr : 0 < r) :
    (r / 4) ^ Z.count ≤ ‖Z.poly z‖ := by
  unfold poly count
  rw [norm_prod, ← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_le_prod (fun _ _ => by positivity)
  intro ρ hρ
  rw [norm_pow]
  apply pow_le_pow_left₀ (by positivity)
  have h1 : ‖z - z₀‖ = 3 * r / 4 := by rw [mem_sphere_iff_norm] at hz; exact hz
  have h2 : ‖ρ - z₀‖ ≤ r / 2 := by
    have := Z.zeros_mem ρ hρ
    rw [mem_closedBall_iff_norm] at this
    exact this
  calc r / 4 = 3 * r / 4 - r / 2 := by ring
    _ ≤ ‖z - z₀‖ - ‖ρ - z₀‖ := by linarith
    _ ≤ ‖(z - z₀) - (ρ - z₀)‖ := norm_sub_norm_le _ _
    _ = ‖z - ρ‖ := by ring_nf

theorem norm_poly_centre_le : ‖Z.poly z₀‖ ≤ (r / 2) ^ Z.count := by
  unfold poly count
  rw [norm_prod, ← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
  intro ρ hρ
  rw [norm_pow]
  apply pow_le_pow_left₀ (norm_nonneg _)
  have := Z.zeros_mem ρ hρ
  rw [mem_closedBall_iff_norm] at this
  rw [← norm_neg, neg_sub]
  exact this

/-- **The maximum principle transfers the growth bound to the unit** at the cost of `2^N`. -/
theorem norm_unit_le (hr : 0 < r) (hf₀ : f z₀ ≠ 0)
    (hf : ∀ z ∈ ball z₀ r, ‖f z‖ ≤ ‖f z₀‖ * Real.exp M) {z : ℂ} (hz : z ∈ ball z₀ (3 * r / 4)) :
    ‖Z.unit z‖ ≤ ‖Z.unit z₀‖ * Real.exp (M + Z.count * Real.log 2) := by
  have hz₀ : z₀ ∈ ball z₀ r := mem_ball_self hr
  have hpoly₀ : Z.poly z₀ ≠ 0 := by
    intro h
    have := Z.factor z₀ hz₀
    unfold poly at h
    rw [h, zero_mul] at this
    exact hf₀ this
  have hunit₀ : ‖Z.unit z₀‖ = ‖f z₀‖ / ‖Z.poly z₀‖ := by
    have := Z.factor z₀ hz₀
    unfold poly at hpoly₀ ⊢
    rw [this, norm_mul, mul_div_cancel_left₀ _ (norm_ne_zero_iff.mpr hpoly₀)]
  -- the bound on the sphere of radius 3r/4
  have hsphere : ∀ w ∈ sphere z₀ (3 * r / 4),
      ‖Z.unit w‖ ≤ ‖Z.unit z₀‖ * Real.exp (M + Z.count * Real.log 2) := by
    intro w hw
    have hwball : w ∈ ball z₀ r := by
      rw [mem_sphere_iff_norm] at hw
      rw [mem_ball_iff_norm, hw]
      linarith
    have hfw := hf w hwball
    have hpw := Z.norm_poly_ge hw hr
    have hpw_pos : 0 < ‖Z.poly w‖ := lt_of_lt_of_le (by positivity) hpw
    have hfac := Z.factor w hwball
    have hunit_w : ‖Z.unit w‖ = ‖f w‖ / ‖Z.poly w‖ := by
      unfold poly at hpw_pos ⊢
      rw [hfac, norm_mul, mul_div_cancel_left₀ _ hpw_pos.ne']
    have hexp : Real.exp (M + Z.count * Real.log 2) = Real.exp M * 2 ^ Z.count := by
      rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log two_pos]
    rw [hunit_w, hunit₀, hexp, div_le_iff₀ hpw_pos]
    have hp₀ := Z.norm_poly_centre_le
    have hp₀_pos : 0 < ‖Z.poly z₀‖ := norm_pos_iff.mpr hpoly₀
    have hf₀_pos : 0 < ‖f z₀‖ := norm_pos_iff.mpr hf₀
    -- ‖f w‖ ≤ ‖f z₀‖ e^M ≤ (‖f z₀‖/‖P z₀‖) e^M 2^N ‖P w‖ since ‖P z₀‖ 2^N ... ≤ ... 
    have hkey : ‖Z.poly z₀‖ ≤ 2 ^ Z.count * ‖Z.poly w‖ := by
      calc ‖Z.poly z₀‖ ≤ (r / 2) ^ Z.count := hp₀
        _ = 2 ^ Z.count * (r / 4) ^ Z.count := by rw [← mul_pow]; ring_nf
        _ ≤ 2 ^ Z.count * ‖Z.poly w‖ := by
            apply mul_le_mul_of_nonneg_left hpw (by positivity)
    calc ‖f w‖ ≤ ‖f z₀‖ * Real.exp M := hfw
      _ = ‖f z₀‖ / ‖Z.poly z₀‖ * Real.exp M * ‖Z.poly z₀‖ := by
          field_simp
      _ ≤ ‖f z₀‖ / ‖Z.poly z₀‖ * Real.exp M * (2 ^ Z.count * ‖Z.poly w‖) := by
          apply mul_le_mul_of_nonneg_left hkey (by positivity)
      _ = ‖f z₀‖ / ‖Z.poly z₀‖ * (Real.exp M * 2 ^ Z.count) * ‖Z.poly w‖ := by ring
  -- maximum principle on the three-quarter ball
  have hbdd : Bornology.IsBounded (ball z₀ (3 * r / 4)) := Metric.isBounded_ball
  have hdc : DiffContOnCl ℂ Z.unit (ball z₀ (3 * r / 4)) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball z₀ (by positivity : 3 * r / 4 ≠ 0)]
    exact Z.unit_diff.mono (closedBall_subset_ball (by linarith))
  have hfront : ∀ w ∈ frontier (ball z₀ (3 * r / 4)),
      ‖Z.unit w‖ ≤ ‖Z.unit z₀‖ * Real.exp (M + Z.count * Real.log 2) := by
    intro w hw
    rw [frontier_ball z₀ (by positivity : 3 * r / 4 ≠ 0)] at hw
    exact hsphere w hw
  exact Complex.norm_le_of_forall_mem_frontier_norm_le hbdd hdc hfront (subset_closure hz)

/-- **Landau's lemma given the factorization.** Off the zeros, on the `r/8` disc, the
log-derivative of `f` is the Coulomb flux of the zero comb up to `16 (M + N log 2) / r`. -/
theorem norm_logDeriv_sub_flux_le (hr : 0 < r) (hM : 0 < M) (hf₀ : f z₀ ≠ 0)
    (hf : ∀ z ∈ ball z₀ r, ‖f z‖ ≤ ‖f z₀‖ * Real.exp M)
    {z : ℂ} (hz : z ∈ closedBall z₀ (r / 8)) (hfz : f z ≠ 0) :
    ‖logDeriv f z - ∑ ρ ∈ Z.zeros, (Z.mult ρ : ℂ) / (z - ρ)‖ ≤
      16 * (M + Z.count * Real.log 2) / r := by
  have hz' : z ∈ ball z₀ r := by
    rw [mem_closedBall_iff_norm] at hz
    rw [mem_ball_iff_norm]
    linarith
  -- the unit's log-derivative bound on the quarter of the three-quarter disc
  have hM' : 0 < M + Z.count * Real.log 2 := by
    have : 0 ≤ (Z.count : ℝ) * Real.log 2 := by positivity
    linarith
  have hunit_bound : ∀ w ∈ ball z₀ (r / 2),
      ‖Z.unit w‖ ≤ ‖Z.unit z₀‖ * Real.exp (M + Z.count * Real.log 2) :=
    fun w hw => Z.norm_unit_le hr hf₀ hf (ball_subset_ball (by linarith) hw)
  have hunit_diff : DifferentiableOn ℂ Z.unit (ball z₀ (r / 2)) :=
    Z.unit_diff.mono (ball_subset_ball (by linarith))
  have hunit_ne : ∀ w ∈ ball z₀ (r / 2), Z.unit w ≠ 0 := fun w hw => Z.unit_ne w hw
  have hzq : z ∈ closedBall z₀ ((r / 2) / 4) := by
    rw [mem_closedBall_iff_norm] at hz ⊢
    linarith
  have hrem := norm_logDeriv_le (by positivity : 0 < r / 2) hM' hunit_diff hunit_ne
    hunit_bound hzq
  -- the log-derivative of f splits as flux plus unit
  have hfeq : f =ᶠ[nhds z] fun w => Z.poly w * Z.unit w := by
    filter_upwards [isOpen_ball.mem_nhds hz'] with w hw
    exact Z.factor w hw
  have hpolyz : Z.poly z ≠ 0 := by
    intro h
    have := Z.factor z hz'
    unfold poly at h
    rw [h, zero_mul] at this
    exact hfz this
  have hfactor_ne : ∀ ρ ∈ Z.zeros, z - ρ ≠ 0 := by
    intro ρ hρ h
    apply hpolyz
    unfold poly
    exact Finset.prod_eq_zero hρ (by rw [h, zero_pow (Nat.pos_iff_ne_zero.mp (Z.mult_pos ρ hρ))])
  have hpoly_diff : DifferentiableAt ℂ Z.poly z := by
    unfold poly
    exact DifferentiableAt.fun_finsetProd fun ρ _ => (differentiableAt_id.sub_const ρ).pow _
  rw [(logDeriv_congr_nhds hfeq).eq_of_nhds,
    logDeriv_mul z hpolyz (Z.unit_ne z (by
      rw [mem_closedBall_iff_norm] at hz
      rw [mem_ball_iff_norm]
      linarith)) hpoly_diff
      (Z.unit_diff.differentiableAt (isOpen_ball.mem_nhds hz'))]
  have hpoly : logDeriv Z.poly z = ∑ ρ ∈ Z.zeros, (Z.mult ρ : ℂ) / (z - ρ) := by
    unfold poly
    rw [logDeriv_prod (s := Z.zeros) (f := fun ρ w => (w - ρ) ^ Z.mult ρ) (x := z)
      (fun ρ hρ => pow_ne_zero _ (hfactor_ne ρ hρ))
      (fun ρ _ => (differentiableAt_id.sub_const ρ).pow _)]
    apply Finset.sum_congr rfl
    intro ρ hρ
    rw [logDeriv_fun_pow (f := fun w => w - ρ) (differentiableAt_id.sub_const ρ), logDeriv_apply,
      deriv_sub_const,
      deriv_id'']
    ring
  rw [hpoly, add_sub_cancel_left, logDeriv_apply]
  calc ‖deriv Z.unit z / Z.unit z‖ ≤ 8 * (M + Z.count * Real.log 2) / (r / 2) := hrem
    _ = 16 * (M + Z.count * Real.log 2) / r := by
        field_simp
        ring

end ZeroFactorization

end Soma.Holonics.RH.LandauLemma
