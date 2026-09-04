import ElementaryHolonics.RH.ConjugationEntire

/-!
# Joint continuity of the flow and a Lipschitz bound in `t`

On `|t| ≤ T`, `‖z‖ ≤ R` the flow is bounded by a constant `K A B ρ T R`, the sum of the majorant
series.  Since `∂_t heatE t f = −heatE t f″`, the flow is Lipschitz in `t` on such boxes with
constant the bound of `f″`'s flow, and `(t, z) ↦ heatE t f z` is jointly continuous.  These are
the inputs for the stability of rectangle zero counts of `H_t` in `t`.
-/

open Complex Metric Filter Topology Set
open Soma.Holonics.RH.EntireDerivativeGrowth
open Soma.Holonics.RH.HeatFlowEntire
open Soma.Holonics.RH.HeatEquationEntire

namespace Soma.Holonics.RH.HeatFlowContinuity

variable {f : ℂ → ℂ} {A B ρ : ℝ}

/-- The majorant constant at `|t| ≤ T`. -/
noncomputable def CT (B ρ T : ℝ) : ℝ := 4 * Real.exp 1 * T * Real.exp (B * 2 ^ ρ)

/-- The bound of the flow on `|t| ≤ T`, `‖z‖ ≤ R`. -/
noncomputable def K (A B ρ T R : ℝ) : ℝ :=
  (A * Real.exp (B * 2 ^ ρ * R ^ ρ)) * ∑' k, majorant (CT B ρ T) (2 / ρ - 1) k

theorem CT_nonneg {B ρ T : ℝ} (hT : 0 ≤ T) : 0 ≤ CT B ρ T := by
  unfold CT
  positivity

theorem majorant_nonneg {C δ : ℝ} (hC : 0 ≤ C) (k : ℕ) : 0 ≤ majorant C δ k := by
  unfold majorant
  split_ifs
  · norm_num
  · exact pow_nonneg (mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg k) _)) k

theorem K_nonneg {A B ρ T R : ℝ} (hA : 0 ≤ A) (hT : 0 ≤ T) : 0 ≤ K A B ρ T R := by
  unfold K
  apply mul_nonneg (by positivity)
  exact tsum_nonneg (majorant_nonneg (CT_nonneg hT))

/-- The flow is bounded on boxes. -/
theorem norm_heatE_le (hf : Differentiable ℂ f) (hg : HasGrowth f A B ρ) (hA : 0 ≤ A)
    (hB : 0 ≤ B) (hρ0 : 0 < ρ) (hρ2 : ρ < 2) {T R : ℝ} (hT : 0 ≤ T) (hR : 0 ≤ R) {t : ℝ}
    (ht : |t| ≤ T) {z : ℂ} (hz : ‖z‖ ≤ R) : ‖heatE t f z‖ ≤ K A B ρ T R := by
  have hδ : 0 < 2 / ρ - 1 := by
    rw [sub_pos, lt_div_iff₀ hρ0]
    linarith
  have hsum := summable_heatTerm hf hg hA hB hρ0 hρ2 t z
  have hmaj : Summable (fun k => majorant (CT B ρ T) (2 / ρ - 1) k) :=
    summable_majorant (CT_nonneg hT) hδ
  have hM : 0 ≤ A * Real.exp (B * 2 ^ ρ * R ^ ρ) := by positivity
  have hterm : ∀ k, ‖heatTerm t f z k‖ ≤
      (A * Real.exp (B * 2 ^ ρ * R ^ ρ)) * majorant (CT B ρ T) (2 / ρ - 1) k := by
    intro k
    refine (norm_heatTerm_le_majorant hf hg hA hB hρ0 t hR hz k).trans ?_
    apply mul_le_mul_of_nonneg_left _ hM
    apply majorant_mono (by positivity) _ k
    unfold CT
    have : 0 ≤ 4 * Real.exp 1 * Real.exp (B * 2 ^ ρ) := by positivity
    calc 4 * Real.exp 1 * |t| * Real.exp (B * 2 ^ ρ)
        = (4 * Real.exp 1 * Real.exp (B * 2 ^ ρ)) * |t| := by ring
      _ ≤ (4 * Real.exp 1 * Real.exp (B * 2 ^ ρ)) * T := mul_le_mul_of_nonneg_left ht this
      _ = 4 * Real.exp 1 * T * Real.exp (B * 2 ^ ρ) := by ring
  calc ‖heatE t f z‖ ≤ ∑' k, ‖heatTerm t f z k‖ := norm_tsum_le_tsum_norm hsum
    _ ≤ ∑' k, (A * Real.exp (B * 2 ^ ρ * R ^ ρ)) * majorant (CT B ρ T) (2 / ρ - 1) k :=
        hsum.tsum_le_tsum hterm (hmaj.mul_left _)
    _ = K A B ρ T R := by
        unfold K
        rw [tsum_mul_left]

/-- The growth constants of `f″`. -/
theorem hasGrowth_deriv_deriv (hf : Differentiable ℂ f) (hg : HasGrowth f A B ρ) (hA : 0 ≤ A)
    (hB : 0 ≤ B) (hρ : 0 ≤ ρ) :
    HasGrowth (deriv (deriv f)) (A * Real.exp (B * 2 ^ ρ) * Real.exp (B * 2 ^ ρ * 2 ^ ρ))
      (B * 2 ^ ρ * 2 ^ ρ) ρ :=
  hasGrowth_deriv hf.deriv (hasGrowth_deriv hf hg hA hB hρ) (by positivity) (by positivity) hρ

/-- The Lipschitz constant of the flow in `t` on `|t| ≤ T`, `‖z‖ ≤ R`. -/
noncomputable def L (A B ρ T R : ℝ) : ℝ :=
  K (A * Real.exp (B * 2 ^ ρ) * Real.exp (B * 2 ^ ρ * 2 ^ ρ)) (B * 2 ^ ρ * 2 ^ ρ) ρ T R

theorem L_nonneg {A B ρ T R : ℝ} (hA : 0 ≤ A) (hT : 0 ≤ T) : 0 ≤ L A B ρ T R :=
  K_nonneg (by positivity) hT

/-- The flow is Lipschitz in `t` on boxes. -/
theorem norm_heatE_sub_le (hf : Differentiable ℂ f) (hg : HasGrowth f A B ρ) (hA : 0 ≤ A)
    (hB : 0 ≤ B) (hρ0 : 0 < ρ) (hρ2 : ρ < 2) {T R : ℝ} (hT : 0 ≤ T) (hR : 0 ≤ R) {s t : ℝ}
    (hs : |s| ≤ T) (ht : |t| ≤ T) {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖heatE s f z - heatE t f z‖ ≤ L A B ρ T R * |s - t| := by
  have hf'' : Differentiable ℂ (deriv (deriv f)) := hf.deriv.deriv
  have hg'' := hasGrowth_deriv_deriv hf hg hA hB hρ0.le
  have hconv : Convex ℝ (Icc (-T) T) := convex_Icc _ _
  have hderiv : ∀ u ∈ Icc (-T) T, HasDerivWithinAt (fun u : ℝ => heatE u f z)
      (-heatE u (deriv (deriv f)) z) (Icc (-T) T) u :=
    fun u _ => (hasDerivAt_heatE_t hf hg hA hB hρ0 hρ2 z u).hasDerivWithinAt
  have hbound : ∀ u ∈ Icc (-T) T, ‖-heatE u (deriv (deriv f)) z‖ ≤ L A B ρ T R := by
    intro u hu
    rw [norm_neg]
    exact norm_heatE_le hf'' hg'' (by positivity) (by positivity) hρ0 hρ2 hT hR
      (abs_le.mpr hu) hz
  have := hconv.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
    (abs_le.mp ht) (abs_le.mp hs)
  simpa [Real.norm_eq_abs] using this

/-- The flow is jointly continuous in `(t, z)`. -/
theorem continuous_heatE (hf : Differentiable ℂ f) (hg : HasGrowth f A B ρ) (hA : 0 ≤ A)
    (hB : 0 ≤ B) (hρ0 : 0 < ρ) (hρ2 : ρ < 2) :
    Continuous (fun p : ℝ × ℂ => heatE p.1 f p.2) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨t₀, z₀⟩
  rw [Metric.continuousAt_iff]
  intro ε hε
  have hz : ContinuousAt (heatE t₀ f) z₀ :=
    (differentiable_heatE hf hg hA hB hρ0 hρ2 t₀ z₀).continuousAt
  obtain ⟨δ₁, hδ₁, hz'⟩ := Metric.continuousAt_iff.mp hz (ε / 2) (by positivity)
  set T : ℝ := |t₀| + 1 with hT
  set R : ℝ := ‖z₀‖ + 1 with hR
  have hT0 : 0 ≤ T := by positivity
  have hR0 : 0 ≤ R := by positivity
  set Lc : ℝ := L A B ρ T R with hLc
  have hL0 : 0 ≤ Lc := L_nonneg hA hT0
  refine ⟨min (min δ₁ 1) (ε / (2 * (Lc + 1))), by positivity, ?_⟩
  rintro ⟨s, z⟩ hd
  rw [Prod.dist_eq] at hd
  simp only at hd
  have hd1 : dist s t₀ < min (min δ₁ 1) (ε / (2 * (Lc + 1))) :=
    lt_of_le_of_lt (le_max_left _ _) hd
  have hd2 : dist z z₀ < min (min δ₁ 1) (ε / (2 * (Lc + 1))) :=
    lt_of_le_of_lt (le_max_right _ _) hd
  have hs1 : |s - t₀| < 1 := by
    rw [Real.dist_eq] at hd1
    exact lt_of_lt_of_le hd1 ((min_le_left _ _).trans (min_le_right _ _))
  have hs2 : |s - t₀| < ε / (2 * (Lc + 1)) := by
    rw [Real.dist_eq] at hd1
    exact lt_of_lt_of_le hd1 (min_le_right _ _)
  have hz1 : ‖z - z₀‖ < 1 := by
    rw [dist_eq_norm] at hd2
    exact lt_of_lt_of_le hd2 ((min_le_left _ _).trans (min_le_right _ _))
  have hz2 : dist z z₀ < δ₁ :=
    lt_of_lt_of_le hd2 ((min_le_left _ _).trans (min_le_left _ _))
  have hsT : |s| ≤ T := by
    rw [hT]
    calc |s| = |(s - t₀) + t₀| := by ring_nf
      _ ≤ |s - t₀| + |t₀| := abs_add_le _ _
      _ ≤ |t₀| + 1 := by linarith
  have ht₀T : |t₀| ≤ T := by
    rw [hT]
    linarith
  have hzR : ‖z‖ ≤ R := by
    rw [hR]
    calc ‖z‖ = ‖(z - z₀) + z₀‖ := by ring_nf
      _ ≤ ‖z - z₀‖ + ‖z₀‖ := norm_add_le _ _
      _ ≤ ‖z₀‖ + 1 := by linarith
  have h1 : dist (heatE s f z) (heatE t₀ f z) < ε / 2 := by
    rw [dist_eq_norm]
    refine (norm_heatE_sub_le hf hg hA hB hρ0 hρ2 hT0 hR0 hsT ht₀T hzR).trans_lt ?_
    calc Lc * |s - t₀| ≤ Lc * (ε / (2 * (Lc + 1))) := mul_le_mul_of_nonneg_left hs2.le hL0
      _ < ε / 2 := by
        rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
  have h2 : dist (heatE t₀ f z) (heatE t₀ f z₀) < ε / 2 := hz' hz2
  calc dist (heatE s f z) (heatE t₀ f z₀)
      ≤ dist (heatE s f z) (heatE t₀ f z) + dist (heatE t₀ f z) (heatE t₀ f z₀) :=
        dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add h1 h2
    _ = ε := by ring

/-- `∂_z H_t` is jointly continuous in `(t, z)`. -/
theorem continuous_deriv_heatE (hf : Differentiable ℂ f) (hg : HasGrowth f A B ρ) (hA : 0 ≤ A)
    (hB : 0 ≤ B) (hρ0 : 0 < ρ) (hρ2 : ρ < 2) :
    Continuous (fun p : ℝ × ℂ => deriv (heatE p.1 f) p.2) := by
  have h : (fun p : ℝ × ℂ => deriv (heatE p.1 f) p.2) = fun p => heatE p.1 (deriv f) p.2 := by
    funext p
    exact deriv_heatE hf hg hA hB hρ0 hρ2 p.1 p.2
  rw [h]
  exact continuous_heatE hf.deriv (hasGrowth_deriv hf hg hA hB hρ0.le) (by positivity)
    (by positivity) hρ0 hρ2

end Soma.Holonics.RH.HeatFlowContinuity
