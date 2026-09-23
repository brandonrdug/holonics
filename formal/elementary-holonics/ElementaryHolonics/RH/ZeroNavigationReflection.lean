import ElementaryHolonics.RH.FiniteZeroCurrent

/-!
# The rightmost reflected current

For a finite Foster divisor, a zero whose real coordinate is maximal receives a nonnegative
normal current from every other zero.  Its same-height reflected partner contributes the
explicit reciprocal distance to the reflection seam.  This is a statement about the actual
finite zero comb, with its multiplicities; it does not assert that the corresponding global
source has no off-line zeros.
-/

noncomputable section

namespace Soma.Holonics.RH.ZeroNavigationReflection

open Complex Finset Filter Topology
open scoped ComplexConjugate
open Soma.Holonics.RH.PairPopulation
open Soma.Holonics.RH.TransverseCurrentBound
open Soma.Holonics.RH.FosterClassFlux
open Soma.Holonics.RH.FosterClassLandau
open Soma.Holonics.RH.FosterClassSplit
open Soma.Holonics.RH.FiniteZeroCurrent
open Soma.Holonics.RH.FosterClassHeatFlow
open Soma.Holonics.RH.HeatFlowEntire
open Soma.Holonics.RH.RiemannXi

private theorem weighted_re_nonneg {Z : Finset ℂ} {m : ℂ → ℕ} {s : ℂ}
    (hmax : ∀ w ∈ Z, w.re ≤ s.re) :
    0 ≤ (∑ w ∈ Z, (m w : ℂ) / (s - w)).re := by
  rw [Complex.re_sum]
  apply Finset.sum_nonneg
  intro w hw
  rw [Complex.div_re]
  simp only [Complex.natCast_re, Complex.natCast_im, zero_mul, zero_div, add_zero,
    Complex.sub_re]
  exact div_nonneg
    (mul_nonneg (by exact_mod_cast Nat.zero_le (m w)) (sub_nonneg.mpr (hmax w hw)))
    (Complex.normSq_nonneg _)

/-- At a rightmost finite zero, all other members of the multiplicity-weighted comb
contribute nonnegative normal current. -/
theorem reflectedFiniteSurplus_re_nonneg
    {f : ℂ → ℂ} {A B σ R : ℝ} [FosterClass f A B σ]
    (hR : 0 < R) {s : ℂ}
    (hmax : ∀ w ∈ (FosterClassSplit.Zfac (f := f) hR).zeros, w.re ≤ s.re) :
    0 ≤ (reflectedFiniteSurplus f A B σ hR s).re := by
  unfold reflectedFiniteSurplus
  apply weighted_re_nonneg
  intro w hw
  exact hmax w ((Finset.mem_erase.mp (Finset.mem_erase.mp hw).2).2)

/-- The finite current at a rightmost off-seam simple zero contains at least the
normal current of its same-height reflected partner.  The multiplier 2 is the
zero-velocity convention of the Foster/heat-flow owners. -/
theorem rightmost_comb_normal_lower
    {f : ℂ → ℂ} {A B σ R : ℝ} [FosterClass f A B σ]
    (hR : 0 < R) {s : ℂ}
    (hd : 0 < s.re - 1 / 2)
    (hmax : ∀ w ∈ (FosterClassSplit.Zfac (f := f) hR).zeros, w.re ≤ s.re)
    (hreflectmem : reflect s ∈ (FosterClassSplit.Zfac (f := f) hR).zeros)
    (hreflect_ne : reflect s ≠ s)
    (hmreflect : (FosterClassSplit.Zfac (f := f) hR).mult (reflect s) = 1) :
    1 / (s.re - 1 / 2) ≤ (2 * (comb' (f := f)) hR s s).re := by
  rw [comb'_eq_reflected_pair_add_surplus (f := f) hR hreflectmem
    hreflect_ne hmreflect]
  have hpair := two_re_inv_sub_reflect hd
  have hsurplus := reflectedFiniteSurplus_re_nonneg (f := f) hR hmax
  simp only [mul_add, Complex.add_re, Complex.mul_re] at *
  norm_num at *
  linarith

/-- The source-local factor at a rightmost simple zero inherits the reflected normal
current, with the exact finite-disc Foster tail as its only discrepancy.  This joins
the divisor/navigation receiver to the analytic source; it does not provide a
global ordering or a terminal continuation through a multiple zero. -/
theorem rightmost_local_factor_normal_lower
    {f : ℂ → ℂ} {A B σ R δ : ℝ} [FosterClass f A B σ]
    (hR : 0 < R) {s : ℂ} {g : ℂ → ℂ}
    (hd : 0 < s.re - 1 / 2)
    (hmax : ∀ w ∈ (FosterClassSplit.Zfac (f := f) hR).zeros, w.re ≤ s.re)
    (hreflectmem : reflect s ∈ (FosterClassSplit.Zfac (f := f) hR).zeros)
    (hreflect_ne : reflect s ≠ s)
    (hmreflect : (FosterClassSplit.Zfac (f := f) hR).mult (reflect s) = 1)
    (hδ : 0 < δ)
    (hball : ∀ y, dist y s < δ →
      (AnalyticAt ℂ g y ∧ g y ≠ 0) ∧ f y = (y - s) * g y)
    (hsmem : s ∈ (FosterClassSplit.Zfac (f := f) hR).zeros)
    (hms : (FosterClassSplit.Zfac (f := f) hR).mult s = 1)
    (hRa : ‖s - 1 / 2‖ + δ / 2 ≤ R / 8) :
    1 / (s.re - 1 / 2) -
      4 * (‖s - 1 / 2‖ + δ / 2) * FosterClassSplit.tailInvSq f R ≤
        (2 * logDeriv g s).re := by
  have hcomb := rightmost_comb_normal_lower (f := f) hR hd hmax
    hreflectmem hreflect_ne hmreflect
  have htail := (comb'_sub_le (f := f)) hδ hball hR hsmem hms hRa
  have hre := (Complex.re_le_norm ((comb' (f := f)) hR s s - logDeriv g s)).trans htail
  simp only [Complex.sub_re] at hre
  simp only [Complex.mul_re] at hcomb ⊢
  norm_num at hcomb ⊢
  linarith

/-- A source-qualified rightmost zero has inward normal velocity up to the exact
Foster exterior tail.  Unlike `re_negative_zero_velocity_le`, no surplus sign is
supplied as a separate premise: it is derived from finite-divisor ordering. -/
theorem rightmost_zero_velocity_normal_upper
    {f : ℂ → ℂ} {A B σ R δ : ℝ} [FosterClass f A B σ]
    (hR : 0 < R) {s : ℂ} {g : ℂ → ℂ}
    (hd : 0 < s.re - 1 / 2)
    (hmax : ∀ w ∈ (FosterClassSplit.Zfac (f := f) hR).zeros, w.re ≤ s.re)
    (hreflectmem : reflect s ∈ (FosterClassSplit.Zfac (f := f) hR).zeros)
    (hreflect_ne : reflect s ≠ s)
    (hmreflect : (FosterClassSplit.Zfac (f := f) hR).mult (reflect s) = 1)
    (hz : f s = 0) (hs : deriv f s ≠ 0)
    (hg : AnalyticAt ℂ g s) (hg0 : g s = deriv f s)
    (hev : ∀ᶠ z in 𝓝 s, f z = (z - s) * g z)
    (hδ : 0 < δ)
    (hball : ∀ y, dist y s < δ →
      (AnalyticAt ℂ g y ∧ g y ≠ 0) ∧ f y = (y - s) * g y)
    (hsmem : s ∈ (FosterClassSplit.Zfac (f := f) hR).zeros)
    (hms : (FosterClassSplit.Zfac (f := f) hR).mult s = 1)
    (hRa : ‖s - 1 / 2‖ + δ / 2 ≤ R / 8) :
    (-deriv (deriv f) s / deriv f s).re ≤
      -1 / (s.re - 1 / 2) +
        4 * (‖s - 1 / 2‖ + δ / 2) * FosterClassSplit.tailInvSq f R := by
  have hcomb := rightmost_comb_normal_lower (f := f) hR hd hmax
    hreflectmem hreflect_ne hmreflect
  have herror := norm_negative_zero_velocity_sub_comb_le (f := f)
    hz hs hg hg0 hev hδ hball hR hsmem hms hRa
  have hre := (Complex.re_le_norm
    (-deriv (deriv f) s / deriv f s - (-2 * (comb' (f := f)) hR s s))).trans herror
  simp only [Complex.sub_re, Complex.neg_re, Complex.mul_re] at hre hcomb
  norm_num at hre hcomb
  have hneg : -1 / (s.re - 1 / 2) = -(s.re - 1 / 2)⁻¹ := by
    simp [div_eq_mul_inv]
  rw [hneg]
  linarith

/-- The same theorem at the actual flowed xi source.  Its Foster instance is supplied
by `FosterClassHeatFlow.instFosterClassHeatE`; the explicit `A,B,σ` preserve the
growth-class chart used by the finite factorization. -/
theorem flowedXi_rightmost_zero_velocity_normal_upper
    {τ A B σ R δ : ℝ} [FosterClass (heatE (-τ) riemannXi) A B σ]
    (hR : 0 < R) {s : ℂ} {g : ℂ → ℂ}
    (hd : 0 < s.re - 1 / 2)
    (hmax : ∀ w ∈
      (FosterClassSplit.Zfac (f := heatE (-τ) riemannXi) hR).zeros, w.re ≤ s.re)
    (hreflectmem : reflect s ∈
      (FosterClassSplit.Zfac (f := heatE (-τ) riemannXi) hR).zeros)
    (hreflect_ne : reflect s ≠ s)
    (hmreflect : (FosterClassSplit.Zfac (f := heatE (-τ) riemannXi) hR).mult
      (reflect s) = 1)
    (hz : heatE (-τ) riemannXi s = 0)
    (hs : deriv (heatE (-τ) riemannXi) s ≠ 0)
    (hg : AnalyticAt ℂ g s)
    (hg0 : g s = deriv (heatE (-τ) riemannXi) s)
    (hev : ∀ᶠ z in 𝓝 s, heatE (-τ) riemannXi z = (z - s) * g z)
    (hδ : 0 < δ)
    (hball : ∀ y, dist y s < δ →
      (AnalyticAt ℂ g y ∧ g y ≠ 0) ∧
        heatE (-τ) riemannXi y = (y - s) * g y)
    (hsmem : s ∈
      (FosterClassSplit.Zfac (f := heatE (-τ) riemannXi) hR).zeros)
    (hms : (FosterClassSplit.Zfac (f := heatE (-τ) riemannXi) hR).mult s = 1)
    (hRa : ‖s - 1 / 2‖ + δ / 2 ≤ R / 8) :
    (-deriv (deriv (heatE (-τ) riemannXi)) s /
      deriv (heatE (-τ) riemannXi) s).re ≤
      -1 / (s.re - 1 / 2) +
        4 * (‖s - 1 / 2‖ + δ / 2) *
          FosterClassSplit.tailInvSq (heatE (-τ) riemannXi) R := by
  exact rightmost_zero_velocity_normal_upper (f := heatE (-τ) riemannXi)
    hR hd hmax hreflectmem hreflect_ne hmreflect hz hs hg hg0 hev
    hδ hball hsmem hms hRa

/-! ## A reflection-only obstruction -/

/-- An exact symmetric source with positive seam value and an off-seam divisor
strictly inside the critical strip.
It carries the same algebraic reflection and conjugation pattern as xi, but not
xi's arithmetic/archimedean constitution. -/
def reflectedQuadratic (s : ℂ) : ℂ := 1 / 4 - (2 * s - 1) ^ 2

theorem reflectedQuadratic_one_sub (s : ℂ) :
    reflectedQuadratic (1 - s) = reflectedQuadratic s := by
  unfold reflectedQuadratic
  ring

theorem reflectedQuadratic_conj (s : ℂ) :
    reflectedQuadratic (conj s) = conj (reflectedQuadratic s) := by
  simp only [reflectedQuadratic, map_sub, map_pow, map_mul, map_one]
  rw [Complex.conj_ofNat]
  norm_num [← Complex.ofReal_div, Complex.conj_ofReal, Complex.conj_ofNat]

theorem reflectedQuadratic_centre : reflectedQuadratic (1 / 2) = 1 / 4 := by
  norm_num [reflectedQuadratic]

theorem reflectedQuadratic_off_seam_zero :
    reflectedQuadratic (3 / 4) = 0 ∧
      (0 : ℝ) < (3 / 4 : ℂ).re ∧ (3 / 4 : ℂ).re < 1 ∧
        (3 / 4 : ℂ).re ≠ 1 / 2 := by
  norm_num [reflectedQuadratic]

/-- The exact forward heat continuation of the quadratic source, in the seam clock.
Its two off-seam zeros at time zero meet at a double seam zero at time `1/32`. -/
def reflectedHeatQuadratic (τ : ℝ) (s : ℂ) : ℂ :=
  reflectedQuadratic s - 8 * (τ : ℂ)

theorem reflectedHeatQuadratic_zero (s : ℂ) :
    reflectedHeatQuadratic 0 s = reflectedQuadratic s := by
  simp [reflectedHeatQuadratic]

theorem reflectedHeatQuadratic_thirtysecond (s : ℂ) :
    reflectedHeatQuadratic (1 / 32) s = -(2 * s - 1) ^ 2 := by
  norm_num [reflectedHeatQuadratic, reflectedQuadratic]

theorem reflectedHeatQuadratic_meets_on_seam :
    reflectedHeatQuadratic (1 / 32) (1 / 2) = 0 := by
  rw [reflectedHeatQuadratic_thirtysecond]
  norm_num

/-- Exact clock increment, without numerical differentiation. -/
theorem reflectedHeatQuadratic_clock_difference (τ ε : ℝ) (s : ℂ) :
    reflectedHeatQuadratic (τ + ε) s - reflectedHeatQuadratic τ s =
      -8 * (ε : ℂ) := by
  unfold reflectedHeatQuadratic
  push_cast
  ring

/-- Exact oriented second spatial difference. -/
theorem reflectedHeatQuadratic_spatial_second_difference
    (τ : ℝ) (s h : ℂ) :
    reflectedHeatQuadratic τ (s + h) -
      2 * reflectedHeatQuadratic τ s +
        reflectedHeatQuadratic τ (s - h) = -8 * h ^ 2 := by
  unfold reflectedHeatQuadratic reflectedQuadratic
  ring

/-- A finite exact heat equation for every real spatial step.  The time
increment equals the squared step, and both sides are polynomial identities. -/
theorem reflectedHeatQuadratic_discrete_heat (τ h : ℝ) (s : ℂ) :
    reflectedHeatQuadratic (τ + h ^ 2) s - reflectedHeatQuadratic τ s =
      reflectedHeatQuadratic τ (s + (h : ℂ)) -
        2 * reflectedHeatQuadratic τ s +
          reflectedHeatQuadratic τ (s - (h : ℂ)) := by
  rw [reflectedHeatQuadratic_clock_difference,
    reflectedHeatQuadratic_spatial_second_difference]
  push_cast
  ring

end Soma.Holonics.RH.ZeroNavigationReflection

#print axioms Soma.Holonics.RH.ZeroNavigationReflection.reflectedFiniteSurplus_re_nonneg
#print axioms Soma.Holonics.RH.ZeroNavigationReflection.rightmost_comb_normal_lower
#print axioms Soma.Holonics.RH.ZeroNavigationReflection.rightmost_local_factor_normal_lower
#print axioms Soma.Holonics.RH.ZeroNavigationReflection.rightmost_zero_velocity_normal_upper
#print axioms Soma.Holonics.RH.ZeroNavigationReflection.flowedXi_rightmost_zero_velocity_normal_upper
#print axioms Soma.Holonics.RH.ZeroNavigationReflection.reflectedQuadratic_off_seam_zero
#print axioms Soma.Holonics.RH.ZeroNavigationReflection.reflectedHeatQuadratic_discrete_heat
#print axioms Soma.Holonics.RH.ZeroNavigationReflection.reflectedHeatQuadratic_meets_on_seam
