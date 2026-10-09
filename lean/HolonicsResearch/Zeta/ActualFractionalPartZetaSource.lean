module

public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
public import Mathlib.NumberTheory.LSeries.SumCoeff
public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

@[expose] public section
set_option autoImplicit false

/-!
Actual ordinary-zeta source for the finite Beurling Mellin value.

The private source passed the whole-module v102 native gate. This is an exact source adapter, not a bound on
signed cancellation or a norm convergence port. The cached L-series
partial-sum integral is used only on Re(s)>1. The cutoff fractional-part
integral is proved holomorphic on Re(s)>0. The cached entire riemannZeta₀
then gives the identity theorem on this convex half-plane; at s=1 its
value is the Euler constant, not Mathlib's totalized ordinary zeta(1).

The boundary term s/(s-1) is retained explicitly in the ordinary-zeta
consumer, which excludes s=1. All integrals use Lebesgue volume.
-/

noncomputable section
namespace Holonics.Zeta.ActualFractionalPartZetaSource

open Set MeasureTheory Filter Asymptotics
open scoped Classical BigOperators Topology

def cutFraction (x : ℝ) : ℂ :=
  if 1 < x then ((Int.fract x : ℝ) : ℂ) else 0

def fractionMoment (s : ℂ) : ℂ := mellin cutFraction (-s)

theorem cutFraction_measurable : Measurable cutFraction :=
  Measurable.ite measurableSet_Ioi
    (Complex.measurable_ofReal.comp measurable_id.fract) measurable_const

theorem cutFraction_norm_le (x : ℝ) : ‖cutFraction x‖ ≤ 1 := by
  unfold cutFraction
  split
  · simpa only [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Int.fract_nonneg x)] using (Int.fract_lt_one x).le
  · simp

theorem cutFraction_locallyIntegrable : LocallyIntegrableOn cutFraction (Ioi 0) :=
  ((memLp_top_of_bound cutFraction_measurable.aestronglyMeasurable 1
    (Eventually.of_forall cutFraction_norm_le)).locallyIntegrable le_top).locallyIntegrableOn _

theorem cutFraction_top : cutFraction =O[atTop] (fun x : ℝ => x ^ (-(0 : ℝ))) := by
  apply IsBigO.of_bound 1
  exact Eventually.of_forall fun x => by
    simpa only [neg_zero, Real.rpow_zero, norm_one, one_mul] using cutFraction_norm_le x

theorem cutFraction_zero (b : ℝ) :
    cutFraction =O[𝓝[>] 0] (fun x : ℝ => x ^ (-b)) := by
  apply IsBigO.of_bound 1
  have hnear : ∀ᶠ x : ℝ in 𝓝[>] 0, x < 1 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hnear] with x hx
  simp only [cutFraction, if_neg (not_lt_of_ge hx.le), norm_zero, one_mul]
  exact norm_nonneg _

theorem actual_fraction_mellin_convergent {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent cutFraction (-s) := by
  apply mellinConvergent_of_isBigO_rpow (a := 0) (b := -s.re - 1)
    cutFraction_locallyIntegrable cutFraction_top
    (by simpa only [Complex.neg_re] using neg_lt_zero.mpr hs)
    (cutFraction_zero (-s.re - 1))
  simp only [Complex.neg_re]
  linarith

theorem fractionMoment_differentiableAt {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ fractionMoment s := by
  have hm : DifferentiableAt ℂ (mellin cutFraction) (-s) :=
    mellin_differentiableAt_of_isBigO_rpow (a := 0) (b := -s.re - 1)
      cutFraction_locallyIntegrable cutFraction_top
      (by simpa only [Complex.neg_re] using neg_lt_zero.mpr hs)
      (cutFraction_zero (-s.re - 1)) (by simp only [Complex.neg_re]; linarith)
  exact hm.comp s differentiableAt_id.neg

/-- The cutoff is joined to the actual Ioi(1) source integral, retaining
the ordinary fract value zero at integers. No endpoint modification is
needed here because the cutoff is also zero at x=1. -/
theorem fractionMoment_eq_integral (s : ℂ) :
    fractionMoment s =
      ∫ x : ℝ in Ioi 1, ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 1)) := by
  have hfun : (fun x : ℝ => (x : ℂ) ^ (-s - 1) * cutFraction x) =
      (Ioi (1 : ℝ)).indicator (fun x : ℝ => ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 1))) := by
    funext x
    by_cases hx : 1 < x
    · rw [Set.indicator_of_mem (s := Ioi (1 : ℝ)) (a := x)
        (show x ∈ Ioi (1 : ℝ) from hx)
        (fun y : ℝ => ((Int.fract y : ℝ) : ℂ) * (y : ℂ) ^ (-(s + 1)))]
      simp only [cutFraction, if_pos hx]
      rw [show -s - 1 = -(s + 1) by ring, mul_comm]
    · simp [cutFraction, hx]
  unfold fractionMoment mellin
  simp only [smul_eq_mul]
  rw [hfun, integral_indicator measurableSet_Ioi,
    Measure.restrict_restrict_of_subset (Ioi_subset_Ioi zero_le_one)]

theorem fractionMoment_integrable {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun x : ℝ => ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 1))) (Ioi 1) := by
  have h := (actual_fraction_mellin_convergent hs).mono_set
    (Ioi_subset_Ioi (zero_le_one : (0 : ℝ) ≤ 1))
  apply h.congr_fun ?_ measurableSet_Ioi
  intro x hx
  have hxgt : (1 : ℝ) < x := hx
  simp only [cutFraction, if_pos hxgt, smul_eq_mul]
  rw [show -s - 1 = -(s + 1) by ring, mul_comm]

/-- Actual partial sums of the constant Dirichlet coefficients give the
floor receiver. This owner is consumed only on its legal half-plane. -/
theorem actual_zeta_floor_integral {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s =
      s * ∫ x : ℝ in Ioi 1, (⌊x⌋₊ : ℂ) * (x : ℂ) ^ (-(s + 1)) := by
  have hO : (fun n : ℕ => ∑ _k ∈ Finset.Icc 1 n, (1 : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (1 : ℝ)) := by
    apply IsBigO.of_bound 1
    exact Eventually.of_forall fun n => by simp
  have h := LSeries_eq_mul_integral_of_nonneg (fun _ : ℕ => (1 : ℝ))
    (by norm_num : (0 : ℝ) ≤ 1) hs hO (fun _ => zero_le_one)
  calc
    riemannZeta s = LSeries (1 : ℕ → ℂ) s := (LSeries_one_eq_riemannZeta hs).symm
    _ = LSeries (fun _ : ℕ => (1 : ℂ)) s :=
      LSeries_congr (fun {_n} _hn => by simp) s
    _ = _ := by
      simpa only [Complex.ofReal_one, Finset.sum_const, nsmul_eq_mul, mul_one,
        Nat.card_Icc, Nat.add_sub_cancel] using h

/-- Source identity first derived on Re(s)>1. The floor splitting pays
its linear part by 1/(s-1); subtracting that pole leaves the entire
ordinary-zeta owner, rather than a supplied continuation hypothesis. -/
theorem regularized_zeta_right {s : ℂ} (hs : 1 < s.re) :
    riemannZeta₀ s = 1 - s * fractionMoment s := by
  have hs0 : 0 < s.re := zero_lt_one.trans hs
  have hsne : s ≠ 1 := by
    intro he
    rw [he] at hs
    norm_num at hs
  have hden : s - 1 ≠ 0 := sub_ne_zero.mpr hsne
  have hexp : (-s).re < -1 := by simp only [Complex.neg_re]; linarith
  have hlin := integrableOn_Ioi_cpow_of_lt hexp (c := (1 : ℝ)) zero_lt_one
  have hfrac := fractionMoment_integrable hs0
  have hlinear : (∫ x : ℝ in Ioi 1, (x : ℂ) ^ (-s)) = 1 / (s - 1) := by
    rw [integral_Ioi_cpow_of_lt hexp zero_lt_one]
    simp only [Complex.ofReal_one, Complex.one_cpow]
    rw [show -s + 1 = -(s - 1) by ring, neg_div_neg_eq]
  have hsplit : (∫ x : ℝ in Ioi 1, (⌊x⌋₊ : ℂ) * (x : ℂ) ^ (-(s + 1))) =
      1 / (s - 1) - fractionMoment s := by
    calc
      _ = ∫ x : ℝ in Ioi 1,
          ((x : ℂ) ^ (-s) - ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 1))) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        have hxpos : 0 < x := zero_lt_one.trans hx
        have hxne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hxpos.ne'
        have hfloor : (⌊x⌋₊ : ℂ) = (x : ℂ) - ((Int.fract x : ℝ) : ℂ) := by
          have hreal : (⌊x⌋₊ : ℝ) = x - Int.fract x := by
            rw [Int.fract, ← natCast_floor_eq_intCast_floor hxpos.le]
            ring
          exact_mod_cast hreal
        have hpower : (x : ℂ) * (x : ℂ) ^ (-(s + 1)) = (x : ℂ) ^ (-s) := by
          calc
            _ = (x : ℂ) ^ (1 : ℂ) * (x : ℂ) ^ (-(s + 1)) := by rw [Complex.cpow_one]
            _ = (x : ℂ) ^ (1 - (s + 1)) := (Complex.cpow_add _ _ hxne).symm
            _ = (x : ℂ) ^ (-s) := by congr 1; ring
        change (⌊x⌋₊ : ℂ) * (x : ℂ) ^ (-(s + 1)) =
          (x : ℂ) ^ (-s) - ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 1))
        rw [hfloor, sub_mul, hpower]
      _ = _ := by rw [integral_sub hlin hfrac, hlinear, fractionMoment_eq_integral]
  have hzeta := actual_zeta_floor_integral hs
  rw [hsplit] at hzeta
  calc
    riemannZeta₀ s = riemannZeta s - (s - 1)⁻¹ := by
      rw [riemannZeta_eq_inv_sub_add hsne]
      ring
    _ = 1 - s * fractionMoment s := by
      rw [hzeta, one_div]
      calc
        s * ((s - 1)⁻¹ - fractionMoment s) - (s - 1)⁻¹ =
            (s - 1) * (s - 1)⁻¹ - s * fractionMoment s := by ring
        _ = _ := by rw [mul_inv_cancel₀ hden]

/-- Actual holomorphic continuation of the pole-subtracted source. It
includes s=1 with the cached removable value riemannZeta₀(1)=gamma. -/
theorem actual_regularized_zeta_fraction {s : ℂ} (hs : 0 < s.re) :
    riemannZeta₀ s = 1 - s * fractionMoment s := by
  let U : Set ℂ := {z | 0 < z.re}
  have hopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hconvex : Convex ℝ U := (convex_Ioi (0 : ℝ)).linear_preimage Complex.reLm
  have hf : AnalyticOnNhd ℂ riemannZeta₀ U :=
    fun z _ => Differentiable.analyticAt differentiable_riemannZeta₀ z
  have hg : AnalyticOnNhd ℂ (fun z : ℂ => 1 - z * fractionMoment z) U := by
    apply DifferentiableOn.analyticOnNhd ?_ hopen
    intro z hz
    exact ((differentiableAt_const (1 : ℂ)).sub
      (differentiableAt_id.mul (fractionMoment_differentiableAt hz))).differentiableWithinAt
  have heq : EqOn riemannZeta₀ (fun z : ℂ => 1 - z * fractionMoment z) U :=
    hf.eqOn_of_preconnected_of_eventuallyEq hg hconvex.isPreconnected
      (by change (0 : ℝ) < (2 : ℂ).re; norm_num : (2 : ℂ) ∈ U)
      (eventuallyEq_of_mem
        ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
          (by norm_num : (1 : ℝ) < (2 : ℂ).re))
        (fun z hz => regularized_zeta_right hz))
  exact heq hs

/-- Actual ordinary-zeta integral, with the linear exterior boundary
term and pole exclusion retained. No Euler series is evaluated here. -/
theorem actual_zeta_fraction_integral {s : ℂ} (hs : 0 < s.re) (hsne : s ≠ 1) :
    riemannZeta s = s / (s - 1) -
      s * ∫ x : ℝ in Ioi 1, ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 1)) := by
  have hden : s - 1 ≠ 0 := sub_ne_zero.mpr hsne
  have hcancel : (s - 1) * (s - 1)⁻¹ = 1 := mul_inv_cancel₀ hden
  rw [riemannZeta_eq_inv_sub_add hsne, actual_regularized_zeta_fraction hs,
    fractionMoment_eq_integral, div_eq_mul_inv]
  calc
    (s - 1)⁻¹ + (1 - s *
        ∫ x : ℝ in Ioi 1, ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 1))) =
        (s - 1)⁻¹ + ((s - 1) * (s - 1)⁻¹ - s *
          ∫ x : ℝ in Ioi 1, ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-(s + 1))) := by
      rw [hcancel]
    _ = _ := by ring

end Holonics.Zeta.ActualFractionalPartZetaSource

#print axioms Holonics.Zeta.ActualFractionalPartZetaSource.actual_fraction_mellin_convergent
#print axioms Holonics.Zeta.ActualFractionalPartZetaSource.actual_zeta_floor_integral
#print axioms Holonics.Zeta.ActualFractionalPartZetaSource.actual_regularized_zeta_fraction
#print axioms Holonics.Zeta.ActualFractionalPartZetaSource.actual_zeta_fraction_integral
