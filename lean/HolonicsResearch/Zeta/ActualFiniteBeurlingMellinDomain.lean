module

public import HolonicsResearch.Zeta.ActualFiniteBeurlingReceiver
public import Mathlib.Analysis.MellinInversion
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section
set_option autoImplicit false

/-!
Actual finite ordinary-Mobius receiver: its logarithmic Mellin/Fourier domain.

The imported finite receiver is the whole-module v83 accepted source, SHA
1401be5362c873e03d4c641ca44e9b804fc79dc4ece6f3b6d00238339ed76ffc.
All measures below are Lebesgue volume. For each fixed N>0 the chart
u -> exp(-sigma*u) r_N(exp(-u)) is L1 and L2 when 0<sigma<1.
The left half-line uses the actual arithmetic exterior r_N(x)=B_N/x;
the right half-line uses ordinary fractional parts, including integers.

The private source passed the whole-module v98 native gate. The publication
receipt records its exact accepted hash and public import-path relocation.
No favorable signed bound, uniform-in-N norm decay, zeta Mellin value,
Plancherel norm equality, actual-current cancellation or RH is asserted.
This is not an Euler-series extension into the critical strip.
-/

noncomputable section
namespace Holonics.Zeta.ActualFiniteBeurlingReceiver

open Set MeasureTheory Filter Asymptotics
open scoped Classical BigOperators FourierTransform

def logReceiver (N : ℕ) (sigma u : ℝ) : ℝ :=
  Real.exp (-sigma * u) * physicalResidual N (Real.exp (-u))

def complexPhysicalResidual (N : ℕ) (x : ℝ) : ℂ :=
  (physicalResidual N x : ℂ)

def complexLogReceiver (N : ℕ) (sigma u : ℝ) : ℂ :=
  (logReceiver N sigma u : ℂ)

theorem physicalResidual_measurable (N : ℕ) : Measurable (physicalResidual N) := by
  have hstep : Measurable (fun y : ℝ => if 1 ≤ y then (1 : ℝ) else 0) :=
    Measurable.ite measurableSet_Ici measurable_const measurable_const
  have hphase : Measurable (phaseRead N) := by
    unfold phaseRead
    apply Finset.measurable_sum
    intro n _
    exact measurable_const.mul (measurable_id.div_const (n : ℝ)).fract
  exact (hstep.add hphase).comp measurable_id.inv

/-- This bound uses the actual finite arithmetic weights |mu(n)|<=1,
not a positive replacement of the signed source. It applies for all x. -/
theorem physicalResidual_abs_le (N : ℕ) (x : ℝ) :
    |physicalResidual N x| ≤ (N : ℝ) + 1 := by
  have hphase : |phaseRead N x⁻¹| ≤ (N : ℝ) := by
    unfold phaseRead
    calc
      |∑ n ∈ Finset.Ioc 0 N, (ArithmeticFunction.moebius n : ℝ) *
          Int.fract (x⁻¹ / n)|
          ≤ ∑ n ∈ Finset.Ioc 0 N, |(ArithmeticFunction.moebius n : ℝ) *
              Int.fract (x⁻¹ / n)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _n ∈ Finset.Ioc 0 N, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro n _
        have hmu : |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := by
          exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))
        rw [abs_mul, abs_of_nonneg (Int.fract_nonneg (x⁻¹ / (n : ℝ)))]
        simpa using mul_le_mul hmu (Int.fract_lt_one _).le
          (Int.fract_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
      _ = N := by simp
  have hstep : |(if 1 ≤ x⁻¹ then (1 : ℝ) else 0)| ≤ 1 := by
    split <;> norm_num
  calc
    |physicalResidual N x| ≤
        |(if 1 ≤ x⁻¹ then (1 : ℝ) else 0)| + |phaseRead N x⁻¹| := abs_add_le _ _
    _ ≤ (N : ℝ) + 1 := by linarith

theorem logReceiver_measurable (N : ℕ) (sigma : ℝ) :
    Measurable (logReceiver N sigma) := by
  exact (Real.measurable_exp.comp (measurable_const.mul measurable_id)).mul
    ((physicalResidual_measurable N).comp (Real.measurable_exp.comp measurable_id.neg))

/-- The accepted exterior is retained exactly, rather than discarded after
changing charts. There is no lower-jet vanishing or denominator hypothesis. -/
theorem actual_log_receiver_left {N : ℕ} (hN : 0 < N) (sigma : ℝ)
    {u : ℝ} (hu : u ≤ 0) :
    logReceiver N sigma u = harmonicMobius N * Real.exp ((1 - sigma) * u) := by
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (Nat.succ_le_of_lt hN)
  have hcut : 1 / (N : ℝ) ≤ 1 := by
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hNr
  have hexp : (1 : ℝ) ≤ Real.exp (-u) :=
    Real.one_le_exp_iff.mpr (neg_nonneg.mpr hu)
  have hinv : (Real.exp (-u))⁻¹ = Real.exp u := by
    rw [← Real.exp_neg]
    congr 1
    ring
  rw [logReceiver, actual_nb_tail_pointwise hN (hcut.trans hexp), div_eq_mul_inv, hinv]
  calc
    Real.exp (-sigma * u) * (harmonicMobius N * Real.exp u) =
        harmonicMobius N * (Real.exp (-sigma * u) * Real.exp u) := by ring
    _ = harmonicMobius N * Real.exp ((1 - sigma) * u) := by
      rw [← Real.exp_add]
      congr 2 <;> ring

theorem logReceiver_abs_le (N : ℕ) (sigma u : ℝ) :
    |logReceiver N sigma u| ≤ ((N : ℝ) + 1) * Real.exp (-sigma * u) := by
  rw [logReceiver, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (-sigma * u) * |physicalResidual N (Real.exp (-u))| ≤
        Real.exp (-sigma * u) * ((N : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left (physicalResidual_abs_le N _) (Real.exp_pos _).le
    _ = _ := mul_comm _ _

theorem actual_log_receiver_integrable {N : ℕ} (hN : 0 < N) {sigma : ℝ}
    (hs0 : 0 < sigma) (hs1 : sigma < 1) :
    Integrable (logReceiver N sigma) := by
  have hleft : IntegrableOn (logReceiver N sigma) (Iic 0) := by
    apply IntegrableOn.congr_fun
      ((integrableOn_exp_mul_Iic (sub_pos.mpr hs1) 0).const_mul
        (harmonicMobius N)) ?_ measurableSet_Iic
    intro u hu
    exact (actual_log_receiver_left hN sigma hu).symm
  have hright : IntegrableOn (logReceiver N sigma) (Ioi 0) := by
    apply ((integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hs0) 0).const_mul
      ((N : ℝ) + 1)).mono' (logReceiver_measurable N sigma).aestronglyMeasurable
    apply (ae_restrict_iff' measurableSet_Ioi).mpr
    exact Eventually.of_forall fun u _ => by
      simpa only [Real.norm_eq_abs] using logReceiver_abs_le N sigma u
  have hunion := integrableOn_union.mpr ⟨hleft, hright⟩
  rw [Iic_union_Ioi, integrableOn_univ] at hunion
  exact hunion

theorem actual_log_receiver_memLp_two {N : ℕ} (hN : 0 < N) {sigma : ℝ}
    (hs0 : 0 < sigma) (hs1 : sigma < 1) :
    MemLp (logReceiver N sigma) 2 volume := by
  apply (memLp_two_iff_integrable_sq
    (logReceiver_measurable N sigma).aestronglyMeasurable).mpr
  have hleft : IntegrableOn (fun u => logReceiver N sigma u ^ 2) (Iic 0) := by
    have hrate : 0 < 2 * (1 - sigma) := mul_pos (by norm_num) (sub_pos.mpr hs1)
    apply IntegrableOn.congr_fun
      ((integrableOn_exp_mul_Iic hrate 0).const_mul
        (harmonicMobius N ^ 2)) ?_ measurableSet_Iic
    intro u hu
    change harmonicMobius N ^ 2 * Real.exp (2 * (1 - sigma) * u) =
      logReceiver N sigma u ^ 2
    rw [actual_log_receiver_left hN sigma hu, mul_pow]
    congr 1
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hright : IntegrableOn (fun u => logReceiver N sigma u ^ 2) (Ioi 0) := by
    have hrate : (-2 : ℝ) * sigma < 0 := mul_neg_of_neg_of_pos (by norm_num) hs0
    apply ((integrableOn_exp_mul_Ioi hrate 0).const_mul
      (((N : ℝ) + 1) ^ 2)).mono'
        ((logReceiver_measurable N sigma).pow_const 2).aestronglyMeasurable
    apply (ae_restrict_iff' measurableSet_Ioi).mpr
    refine Eventually.of_forall fun u _ => ?_
    have hbound := pow_le_pow_left₀ (abs_nonneg (logReceiver N sigma u))
      (logReceiver_abs_le N sigma u) 2
    calc
      ‖logReceiver N sigma u ^ 2‖ = |logReceiver N sigma u| ^ 2 := by
        rw [Real.norm_eq_abs, abs_pow]
      _ ≤ (((N : ℝ) + 1) * Real.exp (-sigma * u)) ^ 2 := hbound
      _ = ((N : ℝ) + 1) ^ 2 * Real.exp ((-2 * sigma) * u) := by
        rw [mul_pow, pow_two (Real.exp _), ← Real.exp_add]
        congr 2 <;> ring
  have hunion := integrableOn_union.mpr ⟨hleft, hright⟩
  rw [Iic_union_Ioi, integrableOn_univ] at hunion
  exact hunion

/-- The actual complex logarithmic receiver lies simultaneously in L1 and
L2, for Lebesgue du. This supplies the domains of future Fourier/L2 joins,
not their norm-decay conclusion. Constants depend on this finite N. -/
theorem actual_log_receiver_l1_l2 {N : ℕ} (hN : 0 < N) {sigma : ℝ}
    (hs0 : 0 < sigma) (hs1 : sigma < 1) :
    Integrable (complexLogReceiver N sigma) ∧
      MemLp (complexLogReceiver N sigma) 2 volume := by
  exact ⟨(actual_log_receiver_integrable hN hs0 hs1).ofReal,
    (actual_log_receiver_memLp_two hN hs0 hs1).ofReal⟩

theorem norm_complexPhysicalResidual (N : ℕ) (x : ℝ) :
    ‖complexPhysicalResidual N x‖ = |physicalResidual N x| := by
  simp only [complexPhysicalResidual, Complex.norm_real, Real.norm_eq_abs]

/-- Full positive ray dx; the exponent restriction pays both ends. The
locally integrable source is proved from its actual finite bound, and
the infinity majorant is paid by the accepted Mobius exterior identity. -/
theorem actual_mellin_convergent {N : ℕ} (hN : 0 < N) {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    MellinConvergent (complexPhysicalResidual N) s := by
  have hmeas : Measurable (complexPhysicalResidual N) :=
    Complex.measurable_ofReal.comp (physicalResidual_measurable N)
  have hbound : ∀ x, ‖complexPhysicalResidual N x‖ ≤ (N : ℝ) + 1 := by
    intro x
    rw [norm_complexPhysicalResidual]
    exact physicalResidual_abs_le N x
  have htopLp : MemLp (complexPhysicalResidual N) ⊤ volume :=
    memLp_top_of_bound hmeas.aestronglyMeasurable ((N : ℝ) + 1)
      (Eventually.of_forall hbound)
  have hlocal : LocallyIntegrableOn (complexPhysicalResidual N) (Ioi 0) :=
    (htopLp.locallyIntegrable le_top).locallyIntegrableOn _
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (Nat.succ_le_of_lt hN)
  have hcut : 1 / (N : ℝ) ≤ 1 := by
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hNr
  have htop : complexPhysicalResidual N =O[atTop] (fun x : ℝ => x ^ (-(1 : ℝ))) := by
    apply IsBigO.of_bound |harmonicMobius N|
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
    rw [norm_complexPhysicalResidual, actual_nb_tail_pointwise hN (hcut.trans hx)]
    simpa only [abs_div, abs_mul, abs_of_pos hxpos, Real.rpow_neg_one, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hxpos), div_eq_mul_inv] using
        (le_rfl : |harmonicMobius N| * x⁻¹ ≤ |harmonicMobius N| * x⁻¹)
  have hbot : complexPhysicalResidual N =O[nhdsWithin (0 : ℝ) (Ioi 0)]
      (fun x : ℝ => x ^ (-(0 : ℝ))) := by
    apply IsBigO.of_bound ((N : ℝ) + 1)
    apply Eventually.of_forall
    intro x
    simpa only [neg_zero, Real.rpow_zero, norm_one, mul_one] using hbound x
  exact mellinConvergent_of_isBigO_rpow hlocal htop hs1 hbot hs0

/-- The cached Fourier convention is exp(-2*pi*i*u*v); its frequency is
Im(s)/(2*pi). Actual Mellin convergence and L1/L2 membership are retained
in the same consumer, so the equality is not an unqualified totalized
integral. The value (1-zeta(s) A_N(s))/s is still an open source adapter. -/
theorem actual_mellin_log_fourier {N : ℕ} (hN : 0 < N) {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    MellinConvergent (complexPhysicalResidual N) s ∧
      Integrable (complexLogReceiver N s.re) ∧
      MemLp (complexLogReceiver N s.re) 2 volume ∧
      mellin (complexPhysicalResidual N) s =
        𝓕 (complexLogReceiver N s.re) (s.im / (2 * Real.pi)) := by
  refine ⟨actual_mellin_convergent hN hs0 hs1,
    (actual_log_receiver_l1_l2 hN hs0 hs1).1,
    (actual_log_receiver_l1_l2 hN hs0 hs1).2, ?_⟩
  have hchart : (fun u : ℝ => Real.exp (-s.re * u) •
      complexPhysicalResidual N (Real.exp (-u))) = complexLogReceiver N s.re := by
    funext u
    change Real.exp (-s.re * u) • (physicalResidual N (Real.exp (-u)) : ℂ) =
      ((Real.exp (-s.re * u) * physicalResidual N (Real.exp (-u)) : ℝ) : ℂ)
    rw [Complex.real_smul, Complex.ofReal_mul]
  rw [← hchart]
  exact mellin_eq_fourier (complexPhysicalResidual N)

end Holonics.Zeta.ActualFiniteBeurlingReceiver

#print axioms Holonics.Zeta.ActualFiniteBeurlingReceiver.actual_log_receiver_left
#print axioms Holonics.Zeta.ActualFiniteBeurlingReceiver.actual_log_receiver_l1_l2
#print axioms Holonics.Zeta.ActualFiniteBeurlingReceiver.actual_mellin_convergent
#print axioms Holonics.Zeta.ActualFiniteBeurlingReceiver.actual_mellin_log_fourier
