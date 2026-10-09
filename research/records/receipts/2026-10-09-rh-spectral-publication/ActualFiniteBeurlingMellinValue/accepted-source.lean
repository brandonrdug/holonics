module

public import ActualFiniteBeurlingMellinDomain
public import ActualFractionalPartZetaSource
public import Mathlib.Data.Complex.BigOperators
public import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

@[expose] public section
set_option autoImplicit false

/-!
Actual finite signed ordinary-Mobius Mellin value on the full positive ray.

PREPARED / UNRUN. The two imported private source units are whole-module
accepted at v98 and v102. Their exact source and full object receipts are
required; this consumer still needs its own native gate. V83 stays intact.

The reciprocal fractional-part integral is split at y=1. Ordinary
fract(1)=0 is retained pointwise. The cached Ioc(0,1) power formula has
value1 at that endpoint, so it is joined to the actual split only almost
everywhere with the singleton explicitly removed. The physical step
chi_(0,1] is then joined pointwise, including x=1, to actual signed finite
Mobius dilations. No infinite prime/Mobius series is used on this strip.

Measures are Lebesgue dx on the full positive ray and du on the full
logarithmic line. This exact transform value does not prove uniform norm
decay, a favorable actual zero-current sign, RH or a Lambda upper bound.
-/

noncomputable section
namespace Holonics.Zeta.ActualFiniteBeurlingMellinValue

open Set MeasureTheory Filter
open Holonics.Zeta.ActualFiniteBeurlingReceiver
open Holonics.Zeta.ActualFractionalPartZetaSource
open scoped Classical BigOperators FourierTransform

def forwardFraction (x : ℝ) : ℂ := ((Int.fract x : ℝ) : ℂ)

def reciprocalFraction (x : ℝ) : ℂ := forwardFraction x⁻¹

def physicalStep : ℝ → ℂ := (Ioc 0 1).indicator (fun _ => 1)

def signedDilation (N : ℕ) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc 0 N, (ArithmeticFunction.moebius n : ℂ) •
    reciprocalFraction ((n : ℝ) * x)

def dirichletPolynomial (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Ioc 0 N, (ArithmeticFunction.moebius n : ℂ) / (n : ℂ) ^ s

/-- The actual forward source is joined to the closed-interval cached
power source only almost everywhere. At y=1 ordinary fract is0, whereas
the Ioc power indicator is1. No pointwise equality is claimed there. -/
theorem actual_fraction_boundary_split_ae :
    forwardFraction =ᵐ[volume.restrict (Ioi 0)]
      (fun x : ℝ => (Ioc 0 1).indicator (fun y : ℝ => (y : ℂ)) x + cutFraction x) := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi,
    (volume.restrict (Ioi (0 : ℝ))).ae_ne 1] with x hx hxne
  change forwardFraction x =
    (Ioc (0 : ℝ) 1).indicator (fun y : ℝ => (y : ℂ)) x + cutFraction x
  by_cases hx1 : x < 1
  · have hmem : x ∈ Ioc (0 : ℝ) 1 := ⟨hx, hx1.le⟩
    have hfrac : Int.fract x = x := Int.fract_eq_self.mpr ⟨hx.le, hx1⟩
    rw [Set.indicator_of_mem (s := Ioc (0 : ℝ) 1) (a := x) hmem
      (fun y : ℝ => (y : ℂ))]
    simp only [forwardFraction, hfrac, cutFraction,
      if_neg (not_lt_of_ge hx1.le), add_zero]
  · have hgt : 1 < x := by
      rcases lt_or_gt_of_ne hxne with hlt | hgt
      · exact (hx1 hlt).elim
      · exact hgt
    have hnot : x ∉ Ioc (0 : ℝ) 1 := fun h => (not_le_of_gt hgt) h.2
    rw [Set.indicator_of_notMem (s := Ioc (0 : ℝ) 1) (a := x) hnot
      (fun y : ℝ => (y : ℂ))]
    simp only [forwardFraction, cutFraction, if_pos hgt, zero_add]

theorem forward_fraction_hasMellin {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    HasMellin forwardFraction (-s) (-riemannZeta s / s) := by
  have hsne0 : s ≠ 0 := Complex.ne_zero_of_re_pos hs0
  have hsne1 : s ≠ 1 := by
    intro h
    rw [h] at hs1
    norm_num at hs1
  have hsmall : HasMellin ((Ioc 0 1).indicator (fun y : ℝ => (y : ℂ)))
      (-s) (1 / (1 - s)) := by
    have h := hasMellin_cpow_Ioc (1 : ℂ) (s := -s)
      (by simp only [Complex.neg_re, Complex.one_re]; linarith)
    simpa only [Complex.cpow_one, show -s + 1 = 1 - s by ring] using h
  have hlarge := actual_fraction_mellin_convergent hs0
  have hadd := hasMellin_add hsmall.1 hlarge
  have hvalue : mellin forwardFraction (-s) = 1 / (1 - s) + fractionMoment s := by
    calc
      _ = mellin (fun x : ℝ =>
          (Ioc 0 1).indicator (fun y : ℝ => (y : ℂ)) x + cutFraction x) (-s) := by
        unfold mellin
        apply integral_congr_ae
        exact actual_fraction_boundary_split_ae.mono fun x hx =>
          congrArg (fun z : ℂ => (x : ℂ) ^ (-s - 1) • z) hx
      _ = _ := by rw [hadd.2, hsmall.2]; rfl
  refine ⟨?_, ?_⟩
  · change IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-s - 1) • forwardFraction x) (Ioi 0)
    exact hadd.1.congr (actual_fraction_boundary_split_ae.symm.mono fun x hx =>
      congrArg (fun z : ℂ => (x : ℂ) ^ (-s - 1) • z) hx)
  · rw [hvalue]
    apply (eq_div_iff hsne0).mpr
    have hzeta := actual_zeta_fraction_integral hs0 hsne1
    rw [← fractionMoment_eq_integral] at hzeta
    rw [hzeta, one_div, div_eq_mul_inv,
      show 1 - s = -(s - 1) by ring, inv_neg]
    ring

/-- The actual inverse coordinate is paid both by a convergence
equivalence and by the cached Mellin substitution. Totalized equality
alone is not used as evidence of convergence. -/
theorem actual_reciprocal_fraction_hasMellin {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    HasMellin reciprocalFraction s (-riemannZeta s / s) := by
  have h := forward_fraction_hasMellin hs0 hs1
  have hpow : MellinConvergent (fun x : ℝ => forwardFraction (x ^ (-1 : ℝ))) s := by
    apply (MellinConvergent.comp_rpow (a := (-1 : ℝ)) (by norm_num)).mpr
    simpa only [Complex.ofReal_neg, Complex.ofReal_one, div_neg, div_one] using h.1
  refine ⟨?_, ?_⟩
  · change MellinConvergent (fun x : ℝ => forwardFraction x⁻¹) s
    simpa only [Real.rpow_neg_one] using hpow
  · change mellin (fun x : ℝ => forwardFraction x⁻¹) s = _
    rw [mellin_comp_inv]
    exact h.2

/-- Actual finite source, with the physical x=1 step endpoint joined
pointwise. All arithmetic signs and every finite dilation remain. -/
theorem actual_receiver_signed_dilation (N : ℕ) {x : ℝ} (hx : 0 < x) :
    complexPhysicalResidual N x = physicalStep x + signedDilation N x := by
  have hstep : Complex.ofReal (if x ≤ 1 then (1 : ℝ) else 0) = physicalStep x := by
    by_cases hx1 : x ≤ 1
    · have hmem : x ∈ Ioc (0 : ℝ) 1 := ⟨hx, hx1⟩
      rw [physicalStep, Set.indicator_of_mem (s := Ioc (0 : ℝ) 1) (a := x) hmem
        (fun _ : ℝ => (1 : ℂ))]
      simp only [if_pos hx1, Complex.ofReal_one]
    · have hnot : x ∉ Ioc (0 : ℝ) 1 := fun h => hx1 h.2
      rw [physicalStep, Set.indicator_of_notMem (s := Ioc (0 : ℝ) 1) (a := x) hnot
        (fun _ : ℝ => (1 : ℂ))]
      simp only [if_neg hx1, Complex.ofReal_zero]
  rw [complexPhysicalResidual, actual_nb_receiver N hx, Complex.ofReal_add,
    hstep, Complex.ofReal_sum]
  congr 1
  unfold signedDilation
  apply Finset.sum_congr rfl
  intro n _
  simp only [Complex.ofReal_mul, Complex.ofReal_intCast, reciprocalFraction,
    forwardFraction, smul_eq_mul, one_div]

theorem signed_dilation_hasMellin (N : ℕ) {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    HasMellin (signedDilation N) s (dirichletPolynomial N s * (-riemannZeta s / s)) := by
  have hbase := actual_reciprocal_fraction_hasMellin hs0 hs1
  have hcomp : ∀ n ∈ Finset.Ioc 0 N,
      MellinConvergent (fun x : ℝ => (ArithmeticFunction.moebius n : ℂ) •
        reciprocalFraction ((n : ℝ) * x)) s := by
    intro n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Ioc.mp hn).1
    have hd : MellinConvergent (fun x : ℝ => reciprocalFraction ((n : ℝ) * x)) s :=
      (MellinConvergent.comp_mul_left hnpos).mpr hbase.1
    exact hd.const_smul (ArithmeticFunction.moebius n : ℂ)
  have hvalue : ∀ n ∈ Finset.Ioc 0 N,
      mellin (fun x : ℝ => (ArithmeticFunction.moebius n : ℂ) •
        reciprocalFraction ((n : ℝ) * x)) s =
          ((ArithmeticFunction.moebius n : ℂ) / (n : ℂ) ^ s) * (-riemannZeta s / s) := by
    intro n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Ioc.mp hn).1
    rw [mellin_const_smul, mellin_comp_mul_left _ _ hnpos, hbase.2]
    simp only [smul_eq_mul, Complex.ofReal_natCast, Complex.cpow_neg, div_eq_mul_inv]
    ring
  refine ⟨?_, ?_⟩
  · unfold MellinConvergent signedDilation
    simp_rw [Finset.smul_sum]
    exact integrable_finsetSum (Finset.Ioc 0 N) hcomp
  · calc
      mellin (signedDilation N) s = ∑ n ∈ Finset.Ioc 0 N,
          mellin (fun x : ℝ => (ArithmeticFunction.moebius n : ℂ) •
            reciprocalFraction ((n : ℝ) * x)) s := by
        unfold mellin signedDilation
        simp_rw [Finset.smul_sum]
        exact integral_finsetSum (Finset.Ioc 0 N) hcomp
      _ = ∑ n ∈ Finset.Ioc 0 N,
          ((ArithmeticFunction.moebius n : ℂ) / (n : ℂ) ^ s) * (-riemannZeta s / s) :=
        Finset.sum_congr rfl hvalue
      _ = _ := by rw [dirichletPolynomial, Finset.sum_mul]

/-- Actual full positive-ray source value, including N=0 (empty signed
sum and the physical indicator). No separate abstract approximation
family or hypothesized transform value appears in the proof. -/
theorem actual_finite_receiver_hasMellin (N : ℕ) {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    HasMellin (complexPhysicalResidual N) s
      ((1 - riemannZeta s * dirichletPolynomial N s) / s) := by
  have hstep : HasMellin physicalStep s (1 / s) := hasMellin_one_Ioc hs0
  have hphase := signed_dilation_hasMellin N hs0 hs1
  have hsum := hasMellin_add hstep.1 hphase.1
  have hae : complexPhysicalResidual N =ᵐ[volume.restrict (Ioi 0)]
      (fun x : ℝ => physicalStep x + signedDilation N x) :=
    (ae_restrict_mem measurableSet_Ioi).mono fun x hx => actual_receiver_signed_dilation N hx
  refine ⟨?_, ?_⟩
  · change IntegrableOn
      (fun x : ℝ => (x : ℂ) ^ (s - 1) • complexPhysicalResidual N x) (Ioi 0)
    exact hsum.1.congr (hae.symm.mono fun x hx =>
      congrArg (fun z : ℂ => (x : ℂ) ^ (s - 1) • z) hx)
  · calc
      mellin (complexPhysicalResidual N) s =
          mellin (fun x : ℝ => physicalStep x + signedDilation N x) s := by
        unfold mellin
        apply integral_congr_ae
        exact hae.mono fun x hx => congrArg (fun z : ℂ => (x : ℂ) ^ (s - 1) • z) hx
      _ = _ := by
        rw [hsum.2, hstep.2, hphase.2]
        simp only [div_eq_mul_inv]
        ring

/-- Actual transform value consumed in the logarithmic L1/L2 receiver.
The frequency convention, domains and both ends of the ray stay in this
consumer. No independent Plancherel or signed norm-decay claim follows. -/
theorem actual_finite_receiver_fourier_value {N : ℕ} (hN : 0 < N) {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    Integrable (complexLogReceiver N s.re) ∧
      MemLp (complexLogReceiver N s.re) 2 volume ∧
      𝓕 (complexLogReceiver N s.re) (s.im / (2 * Real.pi)) =
        (1 - riemannZeta s * dirichletPolynomial N s) / s := by
  have hdomain := actual_mellin_log_fourier hN hs0 hs1
  exact ⟨hdomain.2.1, hdomain.2.2.1,
    hdomain.2.2.2.symm.trans (actual_finite_receiver_hasMellin N hs0 hs1).2⟩

end Holonics.Zeta.ActualFiniteBeurlingMellinValue

#print axioms Holonics.Zeta.ActualFiniteBeurlingMellinValue.actual_fraction_boundary_split_ae
#print axioms Holonics.Zeta.ActualFiniteBeurlingMellinValue.actual_reciprocal_fraction_hasMellin
#print axioms Holonics.Zeta.ActualFiniteBeurlingMellinValue.actual_finite_receiver_hasMellin
#print axioms Holonics.Zeta.ActualFiniteBeurlingMellinValue.actual_finite_receiver_fourier_value
