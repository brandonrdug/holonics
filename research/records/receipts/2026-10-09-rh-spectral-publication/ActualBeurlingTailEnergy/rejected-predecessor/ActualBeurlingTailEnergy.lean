module

public import ActualFiniteBeurlingMellinDomain
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

@[expose] public section
set_option autoImplicit false

/-!
Actual full-ray receiver energy, with its arithmetic exterior retained.

PREPARED / UNRUN: only the sole native queue may check this source.
The actual v83/v98 owners are accepted independently. No Mellin-value
consumer, norm convergence, Mertens estimate or RH hypothesis is imported.

The complete norm splits at the ACTUAL cutoff 1/N, rather than at a
convenient fixed or frequency window. Its exterior equals N * B_N^2.
N=0 is excluded from these cutoff statements. Integer/singleton endpoints
do not change Lebesgue integrals; the pointwise source owns the endpoint.
-/

noncomputable section
namespace Holonics.Zeta.ActualBeurlingTailEnergy

open Set MeasureTheory Filter
open Holonics.Zeta.ActualFiniteBeurlingReceiver

/-- The actual finite signed source's squared norm integrand. -/
def squareReceiver (N : ℕ) (x : ℝ) : ℝ := physicalResidual N x ^ 2

lemma squareReceiver_nonnegative (N : ℕ) (x : ℝ) :
    0 ≤ squareReceiver N x := sq_nonneg _

lemma squareReceiver_exterior {N : ℕ} (hN : 0 < N) {x : ℝ}
    (hx : 1 / (N : ℝ) < x) :
    squareReceiver N x = harmonicMobius N ^ 2 * x ^ (-2 : ℝ) := by
  rw [squareReceiver, actual_nb_tail_pointwise hN hx.le, div_pow]
  simp only [Real.rpow_neg, Real.rpow_two, div_eq_mul_inv]

theorem actual_tail_square_integrable {N : ℕ} (hN : 0 < N) :
    IntegrableOn (squareReceiver N) (Ioi (1 / (N : ℝ))) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have ha : 0 < 1 / (N : ℝ) := one_div_pos.mpr hNr
  have hi : IntegrableOn (fun x : ℝ => x ^ (-2 : ℝ))
      (Ioi (1 / (N : ℝ))) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) ha
  apply (hi.const_mul (harmonicMobius N ^ 2)).congr_fun
    (fun x hx => (squareReceiver_exterior hN hx).symm) measurableSet_Ioi

/-- Exact exterior energy of the actual ordinary-Mobius current. -/
theorem actual_tail_square_integral {N : ℕ} (hN : 0 < N) :
    (∫ x : ℝ in Ioi (1 / (N : ℝ)), squareReceiver N x) =
      (N : ℝ) * harmonicMobius N ^ 2 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have ha : 0 < 1 / (N : ℝ) := one_div_pos.mpr hNr
  have hp : (∫ x : ℝ in Ioi (1 / (N : ℝ)), x ^ (-2 : ℝ)) = (N : ℝ) := by
    have h := integral_Ioi_rpow_of_lt (a := (-2 : ℝ)) (by norm_num) ha
    norm_num [Real.rpow_neg_one] at h
    exact h
  calc
    _ = ∫ x : ℝ in Ioi (1 / (N : ℝ)),
        harmonicMobius N ^ 2 * x ^ (-2 : ℝ) :=
      setIntegral_congr_fun measurableSet_Ioi fun x hx => squareReceiver_exterior hN hx
    _ = harmonicMobius N ^ 2 *
        (∫ x : ℝ in Ioi (1 / (N : ℝ)), x ^ (-2 : ℝ)) := integral_const_mul _ _
    _ = _ := by rw [hp]; ring

lemma actual_interior_square_integrable {N : ℕ} (hN : 0 < N) :
    IntegrableOn (squareReceiver N) (Ioc (0 : ℝ) (1 / (N : ℝ))) := by
  have hc : IntegrableOn (fun _x : ℝ => ((N : ℝ) + 1) ^ 2)
      (Ioc (0 : ℝ) (1 / (N : ℝ))) := integrableOn_const
  have hm : Measurable (squareReceiver N) := (physicalResidual_measurable N).pow_const 2
  apply hc.mono' hm.aestronglyMeasurable
  apply (ae_restrict_iff' measurableSet_Ioc).mpr
  exact Eventually.of_forall fun x _hx => by
    rw [squareReceiver, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hb := physicalResidual_abs_le N x
    have h0 := abs_nonneg (physicalResidual N x)
    have he := sq_abs (physicalResidual N x)
    nlinarith

/-- Both ends of the full physical ray are paid for this actual finite source. -/
theorem actual_full_square_integrable {N : ℕ} (hN : 0 < N) :
    IntegrableOn (squareReceiver N) (Ioi (0 : ℝ)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have ha : 0 ≤ 1 / (N : ℝ) := (one_div_pos.mpr hNr).le
  have h := (actual_interior_square_integrable hN).union
    (actual_tail_square_integrable hN)
  rwa [Ioc_union_Ioi_eq_Ioi ha] at h

/-- Complete geometric receiver: interior plus the opposite exterior return. -/
theorem actual_full_energy_balance {N : ℕ} (hN : 0 < N) :
    (∫ x : ℝ in Ioi (0 : ℝ), squareReceiver N x) =
      (∫ x : ℝ in Ioc (0 : ℝ) (1 / (N : ℝ)), squareReceiver N x) +
        (N : ℝ) * harmonicMobius N ^ 2 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have ha : 0 ≤ 1 / (N : ℝ) := (one_div_pos.mpr hNr).le
  have h := setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
    (actual_interior_square_integrable hN) (actual_tail_square_integrable hN)
  rw [Ioc_union_Ioi_eq_Ioi ha, actual_tail_square_integral hN] at h
  exact h

/-- Omitting the exterior would lose a nonnegative arithmetic contribution. -/
theorem actual_tail_energy_le_full {N : ℕ} (hN : 0 < N) :
    (N : ℝ) * harmonicMobius N ^ 2 ≤
      ∫ x : ℝ in Ioi (0 : ℝ), squareReceiver N x := by
  rw [actual_full_energy_balance hN]
  have h : 0 ≤ ∫ x : ℝ in Ioc (0 : ℝ) (1 / (N : ℝ)), squareReceiver N x :=
    integral_nonneg (squareReceiver_nonnegative N)
  linarith

end Holonics.Zeta.ActualBeurlingTailEnergy

#print axioms Holonics.Zeta.ActualBeurlingTailEnergy.actual_tail_square_integral
#print axioms Holonics.Zeta.ActualBeurlingTailEnergy.actual_full_square_integrable
#print axioms Holonics.Zeta.ActualBeurlingTailEnergy.actual_full_energy_balance
#print axioms Holonics.Zeta.ActualBeurlingTailEnergy.actual_tail_energy_le_full
