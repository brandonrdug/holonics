import ElementaryHolonics.Millennium.LandenFlow
import ElementaryHolonics.Millennium.ThetaQuartic
import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import Mathlib.Tactic

/-!
# ThetaReflection: the plain leg reflects at the scale fixed point

**The reflection instrument of the ledger arc.**  The plain theta leg satisfies

* **`theThetaLegReflects`** — `θ₃(1/t) = √t · θ₃(t)` for `t > 0`:

the real face of Jacobi's modular transformation, carried through the bridge
`θ₃(t) = jacobiTheta(it)` and mathlib's `jacobiTheta_S_smul`.  With the doubling
flow this pins the scale fixed point `t = 1`, where the lemniscatic values live.
Every `theorem` is discharged and none depends on `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.Millennium.ThetaReflection

open Complex Real
open scoped UpperHalfPlane
open Soma.Holonics.Millennium.LandenLattice

/-- The bridge: the real leg is the Jacobi theta on the imaginary axis. -/
theorem theRealLegIsTheJacobiTheta {t : ℝ} (ht : 0 < t) :
    ((T3 t : ℝ) : ℂ) = jacobiTheta (I * t) := by
  rw [jacobiTheta, T3]
  have hterm : ∀ n : ℤ, cexp (π * I * (n : ℂ) ^ 2 * (I * t))
      = ((rexp (-π * (n : ℝ) ^ 2 * t) : ℝ) : ℂ) := by
    intro n
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    rw [show (π : ℂ) * I * (n : ℂ) ^ 2 * (I * t) = (I * I) * π * (n : ℂ) ^ 2 * t from
      by ring, Complex.I_mul_I]
    ring
  rw [show (fun n : ℤ => cexp (π * I * (n : ℂ) ^ 2 * (I * t)))
      = (fun n : ℤ => ((rexp (-π * (n : ℝ) ^ 2 * t) : ℝ) : ℂ)) from
    funext hterm]
  exact (Complex.ofReal_tsum _).symm ▸ rfl

/-- **THE PLAIN LEG REFLECTS**: `θ₃(1/t) = √t · θ₃(t)` for `t > 0` — the real face
of the modular transformation, the reflection whose fixed point is the lemniscatic
scale. -/
theorem theThetaLegReflects {t : ℝ} (ht : 0 < t) :
    T3 (1 / t) = Real.sqrt t * T3 t := by
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  -- the upper-half-plane point `it`
  set τ : ℍ := ⟨I * t, by simpa using ht⟩ with hτ
  have hS := jacobiTheta_S_smul τ
  have hcoe : ((ModularGroup.S • τ : ℍ) : ℂ) = I * (1 / t : ℝ) := by
    rw [UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk]
    have hτc : ((τ : ℍ) : ℂ) = I * (t : ℂ) := rfl
    rw [hτc]
    have hmul : (-(I * (t : ℂ))) * (I * ((1 : ℂ) / t)) = 1 := by
      rw [show (-(I * (t : ℂ))) * (I * ((1 : ℂ) / t)) = -(I * I) * (t / t) from by
        ring, Complex.I_mul_I, div_self htC]
      ring
    rw [inv_eq_of_mul_eq_one_right hmul]
    push_cast
    ring
  have hfac : (-I * (τ : ℂ)) ^ (1 / 2 : ℂ) = ((Real.sqrt t : ℝ) : ℂ) := by
    have h1 : -I * (τ : ℂ) = (t : ℂ) := by
      show -I * (I * (t : ℂ)) = (t : ℂ)
      rw [show -I * (I * (t : ℂ)) = -(I * I) * t from by ring, Complex.I_mul_I]
      ring
    rw [h1, show ((1 : ℂ) / 2) = (((1 / 2 : ℝ)) : ℂ) from by norm_num,
      ← Complex.ofReal_cpow ht.le]
    norm_cast
    rw [Real.sqrt_eq_rpow]
  have hL : ((T3 (1 / t) : ℝ) : ℂ) = jacobiTheta ((ModularGroup.S • τ : ℍ) : ℂ) := by
    rw [hcoe]
    exact theRealLegIsTheJacobiTheta (by positivity)
  have hR : jacobiTheta ((τ : ℍ) : ℂ) = ((T3 t : ℝ) : ℂ) :=
    (theRealLegIsTheJacobiTheta ht).symm
  have hmain : ((T3 (1 / t) : ℝ) : ℂ) = ((Real.sqrt t : ℝ) : ℂ) * ((T3 t : ℝ) : ℂ) := by
    rw [hL, hS, hfac, hR]
  exact_mod_cast hmain

/-! ## The shifted legs reflect into each other -/

private lemma jacobiTheta₂_even (z τ : ℂ) : jacobiTheta₂ (-z) τ = jacobiTheta₂ z τ := by
  unfold jacobiTheta₂
  rw [← (Equiv.neg ℤ).tsum_eq (fun n => jacobiTheta₂_term n z τ)]
  refine tsum_congr fun n => ?_
  unfold jacobiTheta₂_term
  simp only [Equiv.neg_apply]
  congr 1
  push_cast
  ring

private lemma T4_bridge (t : ℝ) :
    ((T4 t : ℝ) : ℂ) = jacobiTheta₂ (1 / 2) (I * t) := by
  rw [jacobiTheta₂, T4]
  have hterm : ∀ n : ℤ, jacobiTheta₂_term n (1 / 2) (I * t)
      = ((((-1 : ℝ)) ^ n * rexp (-π * (n : ℝ) ^ 2 * t) : ℝ) : ℂ) := by
    intro n
    unfold jacobiTheta₂_term
    rw [show (2 * (π : ℂ) * I * n * (1 / 2) + π * I * n ^ 2 * (I * t))
        = ((n : ℂ) * (π * I)) + (((-π * (n : ℝ) ^ 2 * t : ℝ) : ℂ)) from by
      push_cast
      rw [show (π : ℂ) * I * (n : ℂ) ^ 2 * (I * t)
          = (I * I) * (π * (n : ℂ) ^ 2 * t) from by ring, Complex.I_mul_I]
      ring]
    rw [Complex.exp_add, Complex.exp_int_mul, Complex.exp_pi_mul_I]
    push_cast
    ring
  rw [show (fun n : ℤ => jacobiTheta₂_term n (1 / 2) (I * (t : ℂ)))
      = fun n : ℤ => ((((-1 : ℝ)) ^ n * rexp (-π * (n : ℝ) ^ 2 * t) : ℝ) : ℂ) from
    funext hterm]
  exact (Complex.ofReal_tsum _).symm ▸ rfl

private lemma T2_bridge (t : ℝ) :
    ((T2 t : ℝ) : ℂ)
      = cexp (-(π : ℂ) * t / 4) * jacobiTheta₂ (I * t / 2) (I * t) := by
  rw [jacobiTheta₂, ← tsum_mul_left, T2]
  have hterm : ∀ n : ℤ,
      cexp (-(π : ℂ) * t / 4) * jacobiTheta₂_term n (I * t / 2) (I * t)
      = ((rexp (-π * ((n : ℝ) + 1 / 2) ^ 2 * t) : ℝ) : ℂ) := by
    intro n
    unfold jacobiTheta₂_term
    rw [← Complex.exp_add, Complex.ofReal_exp]
    congr 1
    rw [show (2 * (π : ℂ) * I * n * (I * t / 2) + π * I * n ^ 2 * (I * t))
        = (I * I) * (π * (n : ℂ) * t) + (I * I) * (π * (n : ℂ) ^ 2 * t) from by ring,
      Complex.I_mul_I]
    push_cast
    ring
  rw [show (fun n : ℤ => cexp (-(π : ℂ) * t / 4) *
      jacobiTheta₂_term n (I * (t : ℂ) / 2) (I * t))
      = fun n : ℤ => ((rexp (-π * ((n : ℝ) + 1 / 2) ^ 2 * t) : ℝ) : ℂ) from
    funext hterm]
  exact (Complex.ofReal_tsum _).symm ▸ rfl

set_option maxHeartbeats 1000000 in
/-- **THE SHIFTED LEGS REFLECT INTO EACH OTHER**: `θ₂(1/t) = √t · θ₄(t)` for
`t > 0` — the two-variable functional equation at the half characteristic.  At the
fixed point `t = 1` the two outer legs agree, and Jacobi's quartic then forces
`θ₃⁴ = 2θ₄⁴`: the `√2` of the lemniscatic mean. -/
theorem theShiftedLegReflects {t : ℝ} (ht : 0 < t) :
    T2 (1 / t) = Real.sqrt t * T4 t := by
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hτ0 : I * (t : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero htC
  have hFE := jacobiTheta₂_functional_equation (1 / 2) (I * t)
  -- the three transported arguments
  have harg1 : (-1 : ℂ) / (I * t) = I * ((1 / t : ℝ) : ℂ) := by
    rw [div_eq_iff hτ0]
    push_cast
    rw [show I * ((1 : ℂ) / t) * (I * t) = (I * I) * (t / t) from by ring,
      Complex.I_mul_I, div_self htC]
    ring
  have harg2 : ((1 : ℂ) / 2) / (I * t) = -(I * ((1 / (2 * t) : ℝ) : ℂ)) := by
    rw [div_eq_iff hτ0]
    push_cast
    rw [show -(I * ((1 : ℂ) / (2 * t))) * (I * t) = -(I * I) * (t / (2 * t)) from by
      ring, Complex.I_mul_I]
    rw [show ((t : ℂ)) / (2 * t) = 1 / 2 from by
      rw [eq_div_iff (by norm_num : (2 : ℂ) ≠ 0)]
      field_simp]
    ring
  have hzhalf : I * (((1 / t : ℝ)) : ℂ) / 2 = I * ((1 / (2 * t) : ℝ) : ℂ) := by
    push_cast
    ring
  have hfac : (1 : ℂ) / (-I * (I * t)) ^ (1 / 2 : ℂ)
      = ((1 / Real.sqrt t : ℝ) : ℂ) := by
    rw [show -I * (I * (t : ℂ)) = (t : ℂ) from by
      rw [show -I * (I * (t : ℂ)) = -(I * I) * t from by ring, Complex.I_mul_I]
      ring]
    rw [show ((1 : ℂ) / 2) = (((1 / 2 : ℝ)) : ℂ) from by norm_num,
      ← Complex.ofReal_cpow ht.le]
    rw [show ((1 / Real.sqrt t : ℝ) : ℂ) = 1 / ((Real.sqrt t : ℝ) : ℂ) from by
      push_cast
      ring]
    congr 2
    rw [Real.sqrt_eq_rpow]
  have hexp : cexp (-(π : ℂ) * I * (1 / 2) ^ 2 / (I * t))
      = cexp ((π : ℂ) * ((1 / t : ℝ) : ℂ) / 4 * (-1)) := by
    congr 1
    rw [div_eq_iff hτ0]
    push_cast
    rw [show (π : ℂ) * (1 / t) / 4 * (-1) * (I * t) = -(π * I * (t / t) / 4) from by
      ring, div_self htC]
    ring
  -- the inverse bridge at `1/t`
  have hJ2 : jacobiTheta₂ (I * ((1 / (2 * t) : ℝ) : ℂ)) (I * ((1 / t : ℝ) : ℂ))
      = cexp ((π : ℂ) * ((1 / t : ℝ) : ℂ) / 4) * ((T2 (1 / t) : ℝ) : ℂ) := by
    have hb := T2_bridge (1 / t)
    rw [hzhalf] at hb
    rw [hb, ← mul_assoc, ← Complex.exp_add,
      show ((π : ℂ) * ((1 / t : ℝ) : ℂ) / 4 + -(π : ℂ) * ((1 / t : ℝ)) / 4) = 0 from
        by push_cast; ring,
      Complex.exp_zero, one_mul]
  -- assemble
  have hmain : ((T4 t : ℝ) : ℂ)
      = ((1 / Real.sqrt t : ℝ) : ℂ) * ((T2 (1 / t) : ℝ) : ℂ) := by
    rw [T4_bridge t, hFE, harg1, harg2, jacobiTheta₂_even, hfac, hexp, hJ2]
    rw [show ((1 / Real.sqrt t : ℝ) : ℂ) * cexp ((π : ℂ) * ((1 / t : ℝ) : ℂ) / 4 * (-1)) *
        (cexp ((π : ℂ) * ((1 / t : ℝ) : ℂ) / 4) * ((T2 (1 / t) : ℝ) : ℂ))
        = ((1 / Real.sqrt t : ℝ) : ℂ) *
          cexp ((π : ℂ) * ((1 / t : ℝ) : ℂ) / 4 * (-1) + (π : ℂ) * ((1 / t : ℝ) : ℂ) / 4) *
          ((T2 (1 / t) : ℝ) : ℂ) from by rw [Complex.exp_add]; ring,
      show ((π : ℂ) * ((1 / t : ℝ) : ℂ) / 4 * (-1) + (π : ℂ) * ((1 / t : ℝ) : ℂ) / 4) = 0
        from by ring,
      Complex.exp_zero, mul_one]
  have hs0 : Real.sqrt t ≠ 0 := Real.sqrt_ne_zero'.mpr ht
  have hreal : T4 t = (1 / Real.sqrt t) * T2 (1 / t) := by exact_mod_cast hmain
  rw [hreal, ← mul_assoc, mul_one_div, div_self hs0, one_mul]

/-- **THE LEMNISCATIC POINT**: at the reflection fixed point the two outer legs
agree, and Jacobi's quartic forces `θ₃⁴ = 2·θ₄⁴` — the `√2` of the
arithmetic–geometric mean, exactly where the lemniscatic period lives. -/
theorem theLemniscaticPoint : T2 1 = T4 1 ∧ T3 1 ^ 4 = 2 * T4 1 ^ 4 := by
  have h1 := theShiftedLegReflects (t := 1) one_pos
  rw [show (1 : ℝ) / 1 = 1 from by norm_num, Real.sqrt_one, one_mul] at h1
  have h2 := ThetaQuartic.theJacobiQuartic (t := 1) one_pos
  refine ⟨h1, ?_⟩
  rw [h1] at h2
  linarith

end Soma.Holonics.Millennium.ThetaReflection
