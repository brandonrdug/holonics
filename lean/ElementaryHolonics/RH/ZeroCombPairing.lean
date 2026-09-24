import ElementaryHolonics.RH.ZeroComb

/-!
# The reflection pairing of the off-line cross term and real-symmetric squares

On the centred discs the xi divisor is reflection symmetric, so the off-line cross term is a sum
over reflection pairs `{ρ, 1 − ρ}`, each paying `m_ρ (ĥ(ρ) + ĥ(1 − ρ))/2`.  For a real-symmetric
square, `conj (G (conj s)) = G s` (the spectral kernel of a real test function), the kernel is
`ĥ(s) = G(s) G(1 − s)`, reflection invariant, and the cross term is `Σ_{off} m_ρ G(ρ) G(1 − ρ)`.
-/

noncomputable section

namespace Soma.Holonics.RH.ZeroCombPairing

open Soma.Holonics.RH.ExplicitFormulaReceiver
open Soma.Holonics.RH.RiemannXi
open Soma.Holonics.RH.WeilPositivity
open Soma.Holonics.RH.ZeroComb
open Complex Metric

variable {T : WeilTestFunction}

/-! ## Real-symmetric squares -/

/-- A real-symmetric Weil square: `G` commutes with conjugation. -/
structure RealWeilSquare (T : WeilTestFunction) extends WeilSquare T where
  real : ∀ s, (starRingEnd ℂ) (G ((starRingEnd ℂ) s)) = G s

/-- **The kernel of a real-symmetric square is `G(s) G(1 − s)`.** -/
theorem RealWeilSquare.spectralKernel_eq (W : RealWeilSquare T) (s : ℂ) :
    T.spectralKernel s = W.G s * W.G (1 - s) := by
  rw [W.square s]
  congr 1
  have : (1 : ℂ) - (starRingEnd ℂ) s = (starRingEnd ℂ) (1 - s) := by
    rw [map_sub, map_one]
  rw [this, W.real]

/-- **The kernel of a real-symmetric square is reflection invariant.** -/
theorem RealWeilSquare.spectralKernel_one_sub (W : RealWeilSquare T) (s : ℂ) :
    T.spectralKernel (1 - s) = T.spectralKernel s := by
  rw [W.spectralKernel_eq, W.spectralKernel_eq, sub_sub_cancel, mul_comm]

/-- **For a real-symmetric square the cross term is `Σ_{off} m_ρ G(ρ) G(1 − ρ)`.** -/
theorem offLineCross_eq_of_real (W : RealWeilSquare T) (c : ℂ) (R : ℝ) :
    offLineCross T c R = ∑ᶠ u, if u.re = 1 / 2 then 0 else
      (MeromorphicOn.divisor riemannXi (closedBall c |R|) u : ℂ) * (W.G u * W.G (1 - u)) := by
  unfold offLineCross
  refine finsum_congr fun u ↦ ?_
  rw [W.spectralKernel_eq]

/-! ## The reflection pairing on centred discs -/

theorem one_sub_re_eq_half_iff (u : ℂ) : (1 - u).re = 1 / 2 ↔ u.re = 1 / 2 := by
  simp only [Complex.sub_re, Complex.one_re]
  constructor <;> intro h <;> linarith

/-- **The off-line cross term on a centred disc equals its reflection.** -/
theorem offLineCross_eq_reflected (T : WeilTestFunction) (R : ℝ) :
    offLineCross T (1 / 2) R = ∑ᶠ u, if u.re = 1 / 2 then 0 else
      (MeromorphicOn.divisor riemannXi (closedBall (1 / 2 : ℂ) |R|) u : ℂ) *
        T.spectralKernel (1 - u) := by
  unfold offLineCross
  symm
  conv_rhs => rw [← finsum_comp_equiv (Equiv.subLeft (1 : ℂ))]
  refine finsum_congr fun a ↦ ?_
  simp only [Equiv.subLeft_apply]
  rw [divisor_riemannXi_one_sub]
  by_cases h : a.re = 1 / 2
  · rw [if_pos h, if_pos ((one_sub_re_eq_half_iff a).mpr h)]
  · rw [if_neg h, if_neg (fun h' ↦ h ((one_sub_re_eq_half_iff a).mp h'))]

/-- **The off-line cross term on a centred disc is a sum over reflection pairs.** -/
theorem offLineCross_eq_pairs (T : WeilTestFunction) (R : ℝ) :
    offLineCross T (1 / 2) R = ∑ᶠ u, if u.re = 1 / 2 then 0 else
      (MeromorphicOn.divisor riemannXi (closedBall (1 / 2 : ℂ) |R|) u : ℂ) *
        ((T.spectralKernel u + T.spectralKernel (1 - u)) / 2) := by
  classical
  set D := MeromorphicOn.divisor riemannXi (closedBall (1 / 2 : ℂ) |R|) with hD
  have hfin : D.support.Finite := D.finiteSupport (isCompact_closedBall _ _)
  have hsupp : ∀ (g : ℂ → ℂ),
      (Function.support fun u ↦ if u.re = 1 / 2 then (0 : ℂ) else (D u : ℂ) * g u) ⊆
        hfin.toFinset := by
    intro g u hu
    rw [Function.mem_support] at hu
    apply hfin.mem_toFinset.mpr
    rw [Function.mem_support]
    intro h
    apply hu
    rw [h]
    simp
  have h1 := offLineCross_eq_reflected T R
  have h0 : offLineCross T (1 / 2) R = ∑ᶠ u, if u.re = 1 / 2 then (0 : ℂ) else
      (D u : ℂ) * T.spectralKernel u := rfl
  rw [finsum_eq_sum_of_support_subset _ (hsupp fun u ↦ (T.spectralKernel u + T.spectralKernel (1 - u)) / 2)]
  rw [finsum_eq_sum_of_support_subset _ (hsupp fun u ↦ T.spectralKernel (1 - u))] at h1
  rw [finsum_eq_sum_of_support_subset _ (hsupp fun u ↦ T.spectralKernel u)] at h0
  have htwo : (2 : ℂ) * offLineCross T (1 / 2) R = offLineCross T (1 / 2) R + offLineCross T (1 / 2) R := by
    ring
  have hsum : offLineCross T (1 / 2) R + offLineCross T (1 / 2) R =
      ∑ u ∈ hfin.toFinset, (if u.re = 1 / 2 then (0 : ℂ) else
        (D u : ℂ) * (T.spectralKernel u + T.spectralKernel (1 - u))) := by
    calc offLineCross T (1 / 2) R + offLineCross T (1 / 2) R
        = (∑ u ∈ hfin.toFinset, (if u.re = 1 / 2 then (0 : ℂ) else
            (D u : ℂ) * T.spectralKernel u)) +
          ∑ u ∈ hfin.toFinset, (if u.re = 1 / 2 then (0 : ℂ) else
            (D u : ℂ) * T.spectralKernel (1 - u)) := by rw [← h0, ← h1]
      _ = _ := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun u _ ↦ ?_
          split_ifs <;> ring
  have hhalf : offLineCross T (1 / 2) R =
      (∑ u ∈ hfin.toFinset, (if u.re = 1 / 2 then (0 : ℂ) else
        (D u : ℂ) * (T.spectralKernel u + T.spectralKernel (1 - u)))) / 2 := by
    rw [← hsum, ← htwo]
    field_simp
  rw [hhalf, Finset.sum_div]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  by_cases h : u.re = 1 / 2
  · rw [if_pos h, if_pos h, zero_div]
  · rw [if_neg h, if_neg h]
    ring

section Audit

#print axioms RealWeilSquare.spectralKernel_one_sub
#print axioms offLineCross_eq_reflected
#print axioms offLineCross_eq_pairs

end Audit

end Soma.Holonics.RH.ZeroCombPairing
