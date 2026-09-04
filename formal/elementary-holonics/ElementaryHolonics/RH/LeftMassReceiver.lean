import ElementaryHolonics.RH.ZeroCountParity

/-!
# The left mass is the exact receiver of the Riemann Hypothesis on a centred disc

On the centred disc `closedBall ½ R` the multiplicity-weighted mass of the zeros of `ξ` strictly
left of the critical line vanishes exactly when every zero of `ξ` in the disc lies on the line.
Equivalently, the disc mass equals the on-line mass.  Only the reflection symmetry and the
nonnegativity of the divisor of an entire function are used.
-/

noncomputable section

namespace Soma.Holonics.RH.LeftMassReceiver

open Soma.Holonics.RH.RiemannXi
open Soma.Holonics.RH.ZeroComb
open Soma.Holonics.RH.XiConjugation
open Soma.Holonics.RH.ZeroCountParity
open Soma.Holonics.RH.RiemannXi
open Complex Metric

/-- Inside a centred disc of any radius the divisor of `ξ` is nonzero exactly at the zeros. -/
theorem centredDivisor_ne_zero_iff (R : ℝ) (u : ℂ) :
    centredDivisor R u ≠ 0 ↔ u ∈ closedBall (1 / 2 : ℂ) R ∧ riemannXi u = 0 := by
  constructor
  · intro h
    refine ⟨(MeromorphicOn.divisor riemannXi _).supportWithinDomain (Function.mem_support.mpr h),
      ?_⟩
    by_contra hz
    apply h
    have hmem : u ∈ closedBall (1 / 2 : ℂ) R :=
      (MeromorphicOn.divisor riemannXi _).supportWithinDomain (Function.mem_support.mpr h)
    show MeromorphicOn.divisor riemannXi (closedBall (1 / 2 : ℂ) R) u = 0
    rw [MeromorphicOn.divisor_apply (meromorphicOn_riemannXi _) hmem]
    have han : AnalyticAt ℂ riemannXi u := analyticOn_riemannXi Set.univ u (Set.mem_univ u)
    rw [han.meromorphicOrderAt_eq, analyticOrderAt_eq_zero.mpr (Or.inr hz)]
    rfl
  · rintro ⟨hmem, hzero⟩
    show MeromorphicOn.divisor riemannXi (closedBall (1 / 2 : ℂ) R) u ≠ 0
    rw [MeromorphicOn.divisor_apply (meromorphicOn_riemannXi _) hmem]
    have han : AnalyticAt ℂ riemannXi u := analyticOn_riemannXi Set.univ u (Set.mem_univ u)
    have hne : analyticOrderAt riemannXi u ≠ 0 := analyticOrderAt_ne_zero.mpr ⟨han, hzero⟩
    have htop : meromorphicOrderAt riemannXi u ≠ ⊤ :=
      Soma.Holonics.RH.WeightedArgumentPrinciple.meromorphicOrderAt_riemannXi_ne_top u
    rw [han.meromorphicOrderAt_eq] at htop ⊢
    cases hn : analyticOrderAt riemannXi u with
    | top => exact absurd (by rw [hn]; rfl) htop
    | coe n =>
      rw [hn] at hne
      have hn0 : n ≠ 0 := by
        rintro rfl
        exact hne rfl
      simp [hn0]

theorem centredDivisor_nonneg (R : ℝ) (u : ℂ) : 0 ≤ centredDivisor R u :=
  divisor_riemannXi_nonnegative (closedBall (1 / 2 : ℂ) R) u

theorem leftMass_nonneg (R : ℝ) : 0 ≤ leftMass R := by
  classical
  unfold leftMass
  exact Finset.sum_nonneg (fun u _ => centredDivisor_nonneg R u)

/-- **RH on the disc.** Every zero of `ξ` in the centred disc lies on the critical line. -/
def RiemannHypothesisOn (R : ℝ) : Prop :=
  ∀ u ∈ closedBall (1 / 2 : ℂ) R, riemannXi u = 0 → u.re = 1 / 2

/-- **The left mass is the receiver of RH on the disc.** -/
theorem leftMass_eq_zero_iff (R : ℝ) : leftMass R = 0 ↔ RiemannHypothesisOn R := by
  classical
  unfold leftMass RiemannHypothesisOn
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun u _ => centredDivisor_nonneg R u)]
  constructor
  · intro h u hu hz
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hD : centredDivisor R u ≠ 0 := (centredDivisor_ne_zero_iff R u).mpr ⟨hu, hz⟩
      exact hD (h u (Finset.mem_filter.mpr ⟨mem_centredSupport.mpr hD, hlt⟩))
    · have hu' : 1 - u ∈ closedBall (1 / 2 : ℂ) R := (one_sub_mem_closedBall_half_iff u).mpr hu
      have hz' : riemannXi (1 - u) = 0 := (zeroOrbit hz).1
      have hD : centredDivisor R (1 - u) ≠ 0 :=
        (centredDivisor_ne_zero_iff R (1 - u)).mpr ⟨hu', hz'⟩
      have hlt : (1 - u).re < 1 / 2 := by
        simp only [Complex.sub_re, Complex.one_re]
        linarith
      exact hD (h (1 - u) (Finset.mem_filter.mpr ⟨mem_centredSupport.mpr hD, hlt⟩))
  · intro h u hu
    rw [Finset.mem_filter] at hu
    obtain ⟨hs, hlt⟩ := hu
    have hD := mem_centredSupport.mp hs
    obtain ⟨hmem, hz⟩ := (centredDivisor_ne_zero_iff R u).mp hD
    exact absurd (h u hmem hz) (ne_of_lt hlt)

/-- **RH on the disc is the equality of the disc mass and the on-line mass.** -/
theorem divisorMass_eq_onLineMass_iff (R : ℝ) :
    divisorMass R = onLineMass R ↔ RiemannHypothesisOn R := by
  rw [← leftMass_eq_zero_iff, divisorMass_eq_two_mul_leftMass_add_onLineMass]
  constructor
  · intro h
    linarith
  · intro h
    rw [h]
    ring

theorem onLineMass_le_divisorMass (R : ℝ) : onLineMass R ≤ divisorMass R := by
  rw [divisorMass_eq_two_mul_leftMass_add_onLineMass]
  linarith [leftMass_nonneg R]

end Soma.Holonics.RH.LeftMassReceiver
