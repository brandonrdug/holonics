import ElementaryHolonics.RH.ZeroOrbitCount
import ElementaryHolonics.RH.RiemannXiZeroCounting

/-!
# Zero-count parity: the multiplicity-weighted count in a centred disc has the parity of the
on-line count

The reflection `s ↦ 1 − s` preserves the divisor of `ξ` on a centred disc and exchanges the left
half-plane with the right one.  Hence the multiplicity-weighted zero count in the disc is twice the
left mass plus the on-line mass, and its parity is the parity of the on-line mass.  Only the
functional-equation reflection is used; conjugation plays no part.
-/

noncomputable section

namespace Soma.Holonics.RH.ZeroCountParity

open Soma.Holonics.RH.RiemannXi
open Soma.Holonics.RH.ZeroComb
open Soma.Holonics.RH.RiemannXiZeroCounting
open Complex Metric

/-- The divisor of `ξ` on the centred disc of radius `R`. -/
abbrev centredDivisor (R : ℝ) := MeromorphicOn.divisor riemannXi (closedBall (1 / 2 : ℂ) R)

/-- The finite support of the centred divisor. -/
def centredSupport (R : ℝ) : Finset ℂ := by
  classical
  exact ((centredDivisor R).finiteSupport (isCompact_closedBall _ _)).toFinset

theorem mem_centredSupport {R : ℝ} {u : ℂ} : u ∈ centredSupport R ↔ centredDivisor R u ≠ 0 := by
  classical
  unfold centredSupport
  rw [Set.Finite.mem_toFinset, Function.mem_support]

theorem one_sub_mem_centredSupport {R : ℝ} {u : ℂ} (hu : u ∈ centredSupport R) :
    1 - u ∈ centredSupport R := by
  rw [mem_centredSupport] at hu ⊢
  show MeromorphicOn.divisor riemannXi (closedBall (1 / 2 : ℂ) R) (1 - u) ≠ 0
  rw [divisor_riemannXi_one_sub]
  exact hu

/-- The multiplicity-weighted zero count of `ξ` in the centred disc. -/
def divisorMass (R : ℝ) : ℤ := ∑ u ∈ centredSupport R, centredDivisor R u

/-- The multiplicity-weighted count of the zeros on the critical line. -/
def onLineMass (R : ℝ) : ℤ := by
  classical
  exact ∑ u ∈ (centredSupport R).filter (fun u => u.re = 1 / 2), centredDivisor R u

/-- The multiplicity-weighted count of the zeros strictly left of the line. -/
def leftMass (R : ℝ) : ℤ := by
  classical
  exact ∑ u ∈ (centredSupport R).filter (fun u => u.re < 1 / 2), centredDivisor R u

theorem finsum_eq_divisorMass (R : ℝ) : ∑ᶠ u, centredDivisor R u = divisorMass R := by
  classical
  unfold divisorMass
  apply finsum_eq_sum_of_support_subset
  intro u hu
  exact Finset.mem_coe.mpr (mem_centredSupport.mpr hu)

/-- The real-valued inner count of `RiemannXiZeroCounting` is the cast of the integer mass. -/
theorem innerRiemannXiZeroCount_eq_divisorMass_cast {R : ℝ} (hR : 0 ≤ R) :
    innerRiemannXiZeroCount (1 / 2) R = (divisorMass R : ℝ) := by
  rw [innerRiemannXiZeroCount_eq_divisorMass hR, ← finsum_eq_divisorMass]
  have h := (Int.castAddHom ℝ).map_finsum
    ((centredDivisor R).finiteSupport (isCompact_closedBall (1 / 2 : ℂ) R))
  simp only [Int.coe_castAddHom] at h
  exact h.symm

/-- **Reflection splitting.** The disc mass is twice the left mass plus the on-line mass. -/
theorem divisorMass_eq_two_mul_leftMass_add_onLineMass (R : ℝ) :
    divisorMass R = 2 * leftMass R + onLineMass R := by
  classical
  unfold divisorMass leftMass onLineMass
  set S := centredSupport R with hS
  set D := centredDivisor R with hD
  have h1 : ∑ u ∈ S, D u =
      ∑ u ∈ S.filter (fun u => u.re = 1 / 2), D u +
        ∑ u ∈ S.filter (fun u => ¬ u.re = 1 / 2), D u :=
    (Finset.sum_filter_add_sum_filter_not S _ _).symm
  have h2 : ∑ u ∈ S.filter (fun u => ¬ u.re = 1 / 2), D u =
      ∑ u ∈ S.filter (fun u => u.re < 1 / 2), D u +
        ∑ u ∈ S.filter (fun u => 1 / 2 < u.re), D u := by
    rw [← Finset.sum_filter_add_sum_filter_not (S.filter (fun u => ¬ u.re = 1 / 2))
      (fun u => u.re < 1 / 2)]
    congr 1
    · congr 1
      ext u
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨⟨hu, _⟩, hlt⟩
        exact ⟨hu, hlt⟩
      · rintro ⟨hu, hlt⟩
        exact ⟨⟨hu, ne_of_lt hlt⟩, hlt⟩
    · congr 1
      ext u
      simp only [Finset.mem_filter, not_lt]
      constructor
      · rintro ⟨⟨hu, hne⟩, hle⟩
        exact ⟨hu, lt_of_le_of_ne hle (Ne.symm hne)⟩
      · rintro ⟨hu, hlt⟩
        exact ⟨⟨hu, ne_of_gt hlt⟩, le_of_lt hlt⟩
  have h3 : ∑ u ∈ S.filter (fun u => 1 / 2 < u.re), D u =
      ∑ u ∈ S.filter (fun u => u.re < 1 / 2), D u := by
    have himg : S.filter (fun u => 1 / 2 < u.re) =
        (S.filter (fun u => u.re < 1 / 2)).image (fun u => 1 - u) := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨hu, hlt⟩
        refine ⟨1 - u, ⟨one_sub_mem_centredSupport hu, ?_⟩, by ring⟩
        simp only [Complex.sub_re, Complex.one_re]
        linarith
      · rintro ⟨t, ⟨ht, hlt⟩, rfl⟩
        refine ⟨one_sub_mem_centredSupport ht, ?_⟩
        simp only [Complex.sub_re, Complex.one_re]
        linarith
    rw [himg, Finset.sum_image (fun a _ b _ h => by simpa using h)]
    apply Finset.sum_congr rfl
    intro u _
    exact divisor_riemannXi_one_sub u
  rw [h1, h2, h3]
  ring

/-- **Zero-count parity.** The multiplicity-weighted count in a centred disc has the parity of
the on-line count. -/
theorem divisorMass_emod_two (R : ℝ) : divisorMass R % 2 = onLineMass R % 2 := by
  rw [divisorMass_eq_two_mul_leftMass_add_onLineMass]
  omega

end Soma.Holonics.RH.ZeroCountParity
