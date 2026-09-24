import HolonicsResearch.RH.GlobalWeilFinishLine
import HolonicsResearch.RH.ZeroFactorizationExists

/-!
# Cofinal zero-free xi contours

An entire nonzero source has finitely many zeros on every compact disc.
The existing zero-factorization owner supplies this finiteness explicitly.
Choose one radius in each successive real interval outside the finite
population of bad zero radii. This is a source-qualified construction of
the contour family required by GlobalWeilFinishLine; it does not prove
arithmetic positivity or a Weil separator.
-/

noncomputable section

namespace Holonics.RH.CofinalXiContoursConstructed

open Complex Metric Set
open Holonics.RH
open Holonics.RH.RiemannXi
open Holonics.RH.ZeroFactorizationExists
open Holonics.RH.LandauLemma
open Holonics.RH.ExplicitFormulaReceiver

/-- A zero-free xi circle exists between each two successive integer
radii, selected against an actual finite factorization of the source. -/
theorem exists_admissible_radius (n : ℕ) :
    ∃ r : ℝ, (n : ℝ) + 1 < r ∧ r < (n : ℝ) + 2 ∧
      AdmissibleXiContour 0 r := by
  let bigR : ℝ := 2 * ((n : ℝ) + 3)
  have hbig : 0 < bigR := by dsimp [bigR]; positivity
  have hxi0 : riemannXi 0 ≠ 0 := by
    rw [riemannXi_zero_and_one.1]
    norm_num
  let Z : ZeroFactorization riemannXi 0 bigR :=
    Classical.choice (exists_zeroFactorization differentiable_riemannXi hbig hxi0)
  let bad : Finset ℝ := Z.zeros.image (fun z => dist z 0)
  have hinfinite :
      (Ioo ((n : ℝ) + 1) ((n : ℝ) + 2)).Infinite :=
    Set.Ioo_infinite (by linarith)
  have hex : ∃ r : ℝ, r ∈ Ioo ((n : ℝ) + 1) ((n : ℝ) + 2) ∧ r ∉ bad := by
    by_contra h
    push Not at h
    have hsub : Ioo ((n : ℝ) + 1) ((n : ℝ) + 2) ⊆ (bad : Set ℝ) := by
      intro r hr
      exact h r hr
    exact hinfinite ((bad.finite_toSet).subset hsub)
  obtain ⟨r, ⟨hrlow, hrhigh⟩, hrnot⟩ := hex
  refine ⟨r, hrlow, hrhigh, ⟨by linarith, ?_⟩⟩
  intro z hzSphere hzZero
  have hradius : dist z 0 = r := hzSphere
  have hzhalf : z ∈ ball 0 (bigR / 2) := by
    change dist z 0 < bigR / 2
    rw [hradius]
    dsimp [bigR]
    linarith
  have hzfull : z ∈ ball 0 bigR := by
    exact (ball_subset_ball (by linarith [hbig])) hzhalf
  have hfactor := Z.factor z hzfull
  have hunit := Z.unit_ne z hzhalf
  have hprodZero : (∏ ρ ∈ Z.zeros, (z - ρ) ^ Z.mult ρ) = 0 := by
    have hmul : (∏ ρ ∈ Z.zeros, (z - ρ) ^ Z.mult ρ) * Z.unit z = 0 := by
      rw [← hfactor]
      exact hzZero
    exact (mul_eq_zero.mp hmul).resolve_right hunit
  have hprodNonzero : (∏ ρ ∈ Z.zeros, (z - ρ) ^ Z.mult ρ) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro ρ hρ
    apply pow_ne_zero
    apply sub_ne_zero.mpr
    intro heq
    have hbad : r ∈ bad := by
      apply Finset.mem_image.mpr
      refine ⟨ρ, hρ, ?_⟩
      simpa [heq] using hradius
    exact hrnot hbad
  exact hprodNonzero hprodZero

/-- Choose the zero-free radius in the successive rationally bounded
interval. The existence theorem, not a numerical search, supplies it. -/
noncomputable def contourRadius (n : ℕ) : ℝ :=
  Classical.choose (exists_admissible_radius n)

private theorem contourRadius_lower (n : ℕ) :
    (n : ℝ) + 1 < contourRadius n :=
  (Classical.choose_spec (exists_admissible_radius n)).1

private theorem contourRadius_upper (n : ℕ) :
    contourRadius n < (n : ℝ) + 2 :=
  (Classical.choose_spec (exists_admissible_radius n)).2.1

private theorem contourRadius_admissible (n : ℕ) :
    AdmissibleXiContour 0 (contourRadius n) :=
  (Classical.choose_spec (exists_admissible_radius n)).2.2

/-- The cofinal xi contour family required by the global Weil finish
line. Its existence is source-qualified and independent of RH. -/
noncomputable def cofinalXiContours : CofinalXiContours where
  radius := contourRadius
  radius_pos := fun n => (contourRadius_admissible n).radius_pos
  nested := by
    apply (strictMono_nat_of_lt_succ ?_).monotone
    intro n
    have hupper := contourRadius_upper n
    have hlower := contourRadius_lower (n + 1)
    push_cast at hlower
    linarith
  cofinal := by
    intro R
    obtain ⟨n, hn⟩ := exists_nat_gt R
    refine ⟨n, ?_⟩
    have hlower := contourRadius_lower n
    linarith
  admissible := contourRadius_admissible

end Holonics.RH.CofinalXiContoursConstructed

#print axioms Holonics.RH.CofinalXiContoursConstructed.exists_admissible_radius
#print axioms Holonics.RH.CofinalXiContoursConstructed.cofinalXiContours
