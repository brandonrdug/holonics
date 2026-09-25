import Holonics.Hodge.HodgeGreenOperator

/-!
# Temporal Hodge residues

This file records the small, reusable temporal law behind a changing Hodge receiver.  A
harmonic representative is a class representative, not an assertion that the whole source is
harmonic.  A supplied evolution may fix the harmonic part while transporting the orthogonal
residue; an exact-residue hypothesis is what lets the class representative continue to be read
in the closed quotient.  No history archive or analytic matrix exponential is assumed.
-/

noncomputable section

namespace Holonics.Physics

open Holonics.Hodge.HodgeFiniteDecomposition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

open Holonics.Hodge.HodgeFiniteDecomposition.Differential

structure TemporalHodgeEvolution (D : Differential E) where
  T : E →L[ℝ] E
  fixesHarmonic : ∀ h : E, h ∈ D.harmonic → T h = h
  preservesResidue : ∀ r : E, r ∈ D.harmonicᗮ → T r ∈ D.harmonicᗮ

namespace TemporalHodgeEvolution

variable {D : Differential E} (A : TemporalHodgeEvolution D)

/-! ## An explicit finite heat step

The following is an algebraic Euler step.  No positivity of the step, contractivity, or
continuum heat interpretation is included here; those are separate stability/physical claims.
-/

def eulerHeatStep (a : ℝ) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E - a • D.laplacian

theorem eulerHeatStep_apply (a : ℝ) (x : E) :
    eulerHeatStep (D := D) a x = x - a • D.laplacian x := by
  rfl

theorem eulerHeatStep_fixes_harmonic (a : ℝ) {h : E} (hh : h ∈ D.harmonic) :
    eulerHeatStep (D := D) a h = h := by
  rw [eulerHeatStep_apply]
  have hl : D.laplacian h = 0 := LinearMap.mem_ker.mp hh
  simp [hl]

theorem eulerHeatStep_preserves_residue (a : ℝ) {r : E}
    (hr : r ∈ D.harmonicᗮ) : eulerHeatStep (D := D) a r ∈ D.harmonicᗮ := by
  rw [eulerHeatStep_apply, Submodule.mem_orthogonal]
  intro h hh
  have hr0 : inner ℝ h r = 0 := by
    exact hr h hh
  have hl0 : inner ℝ h (D.laplacian r) = 0 := by
    exact D.laplacian_mem_orthogonal r h hh
  rw [inner_sub_right, real_inner_smul_right, hr0, hl0, mul_zero, sub_zero]

def eulerEvolution (a : ℝ) : TemporalHodgeEvolution D where
  T := eulerHeatStep (D := D) a
  fixesHarmonic := fun h hh => eulerHeatStep_fixes_harmonic (D := D) a hh
  preservesResidue := fun r hr => eulerHeatStep_preserves_residue (D := D) a hr

theorem laplacian_exact (a₀ : E) :
    D.laplacian (D.d a₀) = D.d (D.delta (D.d a₀)) := by
  rw [Differential.laplacian]
  simp [D.d_sq_apply]

theorem eulerHeatStep_exact_residue (step : ℝ) (a₀ : E) :
    eulerHeatStep (D := D) step (D.d a₀) =
      D.d (a₀ - step • D.delta (D.d a₀)) := by
  rw [eulerHeatStep_apply, laplacian_exact]
  simp only [map_sub, map_smul, smul_eq_mul]

theorem transport_harmonic_residue {h r : E}
    (hh : h ∈ D.harmonic) (hr : r ∈ D.harmonicᗮ) :
    A.T (h + r) = h + A.T r := by
  rw [map_add, A.fixesHarmonic h hh]

theorem residue_stays_orthogonal {r : E} (hr : r ∈ D.harmonicᗮ) :
    A.T r ∈ D.harmonicᗮ :=
  A.preservesResidue r hr

/-- If the transported residue is exact, the harmonic class is unchanged in cohomology. -/
theorem closed_class_representative
    {h a : E} (hh : h ∈ D.harmonic)
    (hexact : ∃ b : E, A.T (D.d a) = D.d b) :
    ∃ b : E, A.T (h + D.d a) = h + D.d b := by
  obtain ⟨b, hb⟩ := hexact
  have horth : D.d a ∈ D.harmonicᗮ := by
    rw [Submodule.mem_orthogonal]
    intro z hz
    rw [real_inner_comm, D.inner_d_left, (D.mem_harmonic_iff z).mp hz |>.2]
    simp
  refine ⟨b, ?_⟩
  rw [A.transport_harmonic_residue hh horth, hb]

end TemporalHodgeEvolution

end Holonics.Physics
