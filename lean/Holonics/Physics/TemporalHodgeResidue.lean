import Holonics.Hodge.HodgeGreenOperator
import Holonics.Transport.ChangingReceiver.Defect

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

/-! ## A moving or coarse receiver retains its Hodge transport defect

[agent-inferred] A cochain square alone does not fix the metric adjoint: a cut,
changed constitution, or nonisometric chart can change it. The four-term return
below extends the existing heat consumer, rather than declaring a second Hodge
decomposition or assuming the receiver is a reducing subcomplex. The rates use
the existing changing-receiver owner. Boundary conditions are part of the supplied
differentials and adjoints; no continuum boundary or algebraic-cycle claim follows.
-/
namespace CoarseHodgeTransport

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

def differentialDefect (D : Differential E) (C : Differential F)
    (q : E →L[ℝ] F) (x : E) : F := C.d (q x) - q (D.d x)

def codifferentialDefect (D : Differential E) (C : Differential F)
    (q : E →L[ℝ] F) (x : E) : F := C.delta (q x) - q (D.delta x)

def laplacianDefect (D : Differential E) (C : Differential F)
    (q : E →L[ℝ] F) (x : E) : F := C.laplacian (q x) - q (D.laplacian x)

/-- Both differential and adjoint squares contribute, with their signed returns
kept before taking a norm. This identity requires no isometry or injectivity of q. -/
theorem laplacianDefect_eq_four_returns (D : Differential E) (C : Differential F)
    (q : E →L[ℝ] F) (x : E) :
    laplacianDefect D C q x =
      C.d (codifferentialDefect D C q x) +
        differentialDefect D C q (D.delta x) +
        C.delta (differentialDefect D C q x) +
        codifferentialDefect D C q (D.d x) := by
  simp only [laplacianDefect, differentialDefect, codifferentialDefect,
    Differential.laplacian, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, map_add, map_sub]
  abel

/-- A source harmonic mode stays harmonic exactly when this receiver's
Laplacian defect vanishes on that mode. Chain compatibility alone is insufficient. -/
theorem harmonic_image_iff_defect_zero (D : Differential E) (C : Differential F)
    (q : E →L[ℝ] F) {h : E} (hh : h ∈ D.harmonic) :
    q h ∈ C.harmonic ↔ laplacianDefect D C q h = 0 := by
  have hz : D.laplacian h = 0 := LinearMap.mem_ker.mp hh
  change C.laplacian (q h) = 0 ↔ _
  simp [laplacianDefect, hz]

/-- The actual finite Euler heat consumer returns the unresolved operator term.
The step is algebraic; its stability remains a separate spectral condition. -/
theorem eulerHeatStep_receiver_return (D : Differential E) (C : Differential F)
    (q : E →L[ℝ] F) (step : ℝ) (x : E) :
    q (TemporalHodgeEvolution.eulerHeatStep (D := D) step x) =
      TemporalHodgeEvolution.eulerHeatStep (D := C) step (q x) +
        step • laplacianDefect D C q x := by
  simp only [TemporalHodgeEvolution.eulerHeatStep_apply, laplacianDefect,
    map_sub, map_smul, smul_sub]
  abel

/-- Zero step hides every defect. At a nonzero declared step, heat and receiver
commute at a source precisely when its complete Laplacian defect is zero. -/
theorem eulerHeatStep_commutes_iff (D : Differential E) (C : Differential F)
    (q : E →L[ℝ] F) (step : ℝ) (hstep : step ≠ 0) (x : E) :
    q (TemporalHodgeEvolution.eulerHeatStep (D := D) step x) =
        TemporalHodgeEvolution.eulerHeatStep (D := C) step (q x) ↔
      laplacianDefect D C q x = 0 := by
  rw [eulerHeatStep_receiver_return]
  constructor
  · intro heq
    have hz : step • laplacianDefect D C q x = 0 := by
      exact add_left_cancel (heq.trans (add_zero _).symm)
    exact (smul_eq_zero.mp hz).resolve_left hstep
  · intro hz
    simp [hz]

/-- The changing-chart theorem is consumed with the actual two Hodge heat
rates. Qdot survives even where instantaneous Laplacians intertwine. -/
theorem moving_heat_receiver_rate (D : Differential E) (C : Differential F)
    (q : ℝ → E →L[ℝ] F) (qdot : E →L[ℝ] F)
    (x : ℝ → E) (time nu : ℝ)
    (hq : HasDerivAt q qdot time)
    (hx : HasDerivAt x (-nu • D.laplacian (x time)) time) :
    HasDerivAt (fun t => q t (x t))
      (-nu • C.laplacian (q time (x time)) +
        (qdot (x time) + nu • laplacianDefect D C (q time) (x time))) time := by
  have hr := Holonics.Transport.ChangingReceiver.moving_receiver_rate q x time qdot
    (fun z => -nu • D.laplacian z) (fun z => -nu • C.laplacian z) hq hx
  convert hr using 1
  simp only [Holonics.Transport.ChangingReceiver.rateDefect, laplacianDefect,
    map_smul, smul_sub, neg_smul]
  abel_nf
  simp only [map_zsmul, map_smul]

end CoarseHodgeTransport

end Holonics.Physics

#print axioms Holonics.Physics.CoarseHodgeTransport.laplacianDefect_eq_four_returns
#print axioms Holonics.Physics.CoarseHodgeTransport.harmonic_image_iff_defect_zero
#print axioms Holonics.Physics.CoarseHodgeTransport.eulerHeatStep_receiver_return
#print axioms Holonics.Physics.CoarseHodgeTransport.eulerHeatStep_commutes_iff
#print axioms Holonics.Physics.CoarseHodgeTransport.moving_heat_receiver_rate
