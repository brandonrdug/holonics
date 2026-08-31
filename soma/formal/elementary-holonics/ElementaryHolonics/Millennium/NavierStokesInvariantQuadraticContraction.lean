import ElementaryHolonics.Millennium.NavierStokesQuadraticContraction

/-!
# Quadratic contraction inside a closed constitutive fibre

**[proved-derived]** The unconstrained native path carrier is convenient for analytic estimates,
but physical incidences such as Fourier reality occupy closed fibres inside it.  This owner refines
the existing quadratic contraction theorem to the intersection of its restart ball with any
declared closed invariant set.  The fixed point therefore returns with both its norm receipt and
its constitutive incidence.

The set is an explicit receiver fibre, not a new solver or an assertion that any particular
Navier--Stokes path lies in it.  Applications must separately prove closedness, initial membership,
and preservation by the actual mild map.
-/

noncomputable section

open EMetric Function Metric Set
open scoped NNReal

namespace Soma.Holonics.Millennium.NavierStokesInvariantQuadraticContraction

open Soma.Holonics.Millennium.NavierStokesQuadraticContraction

variable {X : Type*} [NormedAddCommGroup X]

/-- The exact intersection of the analytic restart ball and one constitutive fibre. -/
def invariantRestartSet (S : Set X) (R : ℝ) : Set X :=
  restartBall R ∩ S

theorem mem_invariantRestartSet_iff
    {S : Set X} {R : ℝ} {u : X} :
    u ∈ invariantRestartSet S R ↔ ‖u‖ ≤ R ∧ u ∈ S := by
  simp [invariantRestartSet, mem_restartBall_iff]

/-- A quadratic map which preserves the declared fibre maps the intersected restart population to
itself. -/
theorem mapsTo_invariantRestartSet
    {Phi : X → X} {linear : X} {A R : ℝ}
    (data : QuadraticContractionData Phi linear A R)
    {S : Set X} (hPhi : MapsTo Phi S S) :
    MapsTo Phi (invariantRestartSet S R) (invariantRestartSet S R) := by
  intro u hu
  exact ⟨data.mapsTo_restartBall hu.1, hPhi hu.2⟩

/-- Restricting the same local quadratic estimates to a smaller invariant fibre preserves the
explicit contraction factor. -/
theorem contractingWith_invariantRestartSet
    {Phi : X → X} {linear : X} {A R : ℝ}
    (data : QuadraticContractionData Phi linear A R)
    {S : Set X} (hPhi : MapsTo Phi S S) :
    let K : ℝ≥0 := ⟨2 * A * R, mul_nonneg (mul_nonneg (by norm_num)
      data.coefficient_nonneg) data.radius_nonneg⟩
    ContractingWith K
      ((mapsTo_invariantRestartSet data hPhi).restrict Phi
        (invariantRestartSet S R) (invariantRestartSet S R)) := by
  let K : ℝ≥0 := ⟨2 * A * R, mul_nonneg (mul_nonneg (by norm_num)
    data.coefficient_nonneg) data.radius_nonneg⟩
  dsimp only
  constructor
  · exact_mod_cast data.contraction_lt_one
  · apply LipschitzWith.of_dist_le_mul
    intro u v
    change dist (Phi (u : X)) (Phi (v : X)) ≤
      (K : ℝ) * dist (u : X) (v : X)
    rw [dist_eq_norm, dist_eq_norm]
    have hu : ‖(u : X)‖ ≤ R := mem_restartBall_iff.mp u.2.1
    have hv : ‖(v : X)‖ ≤ R := mem_restartBall_iff.mp v.2.1
    have hsum : ‖(u : X)‖ + ‖(v : X)‖ ≤ 2 * R := by linarith
    have hdiff := data.remainder_difference_bound (u : X) (v : X)
    have hrearrange :
        ((Phi (u : X) - linear) - (Phi (v : X) - linear)) =
          Phi (u : X) - Phi (v : X) := by abel
    rw [hrearrange] at hdiff
    calc
      ‖Phi (u : X) - Phi (v : X)‖ ≤
          A * (‖(u : X)‖ + ‖(v : X)‖) * ‖(u : X) - (v : X)‖ := hdiff
      _ ≤ A * (2 * R) * ‖(u : X) - (v : X)‖ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsum data.coefficient_nonneg) (norm_nonneg _)
      _ = (K : ℝ) * ‖(u : X) - (v : X)‖ := by
        simp [K]
        left
        change A * (2 * R) = 2 * A * R
        ring

/-- **Actual invariant fixed-point return.**  A closed fibre preserved by the quadratic map and
containing the zero seed contains a fixed point in the declared restart ball. -/
theorem exists_fixedPoint_mem_restartBall_and_invariant
    [CompleteSpace X]
    {Phi : X → X} {linear : X} {A R : ℝ}
    (data : QuadraticContractionData Phi linear A R)
    {S : Set X} (hS : IsClosed S) (hzeroS : (0 : X) ∈ S)
    (hPhi : MapsTo Phi S S) :
    ∃ u : X, ‖u‖ ≤ R ∧ u ∈ S ∧ IsFixedPt Phi u := by
  let K : ℝ≥0 := ⟨2 * A * R, mul_nonneg (mul_nonneg (by norm_num)
    data.coefficient_nonneg) data.radius_nonneg⟩
  have hclosed : IsClosed (invariantRestartSet S R) :=
    Metric.isClosed_closedBall.inter hS
  have hcomplete : IsComplete (invariantRestartSet S R) := hclosed.isComplete
  have hzero : (0 : X) ∈ invariantRestartSet S R := by
    refine ⟨?_, hzeroS⟩
    rw [mem_restartBall_iff]
    simpa using data.radius_nonneg
  have hmaps := mapsTo_invariantRestartSet data hPhi
  have hcontract := contractingWith_invariantRestartSet data hPhi
  obtain ⟨u, hu, hfixed, _htendsto, _hrate⟩ :=
    hcontract.exists_fixedPoint' hcomplete hmaps hzero
      (edist_ne_top (0 : X) (Phi 0))
  exact ⟨u, mem_restartBall_iff.mp hu.1, hu.2, hfixed⟩

section Audit

#print axioms mapsTo_invariantRestartSet
#print axioms contractingWith_invariantRestartSet
#print axioms exists_fixedPoint_mem_restartBall_and_invariant

end Audit

end Soma.Holonics.Millennium.NavierStokesInvariantQuadraticContraction
