import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.Normed.Module.Basic

/-!
# A quadratic contraction return for the mild restart map

This owner isolates the metric part of the local-restart argument.  A complete normed carrier, a
linear heat path, and a quadratic Volterra correction determine one continuing map.  Explicit
self-map and two-point bounds on a closed ball return an actual fixed point by Banach's theorem.
No Navier--Stokes regularity or extension conclusion is assumed here.
-/

noncomputable section

open EMetric Function Metric Set
open scoped NNReal

namespace Soma.Holonics.Millennium.NavierStokesQuadraticContraction

variable {X : Type*} [NormedAddCommGroup X]

/-- Data carried by a quadratic perturbation of a declared linear path.  The first inequality
controls the image of the ball; the second controls differences of two nonlinear returns. -/
structure QuadraticContractionData
    (Phi : X → X) (linear : X) (A R : ℝ) : Prop where
  coefficient_nonneg : 0 ≤ A
  radius_nonneg : 0 ≤ R
  linear_le_half : ‖linear‖ ≤ R / 2
  quadratic_le_half : A * R ^ 2 ≤ R / 2
  contraction_lt_one : 2 * A * R < 1
  remainder_bound : ∀ u : X,
    ‖Phi u - linear‖ ≤ A * ‖u‖ ^ 2
  remainder_difference_bound : ∀ u v : X,
    ‖(Phi u - linear) - (Phi v - linear)‖ ≤
      A * (‖u‖ + ‖v‖) * ‖u - v‖

/-- The explicit closed receiver ball used by the contraction. -/
def restartBall (R : ℝ) : Set X := Metric.closedBall 0 R

theorem mem_restartBall_iff {R : ℝ} {u : X} :
    u ∈ restartBall (X := X) R ↔ ‖u‖ ≤ R := by
  simp [restartBall]

/-- The quadratic estimates send the declared closed ball into itself. -/
theorem QuadraticContractionData.mapsTo_restartBall
    {Phi : X → X} {linear : X} {A R : ℝ}
    (data : QuadraticContractionData Phi linear A R) :
    MapsTo Phi (restartBall (X := X) R) (restartBall (X := X) R) := by
  intro u hu
  rw [mem_restartBall_iff] at hu ⊢
  have hquadratic : A * ‖u‖ ^ 2 ≤ A * R ^ 2 := by
    apply mul_le_mul_of_nonneg_left _ data.coefficient_nonneg
    exact pow_le_pow_left₀ (norm_nonneg u) hu 2
  calc
    ‖Phi u‖ ≤ ‖linear‖ + ‖Phi u - linear‖ := by
      have htriangle := norm_add_le linear (Phi u - linear)
      simpa [add_sub_cancel] using htriangle
    _ ≤ R / 2 + A * ‖u‖ ^ 2 :=
      add_le_add data.linear_le_half (data.remainder_bound u)
    _ ≤ R / 2 + A * R ^ 2 := add_le_add (le_refl _) hquadratic
    _ ≤ R / 2 + R / 2 := add_le_add (le_refl _) data.quadratic_le_half
    _ = R := by ring

/-- The restricted mild map has the explicit contraction factor `2 A R`. -/
theorem QuadraticContractionData.contractingWith_restartBall
    {Phi : X → X} {linear : X} {A R : ℝ}
    (data : QuadraticContractionData Phi linear A R) :
    let K : ℝ≥0 := ⟨2 * A * R, mul_nonneg (mul_nonneg (by norm_num)
      data.coefficient_nonneg) data.radius_nonneg⟩
    ContractingWith K
      (data.mapsTo_restartBall.restrict Phi
        (restartBall (X := X) R) (restartBall (X := X) R)) := by
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
    have hu : ‖(u : X)‖ ≤ R := mem_restartBall_iff.mp u.2
    have hv : ‖(v : X)‖ ≤ R := mem_restartBall_iff.mp v.2
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
        dsimp [K]
        ring

/-- **Actual fixed-point return.**  The declared quadratic estimates construct a point in the
closed restart ball fixed by the declared map `Phi`. -/
theorem QuadraticContractionData.exists_fixedPoint_mem_restartBall
    [CompleteSpace X]
    {Phi : X → X} {linear : X} {A R : ℝ}
    (data : QuadraticContractionData Phi linear A R) :
    ∃ u : X, ‖u‖ ≤ R ∧ IsFixedPt Phi u := by
  let K : ℝ≥0 := ⟨2 * A * R, mul_nonneg (mul_nonneg (by norm_num)
    data.coefficient_nonneg) data.radius_nonneg⟩
  have hcomplete : IsComplete (restartBall (X := X) R) :=
    Metric.isClosed_closedBall.isComplete
  have hzero : (0 : X) ∈ restartBall (X := X) R := by
    rw [mem_restartBall_iff]
    simpa using data.radius_nonneg
  have hcontract := data.contractingWith_restartBall
  obtain ⟨u, hu, hfixed, _htendsto, _hrate⟩ :=
    hcontract.exists_fixedPoint' hcomplete data.mapsTo_restartBall hzero
      (edist_ne_top (0 : X) (Phi 0))
  exact ⟨u, mem_restartBall_iff.mp hu, hfixed⟩

section Audit

#print axioms QuadraticContractionData.mapsTo_restartBall
#print axioms QuadraticContractionData.contractingWith_restartBall
#print axioms QuadraticContractionData.exists_fixedPoint_mem_restartBall

end Audit

end Soma.Holonics.Millennium.NavierStokesQuadraticContraction
