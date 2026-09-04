import ElementaryHolonics.Millennium.NavierStokesShellStepCost

/-!
# The band feed is a comb: its square is the diagonal plus the pairwise grips

The band feed at a tail mode is a finite sum of feed terms, one per tooth of the frequency comb
inside the cube.  Its squared modulus expands exactly into the diagonal, the sum of the squared
teeth, plus the cross term, the sum over ordered pairs of distinct teeth of their real inner
product, the grip between two teeth.

```text
‖Σ_p z_p‖² = Σ_p ‖z_p‖² + Σ_p Σ_{q ≠ p} ⟪z_p, z_q⟫_ℝ.
```

The coherent bound pays every tooth with aligned phase and returns the count `(2N+1)³`.  When the
cross term is nonpositive, the feed is paid by the diagonal alone and the count enters as its
square root, `(2N+1)^{3/2}`.  That half power is the whole distance between the energy-paid and
the enstrophy-paid coefficient, and it is a statement about the grips between teeth, that is about
the relative phases the arcs have swept, not about the energy.

Viola's Dirac-brush dichotomy (arXiv 1812.05346) is the same statement on the line: a comb rotated
in phase space remains a discrete comb exactly when the rotation's cotangent is rational, and
otherwise its support is the whole line.  A rational rotation composes the teeth coherently; an
irrational one spreads them into a brush.  Nothing here decides which the actual band does; the
cross term is named so that the hypothesis can be stated on it.
-/

noncomputable section

open Set Filter Topology MeasureTheory
open scoped Finset

namespace Soma.Holonics.Millennium.NavierStokesBandCoherence

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPeriodicEnergy
open Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCancellation
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionRemainderBound
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionFullStrain
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionFiniteBandBridge
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionPhysicalBridge
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionBaseEnergy
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionSourceModulus
open Soma.Holonics.Millennium.NavierStokesCoordinateJacobianFourierReconstruction
open Soma.Holonics.Millennium.NavierStokesH2StorageDissipationPayment
open Soma.Holonics.Millennium.NavierStokesAlignedStrainBudget
open Soma.Holonics.Millennium.NavierStokesShellStepCost
open Soma.Holonics.Millennium.NavierStokesFrequencyReach

variable {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
  {pressure : PressureField}
  (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
  (t : Ioo 0 T)

/-! ## The comb expansion of a finite complex sum -/

/-- The squared modulus of a finite sum is the diagonal plus the pairwise grips. -/
theorem norm_sum_sq_eq_diagonal_add_cross {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (z : ι → ℂ) :
    ‖∑ p ∈ s, z p‖ ^ 2 =
      ∑ p ∈ s, ‖z p‖ ^ 2 + ∑ p ∈ s, ∑ q ∈ s.erase p, inner ℝ (z p) (z q) := by
  rw [← real_inner_self_eq_norm_sq, sum_inner, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  rw [inner_sum, ← real_inner_self_eq_norm_sq]
  exact (Finset.add_sum_erase s (fun q ↦ inner ℝ (z p) (z q)) hp).symm

/-! ## The band feed as a comb -/

/-- The diagonal of the band feed: the squared teeth. -/
def bandDiagonal (radius : ℕ) (k : SpatialFrequency) (output : Fin 3) : ℝ :=
  ∑ p ∈ frequencyCube radius, ‖feedTerm solution t k p output‖ ^ 2

/-- The cross term of the band feed: the grips between distinct teeth. -/
def bandCrossTerm (radius : ℕ) (k : SpatialFrequency) (output : Fin 3) : ℝ :=
  ∑ p ∈ frequencyCube radius, ∑ q ∈ (frequencyCube radius).erase p,
    inner ℝ (feedTerm solution t k p output) (feedTerm solution t k q output)

/-- **The band feed is a comb.** -/
theorem norm_bandFeed_sq_eq (radius : ℕ) (k : SpatialFrequency) (output : Fin 3) :
    ‖bandFeed solution t radius k output‖ ^ 2 =
      bandDiagonal solution t radius k output + bandCrossTerm solution t radius k output := by
  unfold bandFeed bandDiagonal bandCrossTerm
  exact norm_sum_sq_eq_diagonal_add_cross _ _

/-- Each tooth is paid by the half-density of the initial energy times the Jacobian tail mass. -/
theorem norm_feedTerm_le_energy (hnu : 0 ≤ nu) {radius : ℕ} {k p : SpatialFrequency}
    (hk : k ∉ frequencyCube (2 * radius)) (hp : p ∈ frequencyCube radius) (output : Fin 3) :
    ‖feedTerm solution t k p output‖ ≤
      3 * Real.sqrt (2 * periodicKineticEnergy velocity 0) *
        openPeriodicJacobianCoefficientTailMass solution t (frequencyCube radius) := by
  have htransported : k - p ∉ frequencyCube radius := by
    intro hkp
    apply hk
    have := add_mem_frequencyCube hkp hp
    rw [sub_add_cancel, ← two_mul] at this
    exact this
  refine (norm_feedTerm_le solution t htransported output).trans ?_
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  have hE := openPeriodicSolutionOn_periodicKineticEnergy_le_initial solution hnu t.2
  have hsqrt : Real.sqrt (2 * periodicKineticEnergy velocity t.1) ≤
      Real.sqrt (2 * periodicKineticEnergy velocity 0) :=
    Real.sqrt_le_sqrt (by linarith)
  exact (complexVectorL1_openPeriodicVelocityFourierMode_le_L2RootReceiver solution t p).trans
    ((openPeriodicVelocityL2RootReceiver_le_kineticEnergy solution t).trans
      (mul_le_mul_of_nonneg_left hsqrt (by norm_num)))

/-- The diagonal is paid by the count times the squared tooth bound. -/
theorem bandDiagonal_le (hnu : 0 ≤ nu) {radius : ℕ} {k : SpatialFrequency}
    (hk : k ∉ frequencyCube (2 * radius)) (output : Fin 3) :
    bandDiagonal solution t radius k output ≤
      (2 * radius + 1) ^ 3 *
        (3 * Real.sqrt (2 * periodicKineticEnergy velocity 0) *
          openPeriodicJacobianCoefficientTailMass solution t (frequencyCube radius)) ^ 2 := by
  unfold bandDiagonal
  have hterm : ∀ p ∈ frequencyCube radius,
      ‖feedTerm solution t k p output‖ ^ 2 ≤
        (3 * Real.sqrt (2 * periodicKineticEnergy velocity 0) *
          openPeriodicJacobianCoefficientTailMass solution t (frequencyCube radius)) ^ 2 :=
    fun p hp ↦ pow_le_pow_left₀ (norm_nonneg _) (norm_feedTerm_le_energy solution t hnu hk hp output) 2
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, card_frequencyCube, nsmul_eq_mul]
  push_cast
  exact le_rfl

/-- **The incoherent bound.**  When the grips between distinct teeth are nonpositive, the band feed
is paid by the square root of the count: the half power. -/
theorem norm_bandFeed_le_of_crossTerm_nonpos (hnu : 0 ≤ nu) {radius : ℕ} {k : SpatialFrequency}
    (hk : k ∉ frequencyCube (2 * radius)) (output : Fin 3)
    (hcross : bandCrossTerm solution t radius k output ≤ 0) :
    ‖bandFeed solution t radius k output‖ ≤
      Real.sqrt ((2 * radius + 1) ^ 3) *
        (3 * Real.sqrt (2 * periodicKineticEnergy velocity 0) *
          openPeriodicJacobianCoefficientTailMass solution t (frequencyCube radius)) := by
  have hsq : ‖bandFeed solution t radius k output‖ ^ 2 ≤
      (2 * radius + 1) ^ 3 *
        (3 * Real.sqrt (2 * periodicKineticEnergy velocity 0) *
          openPeriodicJacobianCoefficientTailMass solution t (frequencyCube radius)) ^ 2 := by
    rw [norm_bandFeed_sq_eq]
    linarith [bandDiagonal_le solution t hnu hk output]
  have hbound : 0 ≤ 3 * Real.sqrt (2 * periodicKineticEnergy velocity 0) *
      openPeriodicJacobianCoefficientTailMass solution t (frequencyCube radius) :=
    mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) (norm_nonneg _)
  have hcount : (0 : ℝ) ≤ (2 * radius + 1) ^ 3 := by positivity
  rw [← Real.sqrt_sq (norm_nonneg _), ← Real.sqrt_sq hbound, ← Real.sqrt_mul hcount]
  exact Real.sqrt_le_sqrt hsq

/-- The coherent bound, for comparison: the count itself. -/
theorem norm_bandFeed_le_coherent (hnu : 0 ≤ nu) {radius : ℕ} {k : SpatialFrequency}
    (hk : k ∉ frequencyCube (2 * radius)) (output : Fin 3) :
    ‖bandFeed solution t radius k output‖ ≤
      (2 * radius + 1) ^ 3 *
        (3 * Real.sqrt (2 * periodicKineticEnergy velocity 0) *
          openPeriodicJacobianCoefficientTailMass solution t (frequencyCube radius)) := by
  refine (norm_bandFeed_le solution t hk output).trans ?_
  rw [← mul_assoc]
  exact mul_le_mul_of_nonneg_right (bandMass_le_count_mul_energy solution t hnu radius)
    (norm_nonneg _)

section Audit

#print axioms norm_sum_sq_eq_diagonal_add_cross
#print axioms norm_bandFeed_sq_eq
#print axioms norm_bandFeed_le_of_crossTerm_nonpos
#print axioms norm_bandFeed_le_coherent

end Audit

end Soma.Holonics.Millennium.NavierStokesBandCoherence
