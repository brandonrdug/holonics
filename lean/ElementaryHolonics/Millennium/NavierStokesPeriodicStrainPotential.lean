import ElementaryHolonics.Millennium.NavierStokesPeriodicCore

/-!
# A smooth periodic strain potential

This owner gives an explicit trigonometric vector potential on the unit three-torus.  Its actual
curl is therefore a smooth periodic divergence-free initial datum, to which the existing positive
viscosity local-existence construction applies.
-/

noncomputable section

open ContDiff Function Set Topology

namespace Soma.Holonics.Millennium.NavierStokesPeriodicStrainPotential

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesAxisymmetricChart
open Soma.Holonics.Millennium.NavierStokesCoreVectorPotential
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPeriodicCore
open Soma.Holonics.Millennium.NavierStokesPeriodicLocalExistence
open scoped BigOperators

def strainPhase (x : ℝ) : ℝ := (2 * Real.pi) * x

def strainF (θ : ℝ) : ℝ := (3 / 2) * Real.sin θ - (3 / 10) * Real.sin (2 * θ) +
  (1 / 30) * Real.sin (3 * θ)

def strainC (θ : ℝ) : ℝ := (3 / 2) * Real.cos θ - (3 / 5) * Real.cos (2 * θ) +
  (1 / 10) * Real.cos (3 * θ)

def strainPsi (x y : ℝ) : ℝ :=
  (169 / 216) * (Real.cos x + Real.cos y) - (4 / 135) *
      (Real.cos (2 * x) + Real.cos (2 * y)) +
    (11 / 3240) * (Real.cos (3 * x) + Real.cos (3 * y)) +
    (7 / 27) * Real.cos x * Real.cos y + (1 / 108) *
      (Real.cos (2 * x) * Real.cos y + Real.cos x * Real.cos (2 * y))

def strainB (rho z : ℝ) : ℝ := 1 + rho * (1 - Real.cos z) ^ 3

def periodicStrainPotential (a rho : ℝ) : InitialVelocity := fun X ↦
  assemble
    (-(a / 2) * strainC (strainPhase (X 0)) * strainF (strainPhase (X 1)) *
      strainF (strainPhase (X 2)))
    ((a / 2) * strainF (strainPhase (X 0)) * strainC (strainPhase (X 1)) *
      strainF (strainPhase (X 2)))
    (strainB rho (strainPhase (X 2)) *
      strainPsi (strainPhase (X 0)) (strainPhase (X 1)))

theorem periodicStrainPotential_contDiff (a rho : ℝ) :
    ContDiff ℝ ∞ (periodicStrainPotential a rho) := by
  unfold periodicStrainPotential assemble strainPhase strainF strainC strainB strainPsi
  fun_prop

private theorem strain_phase_shift (x : Space) (i j : Fin 3) :
    strainPhase ((x + EuclideanSpace.single i (1 : ℝ)) j) =
      strainPhase (x j) + if i = j then 2 * Real.pi else 0 := by
  by_cases hij : i = j
  · subst i
    simp [strainPhase]
    ring
  · simp [strainPhase, hij]

private theorem strain_sin_nat_phase_periodic (n : ℕ) (x : Space) (i j : Fin 3) :
    Real.sin (n * strainPhase ((x + EuclideanSpace.single i (1 : ℝ)) j)) =
      Real.sin (n * strainPhase (x j)) := by
  rw [strain_phase_shift]
  by_cases hij : i = j
  · simp only [if_pos hij]
    rw [show (n : ℝ) * (strainPhase (x j) + 2 * Real.pi) =
      (n : ℝ) * strainPhase (x j) + n * (2 * Real.pi) by ring]
    exact Real.sin_add_nat_mul_two_pi ((n : ℝ) * strainPhase (x j)) n
  · simp [hij]

private theorem strain_cos_nat_phase_periodic (n : ℕ) (x : Space) (i j : Fin 3) :
    Real.cos (n * strainPhase ((x + EuclideanSpace.single i (1 : ℝ)) j)) =
      Real.cos (n * strainPhase (x j)) := by
  rw [strain_phase_shift]
  by_cases hij : i = j
  · simp only [if_pos hij]
    rw [show (n : ℝ) * (strainPhase (x j) + 2 * Real.pi) =
      (n : ℝ) * strainPhase (x j) + n * (2 * Real.pi) by ring]
    exact Real.cos_add_nat_mul_two_pi ((n : ℝ) * strainPhase (x j)) n
  · simp [hij]

theorem periodicStrainPotential_isOnePeriodic (a rho : ℝ) :
    IsOnePeriodic (periodicStrainPotential a rho) := by
  intro x i
  have hsin (j : Fin 3) := strain_sin_nat_phase_periodic 1 x i j
  have hsin2 (j : Fin 3) := strain_sin_nat_phase_periodic 2 x i j
  have hsin3 (j : Fin 3) := strain_sin_nat_phase_periodic 3 x i j
  have hcos (j : Fin 3) := strain_cos_nat_phase_periodic 1 x i j
  have hcos2 (j : Fin 3) := strain_cos_nat_phase_periodic 2 x i j
  have hcos3 (j : Fin 3) := strain_cos_nat_phase_periodic 3 x i j
  have hsin1' (j : Fin 3) :
      Real.sin (strainPhase ((x + EuclideanSpace.single i (1 : ℝ)) j)) =
        Real.sin (strainPhase (x j)) := by simpa using hsin j
  have hsin2' (j : Fin 3) :
      Real.sin (2 * strainPhase ((x + EuclideanSpace.single i (1 : ℝ)) j)) =
        Real.sin (2 * strainPhase (x j)) := by simpa using hsin2 j
  have hsin3' (j : Fin 3) :
      Real.sin (3 * strainPhase ((x + EuclideanSpace.single i (1 : ℝ)) j)) =
        Real.sin (3 * strainPhase (x j)) := by simpa using hsin3 j
  have hcos1' (j : Fin 3) :
      Real.cos (strainPhase ((x + EuclideanSpace.single i (1 : ℝ)) j)) =
        Real.cos (strainPhase (x j)) := by simpa using hcos j
  have hcos2' (j : Fin 3) :
      Real.cos (2 * strainPhase ((x + EuclideanSpace.single i (1 : ℝ)) j)) =
        Real.cos (2 * strainPhase (x j)) := by simpa using hcos2 j
  have hcos3' (j : Fin 3) :
      Real.cos (3 * strainPhase ((x + EuclideanSpace.single i (1 : ℝ)) j)) =
        Real.cos (3 * strainPhase (x j)) := by simpa using hcos3 j
  have hF (j : Fin 3) :
      strainF (strainPhase ((x + EuclideanSpace.single i (1 : ℝ)) j)) =
        strainF (strainPhase (x j)) := by
    unfold strainF
    rw [hsin1' j, hsin2' j, hsin3' j]
  have hC (j : Fin 3) :
      strainC (strainPhase ((x + EuclideanSpace.single i (1 : ℝ)) j)) =
        strainC (strainPhase (x j)) := by
    unfold strainC
    rw [hcos1' j, hcos2' j, hcos3' j]
  have hB (j : Fin 3) :
      strainB rho (strainPhase ((x + EuclideanSpace.single i (1 : ℝ)) j)) =
        strainB rho (strainPhase (x j)) := by
    unfold strainB
    rw [hcos1' j]
  have hPsi :
      strainPsi (strainPhase ((x + EuclideanSpace.single i (1 : ℝ)) 0))
          (strainPhase ((x + EuclideanSpace.single i (1 : ℝ)) 1)) =
        strainPsi (strainPhase (x 0)) (strainPhase (x 1)) := by
    unfold strainPsi
    rw [hcos1' 0, hcos1' 1, hcos2' 0, hcos2' 1, hcos3' 0, hcos3' 1]
  have hcoord (j : Fin 3) :
      ((x + EuclideanSpace.single i (1 : ℝ)) j) =
        x j + if j = i then 1 else 0 := by
    simp [PiLp.add_apply]
  have hF' (j : Fin 3) :
      strainF (strainPhase (x j + if j = i then 1 else 0)) =
        strainF (strainPhase (x j)) := by
    rw [← hcoord j]
    exact hF j
  have hC' (j : Fin 3) :
      strainC (strainPhase (x j + if j = i then 1 else 0)) =
        strainC (strainPhase (x j)) := by
    rw [← hcoord j]
    exact hC j
  have hB' (j : Fin 3) :
      strainB rho (strainPhase (x j + if j = i then 1 else 0)) =
        strainB rho (strainPhase (x j)) := by
    rw [← hcoord j]
    exact hB j
  have hPsi' :
      strainPsi (strainPhase (x 0 + if 0 = i then 1 else 0))
          (strainPhase (x 1 + if 1 = i then 1 else 0)) =
        strainPsi (strainPhase (x 0)) (strainPhase (x 1)) := by
    rw [← hcoord 0, ← hcoord 1]
    exact hPsi
  unfold periodicStrainPotential
  apply PiLp.ext
  intro j
  fin_cases j
  · simp [assemble, hC', hF', hB', hPsi']
  · simp [assemble, hC', hF', hB', hPsi']
  · simp [assemble, hC', hF', hB', hPsi']

def periodicStrainVelocity (a rho : ℝ) : InitialVelocity :=
  coreCurl (periodicStrainPotential a rho)

theorem periodicStrainVelocity_initial_condition (a rho : ℝ) :
    InitialVelocityConditionPeriodic (periodicStrainVelocity a rho) where
  divergenceFree := by
    intro x
    exact divergence_coreCurl_eq_zero (periodicStrainPotential a rho)
      ((periodicStrainPotential_contDiff a rho).of_le
        (WithTop.coe_le_coe.mpr le_top)) x
  smooth := coreCurl_contDiff _ (periodicStrainPotential_contDiff a rho)
  periodic := coreCurl_isOnePeriodic _ (periodicStrainPotential_isOnePeriodic a rho)

theorem periodicStrainVelocity_local_existence (a rho nu : ℝ) (hnu : 0 < nu) :
    ∃ T velocity pressure, 0 < T ∧
      OpenPeriodicSolutionOn T nu (periodicStrainVelocity a rho)
        (fun _ _ ↦ 0) velocity pressure := by
  exact periodicLocalExistence nu hnu _ (periodicStrainVelocity_initial_condition a rho)

#print axioms periodicStrainPotential_contDiff
#print axioms periodicStrainPotential_isOnePeriodic
#print axioms periodicStrainVelocity_initial_condition
#print axioms periodicStrainVelocity_local_existence

end Soma.Holonics.Millennium.NavierStokesPeriodicStrainPotential
