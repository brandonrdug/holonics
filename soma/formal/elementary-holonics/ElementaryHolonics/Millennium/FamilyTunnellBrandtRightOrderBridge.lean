import ElementaryHolonics.Millennium.FamilyTunnellBrandtStabilizerWeights
import Mathlib.Algebra.Quaternion

/-!
# Concrete Lipschitz-unit population comparison and action obstruction

This file records the concrete finite Lipschitz-unit population available from
the quaternion owners.  It deliberately separates that population comparison
from the two quadratic-automorphism fibres: an arbitrary finite equivalence is
easy, while an action-compatible Brandt passage would require additional
order/ideal transport data not present in the current quaternion owners.
-/

noncomputable section
namespace Soma.Holonics.Millennium.FamilyTunnellBrandtRightOrderBridge

open scoped Quaternion
open Soma.Holonics.Millennium.FamilyTunnellQuaternionicBridge
open Soma.Holonics.Millennium.FamilyTunnellBrandtUnitWeights
open Soma.Holonics.Millennium.FamilyTunnellBrandtStabilizerWeights

abbrev HamiltonInt := ℍ[ℤ]

/-- The eight norm-one Lipschitz integral units, retained as an addressed
population rather than collapsed to the numeral eight. -/
def lipschitzUnit : Fin 8 → HamiltonInt :=
  ![hmk (1) (0) (0) (0), hmk (-1) (0) (0) (0), hmk (0) (1) (0) (0), hmk (0) (-1) (0) (0),
    hmk (0) (0) (1) (0), hmk (0) (0) (-1) (0), hmk (0) (0) (0) (1), hmk (0) (0) (0) (-1)]

theorem lipschitzUnit_injective : Function.Injective lipschitzUnit := by
  intro i j h
  have hre := congrArg QuaternionAlgebra.re h
  have hi := congrArg QuaternionAlgebra.imI h
  have hj := congrArg QuaternionAlgebra.imJ h
  have hk := congrArg QuaternionAlgebra.imK h
  fin_cases i <;> fin_cases j <;>
    simp [lipschitzUnit] at hre hi hj hk ⊢

theorem lipschitzUnit_normSq (i : Fin 8) :
    Quaternion.normSq (lipschitzUnit i) = 1 := by
  fin_cases i <;> simp [lipschitzUnit, Quaternion.normSq_def']

abbrev lipschitzUnitPopulation := Fin 8

theorem lipschitzUnitPopulation_card : Fintype.card lipschitzUnitPopulation = 8 := by
  simp [lipschitzUnitPopulation]

private noncomputable def populationToLabel :
    lipschitzUnitPopulation ≃ (Bool × Bool × Bool) := by
  exact (Fintype.equivFin (Bool × Bool × Bool)).symm.trans
    (Equiv.cast (by simp))

/-- A concrete finite-population equivalence to the q₁ automorphism fibre.
This is only a population equivalence; it does not yet claim quaternionic
right-order action compatibility. -/
noncomputable def firstPopulationEquiv :
    lipschitzUnitPopulation ≃ LatticeTransport q₁ :=
  populationToLabel.trans q₁TransportEquiv

/-- The analogous population equivalence for q₂. -/
noncomputable def secondPopulationEquiv :
    lipschitzUnitPopulation ≃ LatticeTransport q₂ :=
  populationToLabel.trans q₂TransportEquiv

theorem firstPopulationEquiv_card :
    Fintype.card lipschitzUnitPopulation = Fintype.card (LatticeTransport q₁) := by
  exact Fintype.card_congr firstPopulationEquiv

theorem secondPopulationEquiv_card :
    Fintype.card lipschitzUnitPopulation = Fintype.card (LatticeTransport q₂) := by
  exact Fintype.card_congr secondPopulationEquiv

/-- Exact source audit: the present quaternion owner supplies embeddings and
norms, but no right-order/ideal multiplication or Brandt-neighbor action.
These fields are concrete data requirements, not a claim that the
Lipschitz-unit population is a Brandt weight or that a right-order
realization has already been constructed. -/
structure RightOrderActionData (RightOrderUnitPopulation : Type*)
    [Fintype RightOrderUnitPopulation] where
  firstUnitPopulationEquiv : RightOrderUnitPopulation ≃ lipschitzUnitPopulation
  firstNeighborTransport : RightOrderUnitPopulation → LatticeTransport q₁
  secondNeighborTransport : RightOrderUnitPopulation → LatticeTransport q₂
  first_transport_agrees :
    ∀ u, firstNeighborTransport u = firstPopulationEquiv (firstUnitPopulationEquiv u)
  second_transport_agrees :
    ∀ u, secondNeighborTransport u = secondPopulationEquiv (firstUnitPopulationEquiv u)

def rightOrderActionDataObligation (RightOrderUnitPopulation : Type*)
    [Fintype RightOrderUnitPopulation] : Prop :=
  Nonempty (RightOrderActionData RightOrderUnitPopulation)

#print axioms lipschitzUnit_injective
#print axioms lipschitzUnit_normSq
#print axioms firstPopulationEquiv_card
#print axioms secondPopulationEquiv_card

end Soma.Holonics.Millennium.FamilyTunnellBrandtRightOrderBridge
