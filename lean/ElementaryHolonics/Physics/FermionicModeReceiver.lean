import ElementaryHolonics.Computation.HolonicFermionicOccupation
import ElementaryHolonics.Computation.HolonicAdjointNormalization

/-!
# A fermionic mode's Gibbs receiver and the binary normalized exponential

The existing CAR owner supplies exclusion. This separate thermal chart supplies grand-canonical
weights for one mode with occupation 0 or 1. Independent-mode factorization is not asserted for
an interacting many-body Hamiltonian. Energy and chemical potential retain the same declared unit;
beta is the inverse energy scale. No spacetime position or preparation-history identifier enters.
-/

noncomputable section

namespace Soma.Holonics.Physics.FermionicModeReceiver

open Soma.Holonics.Computation.HolonicAdjointNormalization
open Soma.Holonics.Computation.HolonicInformationTheory

def thermalMode (beta energy chemicalPotential : ℝ) : PositiveProbabilitySection Bool :=
  NormalizedExponential.face (fun occupied => if occupied then -beta * (energy - chemicalPotential) else 0)

theorem occupation_is_sigmoid (beta energy chemicalPotential : ℝ) :
    (thermalMode beta energy chemicalPotential).mass true =
      sigmoidFace (beta * (chemicalPotential - energy)) := by
  unfold thermalMode
  rw [show -beta * (energy - chemicalPotential) = beta * (chemicalPotential - energy) by ring]
  exact sigmoid_is_binary_normalized_exponential _

theorem fermi_dirac_receiver (beta energy chemicalPotential : ℝ) :
    (thermalMode beta energy chemicalPotential).mass true =
      1 / (1 + Real.exp (beta * (energy - chemicalPotential))) := by
  rw [occupation_is_sigmoid]
  unfold sigmoidFace
  rw [show beta * (energy - chemicalPotential) = -(beta * (chemicalPotential - energy)) by ring,
    Real.exp_neg]
  have nonzero : Real.exp (beta * (chemicalPotential - energy)) ≠ 0 := Real.exp_ne_zero _
  have sum_nonzero : Real.exp (beta * (chemicalPotential - energy)) + 1 ≠ 0 := by positivity
  field_simp

/-- The available final-state weight is the vacant occupation weight. -/
theorem vacancy_is_one_minus_occupation (beta energy chemicalPotential : ℝ) :
    (thermalMode beta energy chemicalPotential).mass false =
      1 - (thermalMode beta energy chemicalPotential).mass true := by
  have normalized := (thermalMode beta energy chemicalPotential).normalized
  simp only [Fintype.sum_bool] at normalized
  linarith

/-- A common shift of energy and chemical reference changes neither occupation face. -/
theorem common_energy_reference (beta energy chemicalPotential offset : ℝ) :
    (thermalMode beta (energy + offset) (chemicalPotential + offset)).mass =
      (thermalMode beta energy chemicalPotential).mass := by
  simp only [thermalMode, add_sub_add_right_eq_sub]

#print axioms occupation_is_sigmoid
#print axioms fermi_dirac_receiver
#print axioms vacancy_is_one_minus_occupation
#print axioms common_energy_reference

end Soma.Holonics.Physics.FermionicModeReceiver
