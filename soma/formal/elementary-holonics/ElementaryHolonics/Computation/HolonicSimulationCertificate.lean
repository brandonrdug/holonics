import ElementaryHolonics.Computation.HolonicEvolutionKinds
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Tactic

/-!
# Exact and bounded finite simulation certificates

**[proved-derived]** A finite simulation return carries its Hamiltonian, state, observable,
method, finite cutoff, and a decomposed nonnegative error budget.  The checker proves only the
predicate represented by that certificate.  Producer execution, backend behavior, experimental
calibration, and continuum reconstruction remain separate testimony.

The exact and approximate controls below use the same finite Hamiltonian and state.  The exact
candidate has zero residual; the approximate candidate has a checked residual mass of `1/16`.
-/

noncomputable section

namespace Soma.Holonics.Computation.HolonicSimulationCertificate

open scoped BigOperators ComplexConjugate Matrix

/-- [definition] Exterior numerical method lineage. -/
inductive SimulationMethod where
  | exactDiagonalization
  | krylov
  | determinantMonteCarlo
  | worldlineMonteCarlo
  | diagrammaticMonteCarlo
  | tensorNetwork
  | analogEmulator
  | digitalQuantum
  deriving DecidableEq

/-- [definition] Assurance layers must not be promoted across this boundary. -/
inductive AssuranceLayer where
  | leanTheorem
  | executableChecker
  | nativeRuntime
  | externalProducer
  deriving DecidableEq

/-- [definition] Decomposed nonnegative numerical/systematic testimony. -/
structure ErrorBudget where
  residual : ℝ
  truncation : ℝ
  rounding : ℝ
  stochastic : ℝ
  systematic : ℝ
  residual_nonnegative : 0 ≤ residual
  truncation_nonnegative : 0 ≤ truncation
  rounding_nonnegative : 0 ≤ rounding
  stochastic_nonnegative : 0 ≤ stochastic
  systematic_nonnegative : 0 ≤ systematic

namespace ErrorBudget

def total (budget : ErrorBudget) : ℝ :=
  budget.residual + budget.truncation + budget.rounding +
    budget.stochastic + budget.systematic

theorem total_nonnegative (budget : ErrorBudget) : 0 ≤ budget.total := by
  unfold total
  linarith [budget.residual_nonnegative, budget.truncation_nonnegative,
    budget.rounding_nonnegative, budget.stochastic_nonnegative,
    budget.systematic_nonnegative]

end ErrorBudget

variable {Index : Type*} [Fintype Index] [DecidableEq Index]

/-- [definition] Eigenpair residual in the declared finite basis. -/
def residual (hamiltonian : Matrix Index Index ℂ) (state : Index → ℂ) (energy : ℝ) :
    Index → ℂ :=
  fun index ↦ (hamiltonian *ᵥ state) index - (energy : ℂ) * state index

/-- [definition] Squared residual mass, after the complete residual vector is retained. -/
def residualMass (hamiltonian : Matrix Index Index ℂ) (state : Index → ℂ)
    (energy : ℝ) : ℝ :=
  ∑ index, Complex.normSq (residual hamiltonian state energy index)

/-- [definition] The energy observable face of one finite state. -/
def energyObservable (hamiltonian : Matrix Index Index ℂ) (state : Index → ℂ) : ℂ :=
  ∑ index, conj (state index) * (hamiltonian *ᵥ state) index

/-- [definition] A checked bounded eigenpair return. -/
structure EigenpairCertificate where
  method : SimulationMethod
  producerLayer : AssuranceLayer
  checkerLayer : AssuranceLayer
  hamiltonian : Matrix Index Index ℂ
  hamiltonianHermitian : hamiltonian.IsHermitian
  state : Index → ℂ
  energy : ℝ
  cutoff : ℕ
  error : ErrorBudget
  residual_checked : residualMass hamiltonian state energy ≤ error.residual

/-- The residual is bounded by the complete declared budget. -/
theorem EigenpairCertificate.residual_le_total
    (certificate : EigenpairCertificate (Index := Index)) :
    residualMass certificate.hamiltonian certificate.state certificate.energy ≤
      certificate.error.total := by
  exact certificate.residual_checked.trans <| by
    unfold ErrorBudget.total
    linarith [certificate.error.truncation_nonnegative,
      certificate.error.rounding_nonnegative, certificate.error.stochastic_nonnegative,
      certificate.error.systematic_nonnegative]

/-- [definition] TorchLean or another graph/tensor backend may provide this exterior metadata.  It
does not provide the Hamiltonian theorem or the certificate proof. -/
structure TensorGraphAdapterBoundary where
  shape : List ℕ
  nodeCount : ℕ
  producerLayer : AssuranceLayer
  checkerLayer : AssuranceLayer
  producer_external : producerLayer = AssuranceLayer.externalProducer
  checker_bounded : checkerLayer = AssuranceLayer.executableChecker ∨
    checkerLayer = AssuranceLayer.leanTheorem

/-! ## One common finite receiver with exact and approximate returns -/

abbrev OneIndex := Fin 1

def oneHamiltonian : Matrix OneIndex OneIndex ℂ := 1
def oneState : OneIndex → ℂ := fun _ ↦ 1

theorem oneHamiltonian_isHermitian : oneHamiltonian.IsHermitian := by
  exact Matrix.isHermitian_one

theorem oneEnergyObservable : energyObservable oneHamiltonian oneState = 1 := by
  norm_num [energyObservable, oneHamiltonian, oneState, Fin.sum_univ_one, Matrix.one_mulVec]

theorem exactResidual : residualMass oneHamiltonian oneState 1 = 0 := by
  norm_num [residualMass, residual, oneHamiltonian, oneState, Fin.sum_univ_one,
    Matrix.one_mulVec, Complex.normSq]

theorem approximateResidual : residualMass oneHamiltonian oneState (3 / 4) = 1 / 16 := by
  norm_num [residualMass, residual, oneHamiltonian, oneState, Fin.sum_univ_one,
    Matrix.one_mulVec, Complex.normSq]

def zeroBudget : ErrorBudget where
  residual := 0
  truncation := 0
  rounding := 0
  stochastic := 0
  systematic := 0
  residual_nonnegative := by norm_num
  truncation_nonnegative := by norm_num
  rounding_nonnegative := by norm_num
  stochastic_nonnegative := by norm_num
  systematic_nonnegative := by norm_num

def boundedBudget : ErrorBudget where
  residual := 1 / 16
  truncation := 0
  rounding := 0
  stochastic := 0
  systematic := 0
  residual_nonnegative := by norm_num
  truncation_nonnegative := by norm_num
  rounding_nonnegative := by norm_num
  stochastic_nonnegative := by norm_num
  systematic_nonnegative := by norm_num

def exactCertificate : EigenpairCertificate (Index := OneIndex) where
  method := .exactDiagonalization
  producerLayer := .leanTheorem
  checkerLayer := .leanTheorem
  hamiltonian := oneHamiltonian
  hamiltonianHermitian := oneHamiltonian_isHermitian
  state := oneState
  energy := 1
  cutoff := 1
  error := zeroBudget
  residual_checked := by rw [exactResidual]; rfl

def boundedCertificate : EigenpairCertificate (Index := OneIndex) where
  method := .krylov
  producerLayer := .externalProducer
  checkerLayer := .leanTheorem
  hamiltonian := oneHamiltonian
  hamiltonianHermitian := oneHamiltonian_isHermitian
  state := oneState
  energy := 3 / 4
  cutoff := 1
  error := boundedBudget
  residual_checked := by rw [approximateResidual]; rfl

/-- Exact and approximate apparatus returns are checked against the same Hamiltonian/state
observable without identifying their different residual grades. -/
theorem controls_share_observable_and_separate_residual :
    energyObservable exactCertificate.hamiltonian exactCertificate.state = 1 ∧
      energyObservable boundedCertificate.hamiltonian boundedCertificate.state = 1 ∧
      residualMass exactCertificate.hamiltonian exactCertificate.state exactCertificate.energy = 0 ∧
      residualMass boundedCertificate.hamiltonian boundedCertificate.state
        boundedCertificate.energy = 1 / 16 := by
  exact ⟨oneEnergyObservable, oneEnergyObservable, exactResidual, approximateResidual⟩

section Audit

#print axioms ErrorBudget.total_nonnegative
#print axioms EigenpairCertificate.residual_le_total
#print axioms oneHamiltonian_isHermitian
#print axioms oneEnergyObservable
#print axioms exactResidual
#print axioms approximateResidual
#print axioms controls_share_observable_and_separate_residual

end Audit

end Soma.Holonics.Computation.HolonicSimulationCertificate
