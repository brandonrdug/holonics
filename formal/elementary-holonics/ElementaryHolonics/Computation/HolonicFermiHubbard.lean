import ElementaryHolonics.Computation.HolonicFermionicOccupation
import Mathlib.Data.Prod.Lex
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Finite local fermion operators and the Fermi--Hubbard Hamiltonian

**[proved-derived]** This file composes the finite occupation/CAR carrier into local number,
directed hopping, undirected bond, on-site interaction, total-number, and Fermi--Hubbard matrices.
Every physical bond is represented by a directed transport plus its returned adjoint.  On-site and
chemical terms remain diagonal receiver-local interactions.  The resulting finite Hamiltonian is
Hermitian and preserves the occupation-number sectors exactly.

No continuum limit, unitary time evolution, thermodynamic limit, stochastic sampler, or physical
calibration is asserted here.
-/

noncomputable section

namespace Soma.Holonics.Computation.HolonicFermiHubbard

open scoped BigOperators
open Soma.Holonics.Computation.HolonicFermionicOccupation

/-- [definition] The two addressed spin fibres of the first Hubbard chart.  `0` and `1` are chart
coordinates, not particle identities. -/
abbrev FermionSpin := Fin 2

def spinUp : FermionSpin := 0
def spinDown : FermionSpin := 1

/-- [definition] A lattice mode is a site together with its dependent spin fibre, presented in the
lexicographic order used only for Koszul signs. -/
abbrev FermionMode (Site : Type*) := Site ×ₗ FermionSpin

def fermionMode {Site : Type*} (site : Site) (spin : FermionSpin) : FermionMode Site :=
  toLex (site, spin)

/-- [definition] Matrix transport on the finite occupation carrier. -/
abbrev FockMatrix (Mode : Type*) [DecidableEq Mode] :=
  Matrix (Occupation Mode) (Occupation Mode) ℂ

variable {Mode : Type*} [Fintype Mode] [DecidableEq Mode] [LinearOrder Mode]

/-- [definition] One directed hop annihilates at `source` and creates at `target`. -/
def directedHopping (target source : Mode) : FockMatrix Mode :=
  creationMatrix target * annihilationMatrix source

/-- [definition] A physical undirected bond retains both oriented hopping passages. -/
def bondHopping (left right : Mode) : FockMatrix Mode :=
  directedHopping left right + (directedHopping left right).conjTranspose

/-- Every bond hopping matrix is Hermitian by construction, without identifying its two directed
passages. -/
theorem bondHopping_isHermitian (left right : Mode) :
    (bondHopping left right).IsHermitian := by
  exact Matrix.isHermitian_add_transpose_self (directedHopping left right)

/-- [definition] The local occupation-number receiver at one mode. -/
def numberMatrix (mode : Mode) : FockMatrix Mode :=
  Matrix.diagonal fun occupation ↦ if mode ∈ occupation then (1 : ℂ) else 0

/-- Local occupation number is Hermitian. -/
theorem numberMatrix_isHermitian (mode : Mode) : (numberMatrix mode).IsHermitian := by
  rw [numberMatrix, Matrix.isHermitian_diagonal_iff]
  intro occupation
  by_cases occupied : mode ∈ occupation <;> simp [occupied]

/-- [definition] The total-number operator is diagonal in the occupation chart. -/
def totalNumberMatrix : FockMatrix Mode :=
  Matrix.diagonal fun occupation ↦ (occupation.card : ℂ)

/-- Total occupation number is Hermitian. -/
theorem totalNumberMatrix_isHermitian :
    (totalNumberMatrix (Mode := Mode)).IsHermitian := by
  rw [totalNumberMatrix, Matrix.isHermitian_diagonal_iff]
  intro occupation
  simp

/-- [definition] A finite lattice supplies typed bond endpoints.  Parallel bonds remain distinct
occurrences and may carry separate later coefficients. -/
structure FiniteLattice (Site Bond : Type*) where
  left : Bond → Site
  right : Bond → Site

variable {Site Bond : Type*}
  [Fintype Site] [DecidableEq Site] [LinearOrder Site]
  [Fintype Bond]

/-- [definition] Double occupation at one site. -/
def doubleOccupationMatrix (site : Site) : FockMatrix (FermionMode Site) :=
  Matrix.diagonal fun occupation ↦
    if fermionMode site spinUp ∈ occupation ∧
        fermionMode site spinDown ∈ occupation then (1 : ℂ) else 0

/-- On-site double occupation is Hermitian. -/
theorem doubleOccupationMatrix_isHermitian (site : Site) :
    (doubleOccupationMatrix site).IsHermitian := by
  rw [doubleOccupationMatrix, Matrix.isHermitian_diagonal_iff]
  intro occupation
  by_cases occupied : fermionMode site spinUp ∈ occupation ∧
      fermionMode site spinDown ∈ occupation <;> simp [occupied]

/-- A declared doubly occupied site returns unit on-site interaction. -/
theorem doubleOccupationMatrix_self_eq_one (site : Site) (occupation : Occupation (FermionMode Site))
    (upOccupied : fermionMode site spinUp ∈ occupation)
    (downOccupied : fermionMode site spinDown ∈ occupation) :
    doubleOccupationMatrix site occupation occupation = 1 := by
  simp [doubleOccupationMatrix, upOccupied, downOccupied]

/-- Finite sums of Hermitian occupation transports remain Hermitian. -/
theorem sum_isHermitian {Index : Type*} [Fintype Index]
    (operator : Index → FockMatrix Mode)
    (hermitian : ∀ index, (operator index).IsHermitian) :
    (∑ index, operator index).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_sum]
  apply Finset.sum_congr rfl
  intro index _
  exact hermitian index

/-- [definition] The symmetric kinetic passage over every typed bond and spin fibre. -/
def kineticHamiltonian (lattice : FiniteLattice Site Bond) :
    FockMatrix (FermionMode Site) :=
  ∑ bond : Bond, ∑ spin : FermionSpin,
    bondHopping (fermionMode (lattice.left bond) spin)
      (fermionMode (lattice.right bond) spin)

/-- The symmetric kinetic passage is Hermitian. -/
theorem kineticHamiltonian_isHermitian (lattice : FiniteLattice Site Bond) :
    (kineticHamiltonian lattice).IsHermitian := by
  apply sum_isHermitian
  intro bond
  apply sum_isHermitian
  intro spin
  exact bondHopping_isHermitian _ _

/-- [definition] The sum of on-site two-spin interactions. -/
def interactionHamiltonian : FockMatrix (FermionMode Site) :=
  ∑ site : Site, doubleOccupationMatrix site

/-- The unscaled on-site interaction passage is Hermitian. -/
theorem interactionHamiltonian_isHermitian :
    (interactionHamiltonian (Site := Site)).IsHermitian := by
  apply sum_isHermitian
  exact doubleOccupationMatrix_isHermitian

/-- [definition] Real coefficients of the finite Fermi--Hubbard receiver. -/
structure Parameters where
  hopping : ℝ
  interaction : ℝ
  chemicalPotential : ℝ

/-- [definition] The finite Fermi--Hubbard Hamiltonian. -/
def hamiltonian (lattice : FiniteLattice Site Bond) (parameters : Parameters) :
    FockMatrix (FermionMode Site) :=
  (-(parameters.hopping : ℂ)) • kineticHamiltonian lattice +
    (parameters.interaction : ℂ) • interactionHamiltonian +
    (-(parameters.chemicalPotential : ℂ)) • totalNumberMatrix

/-- The finite Fermi--Hubbard Hamiltonian is Hermitian for every real parameter population. -/
theorem hamiltonian_isHermitian
  (lattice : FiniteLattice Site Bond) (parameters : Parameters) :
    (hamiltonian lattice parameters).IsHermitian := by
  apply Matrix.IsHermitian.add
  · apply Matrix.IsHermitian.add
    · apply (kineticHamiltonian_isHermitian lattice).smul
      simp [isSelfAdjoint_iff]
    · apply (interactionHamiltonian_isHermitian (Site := Site)).smul
      simp [isSelfAdjoint_iff]
  · apply (totalNumberMatrix_isHermitian (Mode := FermionMode Site)).smul
    simp [isSelfAdjoint_iff]

/-! ## Exact particle-number sector law -/

/-- [definition] A matrix preserves particle number when it has no coefficient between distinct
occupation-cardinality sectors. -/
def PreservesParticleNumber (operator : FockMatrix Mode) : Prop :=
  ∀ target source, target.card ≠ source.card → operator target source = 0

/-- A nonzero creation coefficient determines its insertion endpoints exactly. -/
theorem creationMatrix_support (mode : Mode) (target source : Occupation Mode)
    (nonzero : creationMatrix mode target source ≠ 0) :
    mode ∉ source ∧ target = insert mode source := by
  by_cases support : mode ∉ source ∧ target = insert mode source
  · exact support
  · exact (nonzero (by simp [HolonicFermionicOccupation.creationMatrix, support])).elim

/-- A nonzero annihilation coefficient determines its erasure endpoints exactly. -/
theorem annihilationMatrix_support (mode : Mode) (target source : Occupation Mode)
    (nonzero : annihilationMatrix mode target source ≠ 0) :
    mode ∈ source ∧ target = source.erase mode := by
  by_cases support : mode ∈ source ∧ target = source.erase mode
  · exact support
  · exact (nonzero (by simp [HolonicFermionicOccupation.annihilationMatrix, support])).elim

/-- One creation after one annihilation preserves occupation cardinality. -/
theorem directedHopping_preservesParticleNumber (targetMode sourceMode : Mode) :
    PreservesParticleNumber (directedHopping targetMode sourceMode) := by
  intro target source separated
  rw [directedHopping, Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro middle _
  by_cases creationZero : creationMatrix targetMode target middle = 0
  · simp [creationZero]
  by_cases annihilationZero : annihilationMatrix sourceMode middle source = 0
  · simp [annihilationZero]
  have creationSupport := creationMatrix_support targetMode target middle creationZero
  have annihilationSupport :=
    annihilationMatrix_support sourceMode middle source annihilationZero
  have targetCard : target.card = middle.card + 1 := by
    rw [creationSupport.2]
    simp [creationSupport.1]
  have sourceCard : source.card = middle.card + 1 := by
    simpa [annihilationSupport.2] using
      (Finset.card_erase_add_one annihilationSupport.1).symm
  exact (separated (targetCard.trans sourceCard.symm)).elim

/-- Particle-number preservation is closed under addition. -/
theorem PreservesParticleNumber.add {left right : FockMatrix Mode}
    (leftPreserves : PreservesParticleNumber left)
    (rightPreserves : PreservesParticleNumber right) :
    PreservesParticleNumber (left + right) := by
  intro target source separated
  simp [leftPreserves target source separated, rightPreserves target source separated]

/-- Particle-number preservation is closed under scalar multiplication. -/
theorem PreservesParticleNumber.smul (scalar : ℂ) {operator : FockMatrix Mode}
    (preserves : PreservesParticleNumber operator) :
    PreservesParticleNumber (scalar • operator) := by
  intro target source separated
  simp [preserves target source separated]

/-- Conjugate transpose reverses the endpoints without changing their particle numbers. -/
theorem PreservesParticleNumber.conjTranspose {operator : FockMatrix Mode}
    (preserves : PreservesParticleNumber operator) :
    PreservesParticleNumber operator.conjTranspose := by
  intro target source separated
  simp [Matrix.conjTranspose_apply, preserves source target (Ne.symm separated)]

/-- Finite sums preserve the declared number sectors termwise. -/
theorem preservesParticleNumber_sum {Index : Type*} [Fintype Index]
    (operator : Index → FockMatrix Mode)
    (preserves : ∀ index, PreservesParticleNumber (operator index)) :
    PreservesParticleNumber (∑ index, operator index) := by
  intro target source separated
  simp only [Matrix.sum_apply]
  apply Finset.sum_eq_zero
  intro index _
  exact preserves index target source separated

/-- A physical two-way bond preserves particle number. -/
theorem bondHopping_preservesParticleNumber (left right : Mode) :
    PreservesParticleNumber (bondHopping left right) :=
  (directedHopping_preservesParticleNumber left right).add
    (directedHopping_preservesParticleNumber left right).conjTranspose

/-- Every diagonal occupation operator preserves particle number. -/
theorem diagonal_preservesParticleNumber (diagonal : Occupation Mode → ℂ) :
    PreservesParticleNumber (Matrix.diagonal diagonal) := by
  intro target source separated
  by_cases equal : target = source
  · subst source
    exact (separated rfl).elim
  · simp [Matrix.diagonal, equal]

/-- The full finite Fermi--Hubbard Hamiltonian preserves particle-number sectors. -/
theorem hamiltonian_preservesParticleNumber
    (lattice : FiniteLattice Site Bond) (parameters : Parameters) :
    PreservesParticleNumber (hamiltonian lattice parameters) := by
  apply PreservesParticleNumber.add
  · apply PreservesParticleNumber.add
    · apply PreservesParticleNumber.smul
      apply preservesParticleNumber_sum
      intro bond
      apply preservesParticleNumber_sum
      intro spin
      exact bondHopping_preservesParticleNumber _ _
    · apply PreservesParticleNumber.smul
      apply preservesParticleNumber_sum
      intro site
      exact diagonal_preservesParticleNumber _
  · apply PreservesParticleNumber.smul
    exact diagonal_preservesParticleNumber _

/-! ## Two-site exact control -/

/-- [definition] The smallest nontrivial spatial lattice has one typed bond from site zero to site
one; the bond Hamiltonian itself retains both orientations. -/
def twoSiteLattice : FiniteLattice (Fin 2) Unit where
  left _ := 0
  right _ := 1

/-- [definition] A nonzero hopping and interaction control with no chemical term. -/
def twoSiteParameters : Parameters where
  hopping := 1
  interaction := 1
  chemicalPotential := 0

/-- [definition] The exact finite Hamiltonian matrix returned by the two-site control. -/
def twoSiteHamiltonian : FockMatrix (FermionMode (Fin 2)) :=
  hamiltonian twoSiteLattice twoSiteParameters

/-- The concrete two-site Hamiltonian is Hermitian. -/
theorem twoSiteHamiltonian_isHermitian : twoSiteHamiltonian.IsHermitian :=
  hamiltonian_isHermitian twoSiteLattice twoSiteParameters

/-- The concrete two-site Hamiltonian preserves every occupation-number sector. -/
theorem twoSiteHamiltonian_preservesParticleNumber :
    PreservesParticleNumber twoSiteHamiltonian :=
  hamiltonian_preservesParticleNumber twoSiteLattice twoSiteParameters

def leftUpMode : FermionMode (Fin 2) := fermionMode 0 spinUp
def rightUpMode : FermionMode (Fin 2) := fermionMode 1 spinUp

/-- One directed hopping passage moves the declared one-particle occupation with unit amplitude. -/
theorem twoSite_hopping_is_nontrivial :
    create rightUpMode
        (annihilate leftUpMode
          (create leftUpMode (vacuum (Mode := FermionMode (Fin 2))))) {rightUpMode} = 1 := by
  have same := annihilate_create_add_create_annihilate_same
    leftUpMode (vacuum (Mode := FermionMode (Fin 2)))
  have reduced :
      annihilate leftUpMode
          (create leftUpMode (vacuum (Mode := FermionMode (Fin 2)))) =
        vacuum (Mode := FermionMode (Fin 2)) := by
    simpa [annihilate_vacuum] using same
  rw [reduced]
  exact create_vacuum_singleton rightUpMode

def leftDoubleOccupation : Occupation (FermionMode (Fin 2)) :=
  {fermionMode 0 spinUp, fermionMode 0 spinDown}

/-- The same finite control has a nonzero local two-spin interaction face. -/
theorem twoSite_interaction_is_nontrivial :
    doubleOccupationMatrix (0 : Fin 2) leftDoubleOccupation leftDoubleOccupation = 1 := by
  apply doubleOccupationMatrix_self_eq_one
  · simp [leftDoubleOccupation]
  · simp [leftDoubleOccupation]

section Audit

#print axioms bondHopping_isHermitian
#print axioms numberMatrix_isHermitian
#print axioms totalNumberMatrix_isHermitian
#print axioms kineticHamiltonian_isHermitian
#print axioms interactionHamiltonian_isHermitian
#print axioms hamiltonian_isHermitian
#print axioms directedHopping_preservesParticleNumber
#print axioms hamiltonian_preservesParticleNumber
#print axioms twoSiteHamiltonian_isHermitian
#print axioms twoSiteHamiltonian_preservesParticleNumber
#print axioms twoSite_hopping_is_nontrivial
#print axioms twoSite_interaction_is_nontrivial

end Audit

end Soma.Holonics.Computation.HolonicFermiHubbard
