import Mathlib.Tactic
import Mathlib.Data.Complex.Basic

/-!
# A finite Hodge energy cut

This is a receiver ledger for a closed finite cycle.  It keeps the mixed harmonic/exact
term when a current is cut into pieces; no claim is made that a Hodge projection commutes
with an arbitrary cut.
-/

noncomputable section

namespace Soma.Holonics.Physics.PartitionedHodgeEnergy

open scoped BigOperators

/-! Arbitrary finite complex sections retain the same phase-sensitive cut term. -/
namespace ComplexSection

def energy {Index : Type*} (A : Finset Index) (v : Index → ℂ) : ℝ :=
  ∑ i ∈ A, Complex.normSq (v i)

def mixed {Index : Type*} (A : Finset Index) (h e : Index → ℂ) : ℝ :=
  ∑ i ∈ A, 2 * (h i * star (e i)).re

theorem energy_add {Index : Type*} (A : Finset Index) (h e : Index → ℂ) :
    energy A (h + e) = energy A h + energy A e + mixed A h e := by
  simp [energy, mixed, Complex.normSq_add, Finset.sum_add_distrib]

theorem mixed_union {Index : Type*} [DecidableEq Index]
    (A B : Finset Index) (h e : Index → ℂ) (hdis : Disjoint A B) :
    mixed (A ∪ B) h e = mixed A h e + mixed B h e := by
  exact Finset.sum_union hdis

theorem orthogonal_union_has_opposite_cut_terms {Index : Type*} [DecidableEq Index]
    (A B : Finset Index) (h e : Index → ℂ) (hdis : Disjoint A B)
    (horth : mixed (A ∪ B) h e = 0) : mixed A h e = -mixed B h e := by
  rw [mixed_union A B h e hdis] at horth
  linarith

end ComplexSection

abbrev Edge := Fin 4

def energy {Index : Type*} [Fintype Index] (v : Index → ℝ) : ℝ := ∑ i, v i ^ 2

def crossEnergy {Index : Type*} [Fintype Index] (h e : Index → ℝ) : ℝ := ∑ i, 2 * h i * e i

def pieceEnergy {Index : Type*} (A : Finset Index) (v : Index → ℝ) : ℝ := A.sum (fun i => v i ^ 2)

def pieceCross {Index : Type*} (A : Finset Index) (h e : Index → ℝ) : ℝ :=
  A.sum (fun i => 2 * h i * e i)

theorem energy_add {Index : Type*} [Fintype Index] (h e : Index → ℝ) :
    energy (h + e) = energy h + energy e + crossEnergy h e := by
  simp only [energy, crossEnergy, Pi.add_apply, add_pow_two]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  ring

theorem pieceEnergy_add {Index : Type*} (A : Finset Index) (h e : Index → ℝ) :
    pieceEnergy A (h + e) = pieceEnergy A h + pieceEnergy A e + pieceCross A h e := by
  simp only [pieceEnergy, pieceCross, Pi.add_apply, add_pow_two]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  ring

def hWitness : Edge → ℝ := fun _ => 5 / 2

def eWitness : Edge → ℝ := fun i =>
  if i.val = 0 then -3 / 2 else if i.val = 1 then -1 / 2 else if i.val = 2 then 1 / 2 else 3 / 2

def potentialWitness : Edge → ℝ := fun i =>
  if i.val = 0 then 0 else if i.val = 1 then -3 / 2 else if i.val = 2 then -2 else -3 / 2

def leftCut : Finset Edge := {0, 1}

def rightCut : Finset Edge := {2, 3}

theorem eWitness_is_cyclic_gradient :
    eWitness 0 = potentialWitness 1 - potentialWitness 0 ∧
    eWitness 1 = potentialWitness 2 - potentialWitness 1 ∧
    eWitness 2 = potentialWitness 3 - potentialWitness 2 ∧
    eWitness 3 = potentialWitness 0 - potentialWitness 3 := by
  have e0 : eWitness 0 = -(3 / 2 : ℝ) := by norm_num [eWitness]
  have e1 : eWitness 1 = -(1 / 2 : ℝ) := by norm_num [eWitness]
  have e2 : eWitness 2 = (1 / 2 : ℝ) := by norm_num [eWitness]
  have e3 : eWitness 3 = (3 / 2 : ℝ) := by norm_num [eWitness]
  have p0 : potentialWitness 0 = (0 : ℝ) := by norm_num [potentialWitness]
  have p1 : potentialWitness 1 = -(3 / 2 : ℝ) := by norm_num [potentialWitness]
  have p2 : potentialWitness 2 = (-2 : ℝ) := by norm_num [potentialWitness]
  have p3 : potentialWitness 3 = -(3 / 2 : ℝ) := by norm_num [potentialWitness]
  simp [e0, e1, e2, e3, p0, p1, p2, p3] <;> norm_num

def cycleBoundary (v : Edge → ℝ) (i : Edge) : ℝ := v (i - 1) - v i

theorem hWitness_boundary_zero (i : Edge) : cycleBoundary hWitness i = 0 := by
  fin_cases i <;> norm_num [cycleBoundary, hWitness]

theorem leftCut_boundary_is_nonzero :
    cycleBoundary (fun i => if i ∈ leftCut then hWitness i else 0) 0 = -(5 / 2 : ℝ) := by
  norm_num [cycleBoundary, leftCut, hWitness] <;> norm_num <;> decide

theorem cut_boundaries_cancel (i : Edge) :
    cycleBoundary (fun j => if j ∈ leftCut then hWitness j else 0) i +
      cycleBoundary (fun j => if j ∈ rightCut then hWitness j else 0) i = 0 := by
  have hu : leftCut ∪ rightCut = Finset.univ := by decide
  have hd : Disjoint leftCut rightCut := by decide
  have hc (j : Edge) :
      (if j ∈ leftCut then hWitness j else 0) +
        (if j ∈ rightCut then hWitness j else 0) = hWitness j := by
    by_cases hl : j ∈ leftCut
    · have hr : j ∉ rightCut := fun hr => Finset.disjoint_left.mp hd hl hr
      simp [hl, hr]
    · have hm : j ∈ leftCut ∪ rightCut := by rw [hu]; simp
      have hr : j ∈ rightCut := by simpa [hl] using hm
      simp [hl, hr]
  have hprev := hc (i - 1)
  have hhere := hc i
  have hz := hWitness_boundary_zero i
  unfold cycleBoundary at hz ⊢
  linarith

theorem witness_total_energy : energy (hWitness + eWitness) = 30 := by
  norm_num [energy, hWitness, eWitness, Fin.sum_univ_succ, Pi.add_apply]

theorem witness_component_energies :
    energy hWitness = 25 ∧ energy eWitness = 5 := by
  norm_num [energy, hWitness, eWitness, Fin.sum_univ_succ]

theorem witness_cut_energies :
    pieceEnergy leftCut (hWitness + eWitness) = 5 ∧
    pieceEnergy rightCut (hWitness + eWitness) = 25 := by
  have h0 : hWitness 0 = (5 / 2 : ℝ) := by norm_num [hWitness]
  have h1 : hWitness 1 = (5 / 2 : ℝ) := by norm_num [hWitness]
  have e0 : eWitness 0 = -(3 / 2 : ℝ) := by norm_num [eWitness]
  have e1 : eWitness 1 = -(1 / 2 : ℝ) := by norm_num [eWitness]
  have h2 : hWitness 2 = (5 / 2 : ℝ) := by norm_num [hWitness]
  have h3 : hWitness 3 = (5 / 2 : ℝ) := by norm_num [hWitness]
  have e2 : eWitness 2 = (1 / 2 : ℝ) := by norm_num [eWitness]
  have e3 : eWitness 3 = (3 / 2 : ℝ) := by norm_num [eWitness]
  simp [pieceEnergy, leftCut, rightCut, Finset.sum_insert, h0, h1, e0, e1, h2, h3, e2, e3] <;> norm_num

theorem witness_cut_component_energies :
    pieceEnergy leftCut hWitness = 25 / 2 ∧
    pieceEnergy leftCut eWitness = 5 / 2 ∧
    pieceEnergy rightCut hWitness = 25 / 2 ∧
    pieceEnergy rightCut eWitness = 5 / 2 := by
  have h0 : hWitness 0 = (5 / 2 : ℝ) := by norm_num [hWitness]
  have h1 : hWitness 1 = (5 / 2 : ℝ) := by norm_num [hWitness]
  have h2 : hWitness 2 = (5 / 2 : ℝ) := by norm_num [hWitness]
  have h3 : hWitness 3 = (5 / 2 : ℝ) := by norm_num [hWitness]
  have e0 : eWitness 0 = -(3 / 2 : ℝ) := by norm_num [eWitness]
  have e1 : eWitness 1 = -(1 / 2 : ℝ) := by norm_num [eWitness]
  have e2 : eWitness 2 = (1 / 2 : ℝ) := by norm_num [eWitness]
  have e3 : eWitness 3 = (3 / 2 : ℝ) := by norm_num [eWitness]
  simp [pieceEnergy, leftCut, rightCut, Finset.sum_insert, h0, h1, h2, h3,
    e0, e1, e2, e3] <;> norm_num

theorem witness_cut_cross_defects :
    pieceCross leftCut hWitness eWitness = -10 ∧
    pieceCross rightCut hWitness eWitness = 10 := by
  have h0 : hWitness 0 = (5 / 2 : ℝ) := by norm_num [hWitness]
  have h1 : hWitness 1 = (5 / 2 : ℝ) := by norm_num [hWitness]
  have h2 : hWitness 2 = (5 / 2 : ℝ) := by norm_num [hWitness]
  have h3 : hWitness 3 = (5 / 2 : ℝ) := by norm_num [hWitness]
  have e0 : eWitness 0 = -(3 / 2 : ℝ) := by norm_num [eWitness]
  have e1 : eWitness 1 = -(1 / 2 : ℝ) := by norm_num [eWitness]
  have e2 : eWitness 2 = (1 / 2 : ℝ) := by norm_num [eWitness]
  have e3 : eWitness 3 = (3 / 2 : ℝ) := by norm_num [eWitness]
  simp [pieceCross, leftCut, rightCut, Finset.sum_insert, h0, h1, h2, h3,
    e0, e1, e2, e3] <;> norm_num

theorem witness_cross_terms_cancel :
    pieceCross leftCut hWitness eWitness + pieceCross rightCut hWitness eWitness = 0 := by
  obtain ⟨hl, hr⟩ := witness_cut_cross_defects
  rw [hl, hr]
  norm_num

theorem witness_cut_ledger_retains_mixed_term :
    pieceEnergy leftCut (hWitness + eWitness) =
        pieceEnergy leftCut hWitness + pieceEnergy leftCut eWitness +
          pieceCross leftCut hWitness eWitness ∧
    pieceEnergy rightCut (hWitness + eWitness) =
        pieceEnergy rightCut hWitness + pieceEnergy rightCut eWitness +
          pieceCross rightCut hWitness eWitness := by
  constructor <;> exact pieceEnergy_add _ _ _

end Soma.Holonics.Physics.PartitionedHodgeEnergy

end
