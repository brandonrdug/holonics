import Mathlib.Tactic
import Mathlib.Data.Complex.Basic
import Holonics.Foundation.SectionResidual

/-!
# A finite Hodge energy cut

This is a receiver ledger for a closed finite cycle.  It keeps the mixed harmonic/exact
term when a current is cut into pieces; no claim is made that a Hodge projection commutes
with an arbitrary cut.
-/

noncomputable section

namespace Holonics.Physics.PartitionedHodgeEnergy

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

/-! ## The same cut fails the heat consumer's commuting square

The differential below is the cyclic vertex-to-edge incidence; cycleBoundary
is its unit-metric adjoint. Thus the Laplacian is the actual incidence-adjoint
composition on this declared four-edge cycle, not an arbitrary operator chosen
to make a receiver fail. This is a finite closed cycle, with no continuum or
algebraic-cycle interpretation imposed on its cut.
-/

def cycleCoboundary (p : Edge → ℝ) (i : Edge) : ℝ := p (i + 1) - p i

def cycleLaplacian (v : Edge → ℝ) : Edge → ℝ :=
  cycleCoboundary (cycleBoundary v)

def cut (A : Finset Edge) (v : Edge → ℝ) : Edge → ℝ :=
  fun i => if i ∈ A then v i else 0

def cycleHeatStep (step : ℝ) (v : Edge → ℝ) : Edge → ℝ :=
  v - step • cycleLaplacian v

private theorem cycleIndex_neg_one : (-1 : Edge) = 3 := by decide

theorem cycleBoundary_is_adjoint (p v : Edge → ℝ) :
    (∑ i, cycleCoboundary p i * v i) = ∑ i, p i * cycleBoundary v i := by
  simp [cycleCoboundary, cycleBoundary, Fin.sum_univ_succ, cycleIndex_neg_one]
  ring

theorem cut_sub (A : Finset Edge) (v w : Edge → ℝ) :
    cut A (v - w) = cut A v - cut A w := by
  funext i
  by_cases hi : i ∈ A <;> simp [cut, hi]

theorem cut_smul (A : Finset Edge) (a : ℝ) (v : Edge → ℝ) :
    cut A (a • v) = a • cut A v := by
  funext i
  by_cases hi : i ∈ A <;> simp [cut, hi]

/-- The same heat/receiver return as the general temporal Hodge consumer,
specialized to actual cyclic incidence and its declared unit-metric adjoint. -/
theorem cycleHeatStep_cut_return (A : Finset Edge) (step : ℝ) (v : Edge → ℝ) :
    cut A (cycleHeatStep step v) = cycleHeatStep step (cut A v) +
      step • (cycleLaplacian (cut A v) - cut A (cycleLaplacian v)) := by
  simp only [cycleHeatStep, cut_sub, cut_smul, smul_sub]
  abel

theorem harmonicWitness_laplacian_zero : cycleLaplacian hWitness = 0 := by
  funext i
  simp [cycleLaplacian, cycleCoboundary, hWitness_boundary_zero]

/-- The source harmonic current is locally silent, but its cut creates a
seam return of 5/2. Reusing global harmonicity at the cut would erase it. -/
theorem cut_harmonic_laplacian_defect :
    (cycleLaplacian (cut leftCut hWitness) -
      cut leftCut (cycleLaplacian hWitness)) 0 = (5 / 2 : ℝ) := by
  norm_num [cycleLaplacian, cycleCoboundary, cycleBoundary, cut,
    leftCut, hWitness, cycleIndex_neg_one] <;> decide

/-- At any nonzero step the left cut and the declared Euler heat step fail
to commute. This supplies the fixed acceptance's exact falsifier. -/
theorem cut_heat_commutation_fails (step : ℝ) (hstep : step ≠ 0) :
    cut leftCut (cycleHeatStep step hWitness) ≠
      cycleHeatStep step (cut leftCut hWitness) := by
  intro heq
  have hr := congrFun (cycleHeatStep_cut_return leftCut step hWitness) 0
  have hc := congrFun heq 0
  have hd := cut_harmonic_laplacian_defect
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hr
  rw [hd, hc] at hr
  have hz : step * (5 / 2 : ℝ) = 0 := by linarith
  exact hstep ((mul_eq_zero.mp hz).resolve_right (by norm_num))

end Holonics.Physics.PartitionedHodgeEnergy

end

#print axioms Holonics.Physics.PartitionedHodgeEnergy.cycleBoundary_is_adjoint
#print axioms Holonics.Physics.PartitionedHodgeEnergy.cycleHeatStep_cut_return
#print axioms Holonics.Physics.PartitionedHodgeEnergy.cut_harmonic_laplacian_defect
#print axioms Holonics.Physics.PartitionedHodgeEnergy.cut_heat_commutation_fails

/-! ## The two-level nonlinear cut receiver

The same parked Hodge current consumes the generic section return in its
canonical owner. The original private importing receipt is retained; these
relocated source/import bytes require their own check. -/

noncomputable section
namespace Holonics.Physics.PartitionedHodgeEnergy.RecursiveCutReadout

open Holonics.Foundation.SectionResidual

def pairMeans : (Edge → ℝ) →ₗ[ℝ] (ℝ × ℝ) where
  toFun x := ((x 0 + x 1) / 2, (x 2 + x 3) / 2)
  map_add' := by intro x y; ext <;> simp <;> ring
  map_smul' := by intro a x; ext <;> simp <;> ring

def wholeMean : (ℝ × ℝ) →ₗ[ℝ] ℝ where
  toFun y := (y.1 + y.2) / 2
  map_add' := by intro x y; simp; ring
  map_smul' := by intro a x; simp; ring

def pairSection : Section pairMeans where
  value y := ![y.1, y.1, y.2, y.2]
  rightInverse := by intro y; ext <;> simp [pairMeans] <;> ring

def wholeSection : Section wholeMean where
  value a := (a, a)
  rightInverse := by intro a; simp [wholeMean] <;> ring

def cutEnergyRead (A : Finset Edge) (v : Edge → ℝ) : ℂ := pieceEnergy A v

/-- Two section returns for the actual nonlinear local energy receiver, using
the exact accepted theorem without imposing linearity on the energy reading. -/
theorem recursive_cut_energy_receiver (A : Finset Edge) (x : Edge → ℝ) :
    cutEnergyRead A x =
      cutEnergyRead A (pairSection.value
        (wholeSection.value (wholeMean (pairMeans x)))) +
      receiverDefect (cutEnergyRead A) pairSection x +
      receiverDefect (fun y => cutEnergyRead A (pairSection.value y))
        wholeSection (pairMeans x) :=
  two_level_receiver_defects (cutEnergyRead A) pairSection wholeSection x

def source : Edge → ℝ := ![1, 2, 3, 4]

@[simp] private theorem source_zero : source 0 = 1 := rfl
@[simp] private theorem source_one : source 1 = 2 := rfl
@[simp] private theorem source_two : source 2 = 3 := rfl
@[simp] private theorem source_three : source 3 = 4 := rfl

theorem source_is_parked_hodge_current : source = hWitness + eWitness := by
  funext i
  fin_cases i <;> norm_num [source, hWitness, eWitness]

/-- The two-level quotient retains the parked current's harmonic part. The
local energy returns are 1/2 and -8; dropping the latter gives the wrong cut. -/
theorem parked_cut_receipt :
    pairSection.value (wholeSection.value (wholeMean (pairMeans source))) = hWitness ∧
      cutEnergyRead leftCut source = (5 : ℂ) ∧
      cutEnergyRead leftCut hWitness = (25 / 2 : ℂ) ∧
      receiverDefect (cutEnergyRead leftCut) pairSection source = (1 / 2 : ℂ) ∧
      receiverDefect (fun y => cutEnergyRead leftCut (pairSection.value y))
        wholeSection (pairMeans source) = (-8 : ℂ) := by
  constructor
  · funext i
    fin_cases i <;> norm_num [pairSection, wholeSection, pairMeans, wholeMean,
      hWitness, Matrix.vecHead, Matrix.vecTail]
  · norm_num [cutEnergyRead, pieceEnergy, leftCut, hWitness,
      receiverDefect, remainder, pairSection, wholeSection, pairMeans, wholeMean,
      Matrix.vecHead, Matrix.vecTail]

/-- Reading the lower remainder alone gives energy 2. The actual translated
pivot return is -8. Its missing mixed term is exactly -10 from the parked cut. -/
theorem lower_remainder_energy_is_not_pivot_return :
    cutEnergyRead leftCut (pairSection.value
      (remainder wholeSection (pairMeans source))) = (2 : ℂ) ∧
      receiverDefect (fun y => cutEnergyRead leftCut (pairSection.value y))
        wholeSection (pairMeans source) = (-8 : ℂ) := by
  norm_num [cutEnergyRead, pieceEnergy, leftCut, receiverDefect,
    remainder, pairSection, wholeSection, pairMeans, wholeMean,
    Matrix.vecHead, Matrix.vecTail]

end Holonics.Physics.PartitionedHodgeEnergy.RecursiveCutReadout

#print axioms Holonics.Physics.PartitionedHodgeEnergy.RecursiveCutReadout.recursive_cut_energy_receiver
#print axioms Holonics.Physics.PartitionedHodgeEnergy.RecursiveCutReadout.parked_cut_receipt
#print axioms Holonics.Physics.PartitionedHodgeEnergy.RecursiveCutReadout.lower_remainder_energy_is_not_pivot_return
