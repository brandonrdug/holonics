import ElementaryHolonics.Millennium.Chronology
import ElementaryHolonics.Millennium.HolonicDifferenceCalculus
import Mathlib.Algebra.DualNumber
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Constructive differential, boundary, and receiver calculus

This owner replaces the informal instruction “multiply by `dx`” with an explicit square-zero
carrier or a linear differential evaluated on a typed tangent.  Finite integration is the exact
telescoping of those returned local differences.  A lower-dimensional receiver retains its kernel,
and a vanishing receiver face never silently erases the residue behind it.

The construction uses ordinary Mathlib dual numbers.  It adds no Kock--Lawvere, nonstandard-real,
or paraconsistent axiom.
-/

namespace Soma.Holonics.Computation.HolonicConstructiveDifferentialBoundary

open Filter Set
open scoped BigOperators Topology

/-! ## 1. A first-order factor is a typed square-zero carrier -/

section DualJet

variable {R : Type*} [Ring R]

/-- The explicit first-order occurrence `base + tangent ε`. -/
def firstOrderJet (base tangent : R) : DualNumber R :=
  TrivSqZeroExt.inl base + TrivSqZeroExt.inr tangent

@[simp] theorem firstOrderJet_standardFace (base tangent : R) :
    TrivSqZeroExt.fst (firstOrderJet base tangent) = base := by
  simp [firstOrderJet]

@[simp] theorem firstOrderJet_residue (base tangent : R) :
    TrivSqZeroExt.snd (firstOrderJet base tangent) = tangent := by
  simp [firstOrderJet]

/-- The infinitesimal basis is square-zero; it is not thereby an invertible scalar factor. -/
theorem infinitesimal_square_zero :
    (DualNumber.eps : DualNumber R) ^ 2 = 0 :=
  DualNumber.eps_pow_two

/-- Multiplication of first-order occurrences returns the exact Leibniz coefficient. -/
theorem firstOrderJet_product_residue (left dleft right dright : R) :
    TrivSqZeroExt.snd (firstOrderJet left dleft * firstOrderJet right dright) =
      left * dright + dleft * right := by
  simp

/-- Both faces together reconstruct the complete first-order carrier. -/
def completeJetReceiver (carrier : DualNumber R) : R × R :=
  (TrivSqZeroExt.fst carrier, TrivSqZeroExt.snd carrier)

omit [Ring R] in
theorem completeJetReceiver_injective : Function.Injective (completeJetReceiver (R := R)) := by
  intro left right hequal
  apply TrivSqZeroExt.ext
  · exact congrArg Prod.fst hequal
  · exact congrArg Prod.snd hequal

/-- A standard face may be zero while its retained differential residue is nonzero. -/
theorem pureInfinitesimal_has_zeroFace_and_nonzeroResidue {tangent : R}
    (htangent : tangent ≠ 0) :
    TrivSqZeroExt.fst (TrivSqZeroExt.inr tangent : DualNumber R) = 0 ∧
      TrivSqZeroExt.snd (TrivSqZeroExt.inr tangent : DualNumber R) = tangent ∧
      (TrivSqZeroExt.inr tangent : DualNumber R) ≠ 0 := by
  constructor
  · simp
  constructor
  · simp
  · intro hzero
    have hsnd := congrArg TrivSqZeroExt.snd hzero
    simpa using htangent hsnd

end DualJet

/-! ## 2. Typed local differentials integrate to the addressed boundary -/

section ExactPath

open Soma.Holonics.Millennium.HolonicDifferenceCalculus

variable {Scalar Tangent Value Face : Type*}
variable [Semiring Scalar]
variable [AddCommMonoid Tangent] [Module Scalar Tangent]
variable [AddCommGroup Value] [Module Scalar Value]
variable [AddCommGroup Face] [Module Scalar Face]

/-- A chronological path whose local differences are returned by one bundled linear differential. -/
structure ExactDifferentialPath (steps : ℕ) where
  point : ℕ → Value
  tangent : ℕ → Tangent
  differential : Tangent →ₗ[Scalar] Value
  localLaw : ∀ time, time < steps →
    firstDifference point time = differential (tangent time)

/-- The tangent population retained before its endpoint receiver is applied. -/
def ExactDifferentialPath.integratedTangent {steps : ℕ}
    (path : ExactDifferentialPath (Scalar := Scalar) (Tangent := Tangent)
      (Value := Value) steps) : Tangent :=
  ∑ time ∈ Finset.range steps, path.tangent time

/-- Finite FTC: the integrated typed differential is exactly the endpoint difference. -/
theorem ExactDifferentialPath.integratesToBoundary {steps : ℕ}
    (path : ExactDifferentialPath (Scalar := Scalar) (Tangent := Tangent)
      (Value := Value) steps) :
    path.differential path.integratedTangent = path.point steps - path.point 0 := by
  calc
    path.differential path.integratedTangent =
        ∑ time ∈ Finset.range steps, path.differential (path.tangent time) := by
      simp [ExactDifferentialPath.integratedTangent]
    _ = ∑ time ∈ Finset.range steps, firstDifference path.point time := by
      apply Finset.sum_congr rfl
      intro time htime
      exact (path.localLaw time (Finset.mem_range.mp htime)).symm
    _ = path.point steps - path.point 0 :=
      localDifferences_integrateToBoundary path.point steps

/-- A linear receiver sees the same FTC boundary without becoming the complete carrier. -/
theorem ExactDifferentialPath.receiverIntegratesToBoundary {steps : ℕ}
    (path : ExactDifferentialPath (Scalar := Scalar) (Tangent := Tangent)
      (Value := Value) steps)
    (receiver : Value →ₗ[Scalar] Face) :
    receiver (path.differential path.integratedTangent) =
      receiver (path.point steps) - receiver (path.point 0) := by
  rw [path.integratesToBoundary, map_sub]

/-- Scaling a tangent is an explicit module action, not untyped multiplication by `dx`. -/
theorem differential_scale {steps : ℕ}
    (path : ExactDifferentialPath (Scalar := Scalar) (Tangent := Tangent)
      (Value := Value) steps)
    (scale : Scalar) (tangent : Tangent) :
    path.differential (scale • tangent) = scale • path.differential tangent := by
  exact path.differential.map_smul scale tangent

end ExactPath

/-! ## 3. A lower-dimensional face retains its complete reconstruction fibre -/

section ReceiverFibre

variable {R Ambient Face : Type*}
variable [Ring R]
variable [AddCommGroup Ambient] [Module R Ambient]
variable [AddCommGroup Face] [Module R Face]

/-- A declared lower-dimensional linear chart on a higher-dimensional carrier. -/
structure HigherDimensionalReceiver where
  shadow : Ambient →ₗ[R] Face

/-- All occurrences which the declared face alone cannot distinguish. -/
def HigherDimensionalReceiver.ReconstructionFibre
    (receiver : HigherDimensionalReceiver (R := R) (Ambient := Ambient) (Face := Face))
    (face : Face) :=
  {occurrence : Ambient // receiver.shadow occurrence = face}

/-- Equal shadows identify precisely a difference in the receiver kernel, not source equality. -/
theorem HigherDimensionalReceiver.equalShadow_iff_difference_mem_kernel
    (receiver : HigherDimensionalReceiver (R := R) (Ambient := Ambient) (Face := Face))
    (left right : Ambient) :
    receiver.shadow left = receiver.shadow right ↔
      left - right ∈ LinearMap.ker receiver.shadow := by
  change receiver.shadow left = receiver.shadow right ↔ receiver.shadow (left - right) = 0
  rw [map_sub, sub_eq_zero]

end ReceiverFibre

/-! ## 4. Refinement does not erase integrated potential -/

/-- One cell of the exact `n + 1` partition of unit potential. -/
noncomputable def radixCellPotential (n : ℕ) : ℝ :=
  1 / ((n : ℝ) + 1)

/-- The integrated population of all cells, retained before any pointwise limit. -/
noncomputable def radixTotalPotential (n : ℕ) : ℝ :=
  ∑ _cell : Fin (n + 1), radixCellPotential n

theorem radixTotalPotential_eq_one (n : ℕ) : radixTotalPotential n = 1 := by
  have hdenominator : (n : ℝ) + 1 ≠ 0 := by positivity
  simp [radixTotalPotential, radixCellPotential, hdenominator]

theorem radixCellPotential_tendsto_zero :
    Tendsto radixCellPotential atTop (𝓝 0) := by
  exact tendsto_one_div_add_atTop_nhds_zero_nat

/-- The pointwise cell limit and the integrated boundary return are simultaneously exact. -/
theorem refinement_cell_vanishes_but_total_remains :
    Tendsto radixCellPotential atTop (𝓝 0) ∧
      ∀ n, radixTotalPotential n = 1 :=
  ⟨radixCellPotential_tendsto_zero, radixTotalPotential_eq_one⟩

/-! ## 5. Mean-value and squeeze receivers carry their hypotheses -/

/-- The interior occurrence supplied by the classical mean-value theorem. -/
structure MeanValueWitness (f f' : ℝ → ℝ) (a b : ℝ) where
  point : ℝ
  interior : point ∈ Ioo a b
  derivative : HasDerivAt f (f' point) point
  meanRate : f' point = (f b - f a) / (b - a)

/-- Construct the witness only from continuity, interior differentiability, and ordered endpoints. -/
theorem meanValueWitness_of_hypotheses {f f' : ℝ → ℝ} {a b : ℝ}
    (hab : a < b)
    (continuous : ContinuousOn f (Icc a b))
    (differentiable : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) :
    Nonempty (MeanValueWitness f f' a b) := by
  rcases exists_hasDerivAt_eq_slope f f' hab continuous differentiable with
    ⟨point, hinterior, hmean⟩
  exact ⟨⟨point, hinterior, differentiable point hinterior, hmean⟩⟩

/-- A squeeze places one declared real receiver face while retaining an independent residue face. -/
structure ReceiverSqueezeCertificate (Index Residue : Type*) (l : Filter Index) where
  lower : Index → ℝ
  standardFace : Index → ℝ
  upper : Index → ℝ
  limit : ℝ
  lower_tendsto : Tendsto lower l (𝓝 limit)
  upper_tendsto : Tendsto upper l (𝓝 limit)
  lower_le : lower ≤ standardFace
  face_le : standardFace ≤ upper
  residue : Index → Residue

theorem ReceiverSqueezeCertificate.standardFace_tendsto
    {Index Residue : Type*} {l : Filter Index}
    (certificate : ReceiverSqueezeCertificate Index Residue l) :
    Tendsto certificate.standardFace l (𝓝 certificate.limit) :=
  Soma.Holonics.Millennium.Chronology.theBodyIsPlacedWhenTheConstraintsClose
    certificate.lower_tendsto certificate.upper_tendsto certificate.lower_le certificate.face_le

/-- The proved limit is exactly the first projection; the residue remains in the combined carrier. -/
theorem ReceiverSqueezeCertificate.combined_standardFace_tendsto
    {Index Residue : Type*} {l : Filter Index}
    (certificate : ReceiverSqueezeCertificate Index Residue l) :
    Tendsto (fun index ↦ (certificate.standardFace index, certificate.residue index).1)
      l (𝓝 certificate.limit) := by
  simpa using certificate.standardFace_tendsto

#print axioms infinitesimal_square_zero
#print axioms ExactDifferentialPath.integratesToBoundary
#print axioms HigherDimensionalReceiver.equalShadow_iff_difference_mem_kernel
#print axioms refinement_cell_vanishes_but_total_remains
#print axioms meanValueWitness_of_hypotheses
#print axioms ReceiverSqueezeCertificate.standardFace_tendsto

end Soma.Holonics.Computation.HolonicConstructiveDifferentialBoundary
