import ElementaryHolonics.Geometry.SixSpherePeriods
import Mathlib.Analysis.Complex.Basic
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.DiscreteSubset
import Mathlib.Topology.Instances.Int

/-!
# The geometric complex two-torus fibre in the six-sphere family

The period matrix now acts on the full integral carrier `ℤ⁴`.  Under the already proved
upper-half-plane and negative-defect gates, its four real columns form a closed embedding into
`ℂ²`; their image is therefore a closed discrete subgroup.  `ComplexTorusFibre p` is the
topological additive quotient `ℂ² / Λₚ`, not a finite phase sample.

The three period equivariances are then descended to continuous additive equivalences of quotient
fibres.  The inverse-transpose matrices `A₁`, `A₂`, and `M₀` are the variance adapters: they
turn the right primal lattice action in the period formula into the inverse lattice representative
needed by the left fibre-coordinate transport.  Thus the arithmetic monodromy now acts on the
geometric quotient carrier.

Truth status: `[proved-derived] [formal-checked]` for every theorem, relative to the explicit period
matrix and determinant hypotheses in `SixSpherePeriods`.  This file constructs the discrete period
lattice, topological quotient, admissible parameter family, and its three generator lifts.  It does
not construct the paper's holomorphic functions on the upper half-plane, prove compactness of the
quotient, construct the exceptional toric/logarithmic fillings, glue their collars, or identify a
completed total space with `S⁶`; those are later source-ordered deeds.
-/

namespace Soma.Holonics.Geometry.SixSphereTorusFibre

open Soma.Holonics.Geometry.SixSphereMonodromy
open Soma.Holonics.Geometry.SixSpherePeriods
open Topology

noncomputable section

abbrev ComplexTwoSpace := Fin 2 → ℂ
abbrev RealFourSpace := Fin 4 → ℝ

/-! ## The full period lattice and its topology -/

/-- Coordinatewise inclusion of the integral rank-four carrier in real four-space. -/
def latticeCast (v : Lattice) : RealFourSpace := fun i ↦ (v i : ℝ)

theorem latticeCast_isClosedEmbedding : Topology.IsClosedEmbedding latticeCast := by
  change Topology.IsClosedEmbedding
    (fun v : Fin 4 → ℤ => fun i => (v i : ℝ))
  exact Topology.IsClosedEmbedding.piMap
    (fun _ : Fin 4 ↦ Int.isClosedEmbedding_coe_real)

/-- The receiver reassembles four real coordinates into two genuinely complex coordinates. -/
def realFourEquivComplexTwo : RealFourSpace ≃ₗ[ℝ] ComplexTwoSpace where
  toFun x := ![⟨x 0, x 1⟩, ⟨x 2, x 3⟩]
  invFun z := ![(z 0).re, (z 0).im, (z 1).re, (z 1).im]
  left_inv x := by ext i; fin_cases i <;> rfl
  right_inv z := by ext i <;> fin_cases i <;> apply Complex.ext <;> rfl
  map_add' x y := by ext i <;> fin_cases i <;> apply Complex.ext <;> simp
  map_smul' c x := by ext i <;> fin_cases i <;> apply Complex.ext <;> simp

/-- A nonzero real period determinant makes multiplication by the real period matrix an
equivalence, not merely an injective finite probe. -/
def realPeriodLinearEquiv (p : PeriodPoint) (hdet : (realPeriodMatrix p).det ≠ 0) :
    RealFourSpace ≃ₗ[ℝ] RealFourSpace :=
  LinearEquiv.ofBijective (Matrix.mulVecLin (realPeriodMatrix p)) ⟨
    Matrix.mulVec_injective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)),
    Matrix.mulVec_surjective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet))⟩

/-- The integral combination of the four displayed complex period columns. -/
def periodColumnVector (p : PeriodPoint) (v : Lattice) : ComplexTwoSpace :=
  (periodMatrix p).mulVec fun j ↦ (v j : ℂ)

/-- Realifying the complex period combination gives exactly the displayed real period matrix. -/
theorem realify_periodColumnVector (p : PeriodPoint) (v : Lattice) :
    realFourEquivComplexTwo ((realPeriodMatrix p).mulVec (latticeCast v)) =
      periodColumnVector p v := by
  ext i
  fin_cases i <;>
    apply Complex.ext <;>
    simp [realFourEquivComplexTwo, realPeriodMatrix, latticeCast, periodColumnVector,
      periodMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;>
    ring

/-- The period-column construction as an additive map from the full lattice. -/
def periodColumnAddHom (p : PeriodPoint) : Lattice →+ ComplexTwoSpace where
  toFun := periodColumnVector p
  map_zero' := by
    ext i
    fin_cases i <;>
      simp [periodColumnVector, periodMatrix, Matrix.mulVec, dotProduct]
  map_add' x y := by
    ext i
    fin_cases i <;>
      simp [periodColumnVector, periodMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;>
      ring

/-- The rank-four period lattice `Λₚ ⊆ ℂ²`. -/
def periodLattice (p : PeriodPoint) : AddSubgroup ComplexTwoSpace :=
  (periodColumnAddHom p).range

/-- The geometric quotient carrier.  Its topology is the quotient topology from `ℂ²`. -/
abbrev ComplexTorusFibre (p : PeriodPoint) := ComplexTwoSpace ⧸ periodLattice p

/-- The determinant gate upgrades the period map to a closed embedding of `ℤ⁴` in `ℂ²`. -/
theorem periodColumnVector_isClosedEmbedding (p : PeriodPoint)
    (hτ : 0 < p.τ.im) (hD : D p < 0) :
    Topology.IsClosedEmbedding (periodColumnVector p) := by
  let eR := (realPeriodLinearEquiv p (realPeriodMatrix_det_ne_zero p hτ hD))
    |>.toContinuousLinearEquiv
  let eC := realFourEquivComplexTwo.toContinuousLinearEquiv
  have hcomp : Topology.IsClosedEmbedding (fun v : Lattice ↦ eC (eR (latticeCast v))) :=
    eC.toHomeomorph.isClosedEmbedding.comp
      (eR.toHomeomorph.isClosedEmbedding.comp latticeCast_isClosedEmbedding)
  have heq : periodColumnVector p = fun v : Lattice ↦ eC (eR (latticeCast v)) := by
    funext v
    exact (realify_periodColumnVector p v).symm
  rw [heq]
  exact hcomp

/-- The full period subgroup is discrete in the inherited topology from `ℂ²`. -/
theorem periodLattice_isDiscrete (p : PeriodPoint)
    (hτ : 0 < p.τ.im) (hD : D p < 0) :
    IsDiscrete (periodLattice p : Set ComplexTwoSpace) := by
  simpa [periodLattice, periodColumnAddHom] using
    ((periodColumnVector_isClosedEmbedding p hτ hD).isEmbedding.isInducing.isDiscrete_range)

/-- The same embedded period subgroup is closed, so the quotient has the expected separation
gate whenever these hypotheses are installed. -/
theorem periodLattice_isClosed (p : PeriodPoint)
    (hτ : 0 < p.τ.im) (hD : D p < 0) :
    IsClosed (periodLattice p : Set ComplexTwoSpace) := by
  simpa [periodLattice, periodColumnAddHom] using
    (periodColumnVector_isClosedEmbedding p hτ hD).isClosed_range

/-! ## Primal/dual variance and period transport -/

/-- Complexifying the primal transpose action commutes with applying it to an integral vector. -/
theorem complexMonodromy_mulVec_cast (T : LatticeEnd) (v : Lattice) :
    (complexMonodromy T).mulVec (fun j ↦ (v j : ℂ)) =
      fun i ↦ ((T.transpose.mulVec v i : ℤ) : ℂ) := by
  ext i
  simp [complexMonodromy, Matrix.mulVec, dotProduct]

theorem periodColumnVector_g1 (p : PeriodPoint) (hτ : p.τ ≠ 0) (v : Lattice) :
    periodColumnVector (g1 p) v =
      (R1 p).mulVec (periodColumnVector p (T1.transpose.mulVec v)) := by
  unfold periodColumnVector
  rw [periodMatrix_g1_equivariant p hτ]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  change (R1 p).mulVec ((periodMatrix p).mulVec
    ((complexMonodromy T1).mulVec (fun j ↦ (v j : ℂ)))) = _
  rw [complexMonodromy_mulVec_cast]

/-- `A₁ = (T₁⁻¹)ᵀ` supplies the inverse representative needed for left fibre transport. -/
theorem periodColumnVector_g1_inverseVariance (p : PeriodPoint) (hτ : p.τ ≠ 0)
    (v : Lattice) :
    periodColumnVector (g1 p) (A1.mulVec v) =
      (R1 p).mulVec (periodColumnVector p v) := by
  rw [periodColumnVector_g1 p hτ]
  rw [Matrix.mulVec_mulVec, A1_isInverseTranspose.2]
  simp

theorem periodColumnVector_g2 (p : PeriodPoint) (hτ : p.τ ≠ 0) (v : Lattice) :
    periodColumnVector (g2 p) v =
      (R2 p).mulVec (periodColumnVector p (T2.transpose.mulVec v)) := by
  unfold periodColumnVector
  rw [periodMatrix_g2_equivariant p hτ]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  change (R2 p).mulVec ((periodMatrix p).mulVec
    ((complexMonodromy T2).mulVec (fun j ↦ (v j : ℂ)))) = _
  rw [complexMonodromy_mulVec_cast]

/-- `A₂ = (T₂⁻¹)ᵀ` is the second exact primal/dual variance adapter. -/
theorem periodColumnVector_g2_inverseVariance (p : PeriodPoint) (hτ : p.τ ≠ 0)
    (v : Lattice) :
    periodColumnVector (g2 p) (A2.mulVec v) =
      (R2 p).mulVec (periodColumnVector p v) := by
  rw [periodColumnVector_g2 p hτ]
  rw [Matrix.mulVec_mulVec, A2_isInverseTranspose.2]
  simp

theorem periodColumnVector_g0 (p : PeriodPoint) (v : Lattice) :
    periodColumnVector (g0 p) v =
      R0.mulVec (periodColumnVector p (T0.transpose.mulVec v)) := by
  unfold periodColumnVector
  rw [periodMatrix_g0_equivariant p]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  change R0.mulVec ((periodMatrix p).mulVec
    ((complexMonodromy T0).mulVec (fun j ↦ (v j : ℂ)))) = _
  rw [complexMonodromy_mulVec_cast]

/-- `M₀ = (T₀⁻¹)ᵀ` supplies the inverse representative at the parabolic return. -/
theorem periodColumnVector_g0_inverseVariance (p : PeriodPoint) (v : Lattice) :
    periodColumnVector (g0 p) (M0.mulVec v) =
      R0.mulVec (periodColumnVector p v) := by
  rw [periodColumnVector_g0 p]
  rw [Matrix.mulVec_mulVec, M0_isInverseTranspose.2]
  simp

/-! ## Descending the transport to quotient charts -/

/-- A nondegenerate fibre-coordinate matrix as a complex linear equivalence. -/
def fibreLinearEquiv (R : FibreMatrix) (hdet : R.det ≠ 0) :
    ComplexTwoSpace ≃ₗ[ℂ] ComplexTwoSpace :=
  LinearEquiv.ofBijective (Matrix.mulVecLin R) ⟨
    Matrix.mulVec_injective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)),
    Matrix.mulVec_surjective_iff_isUnit.mpr
      ((Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet))⟩

/-- A complex linear equivalence which carries one subgroup exactly onto another descends to a
continuous additive equivalence of the corresponding quotient charts. -/
def quotientContinuousLinearEquiv (L K : AddSubgroup ComplexTwoSpace)
    (e : ComplexTwoSpace ≃ₗ[ℂ] ComplexTwoSpace) (he : L.map e.toAddEquiv = K) :
    (ComplexTwoSpace ⧸ L) ≃ₜ+ (ComplexTwoSpace ⧸ K) where
  toAddEquiv := QuotientAddGroup.congr L K e.toAddEquiv he
  continuous_toFun := by
    apply (QuotientAddGroup.isQuotientMap_mk L).continuous_iff.mpr
    change Continuous (fun z : ComplexTwoSpace ↦ QuotientAddGroup.mk (e z))
    exact QuotientAddGroup.continuous_mk.comp e.toContinuousLinearEquiv.continuous
  continuous_invFun := by
    apply (QuotientAddGroup.isQuotientMap_mk K).continuous_iff.mpr
    change Continuous (fun z : ComplexTwoSpace ↦ QuotientAddGroup.mk (e.symm z))
    exact QuotientAddGroup.continuous_mk.comp e.symm.toContinuousLinearEquiv.continuous

theorem R1_maps_periodLattice (p : PeriodPoint) (hτ : p.τ ≠ 0) :
    (periodLattice p).map (fibreLinearEquiv (R1 p) (R1_det_ne_zero p hτ)).toAddEquiv =
      periodLattice (g1 p) := by
  apply le_antisymm
  · rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
    exact ⟨A1.mulVec v, periodColumnVector_g1_inverseVariance p hτ v⟩
  · rintro _ ⟨v, rfl⟩
    refine ⟨periodColumnVector p (T1.transpose.mulVec v), ⟨_, rfl⟩, ?_⟩
    exact (periodColumnVector_g1 p hτ v).symm

theorem R2_maps_periodLattice (p : PeriodPoint) (hτ : p.τ ≠ 0) :
    (periodLattice p).map (fibreLinearEquiv (R2 p) (R2_det_ne_zero p hτ)).toAddEquiv =
      periodLattice (g2 p) := by
  apply le_antisymm
  · rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
    exact ⟨A2.mulVec v, periodColumnVector_g2_inverseVariance p hτ v⟩
  · rintro _ ⟨v, rfl⟩
    refine ⟨periodColumnVector p (T2.transpose.mulVec v), ⟨_, rfl⟩, ?_⟩
    exact (periodColumnVector_g2 p hτ v).symm

theorem R0_maps_periodLattice (p : PeriodPoint) :
    (periodLattice p).map (fibreLinearEquiv R0 (by rw [R0_det]; norm_num)).toAddEquiv =
      periodLattice (g0 p) := by
  apply le_antisymm
  · rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
    exact ⟨M0.mulVec v, periodColumnVector_g0_inverseVariance p v⟩
  · rintro _ ⟨v, rfl⟩
    refine ⟨periodColumnVector p (T0.transpose.mulVec v), ⟨_, rfl⟩, ?_⟩
    exact (periodColumnVector_g0 p v).symm

/-- Order-three transport on the complete quotient fibre. -/
def torusTransportG1 (p : PeriodPoint) (hτ : p.τ ≠ 0) :
    ComplexTorusFibre p ≃+ ComplexTorusFibre (g1 p) :=
  QuotientAddGroup.congr (periodLattice p) (periodLattice (g1 p))
    (fibreLinearEquiv (R1 p) (R1_det_ne_zero p hτ)).toAddEquiv
    (R1_maps_periodLattice p hτ)

/-- Order-four transport on the complete quotient fibre. -/
def torusTransportG2 (p : PeriodPoint) (hτ : p.τ ≠ 0) :
    ComplexTorusFibre p ≃+ ComplexTorusFibre (g2 p) :=
  QuotientAddGroup.congr (periodLattice p) (periodLattice (g2 p))
    (fibreLinearEquiv (R2 p) (R2_det_ne_zero p hτ)).toAddEquiv
    (R2_maps_periodLattice p hτ)

/-- Parabolic transport on the complete quotient fibre. -/
def torusTransportG0 (p : PeriodPoint) :
    ComplexTorusFibre p ≃+ ComplexTorusFibre (g0 p) :=
  QuotientAddGroup.congr (periodLattice p) (periodLattice (g0 p))
    (fibreLinearEquiv R0 (by rw [R0_det]; norm_num)).toAddEquiv
    (R0_maps_periodLattice p)

theorem torusTransportG1_mk (p : PeriodPoint) (hτ : p.τ ≠ 0) (z : ComplexTwoSpace) :
    torusTransportG1 p hτ (QuotientAddGroup.mk z) =
      QuotientAddGroup.mk ((R1 p).mulVec z) := by
  rfl

theorem torusTransportG2_mk (p : PeriodPoint) (hτ : p.τ ≠ 0) (z : ComplexTwoSpace) :
    torusTransportG2 p hτ (QuotientAddGroup.mk z) =
      QuotientAddGroup.mk ((R2 p).mulVec z) := by
  rfl

theorem torusTransportG0_mk (p : PeriodPoint) (z : ComplexTwoSpace) :
    torusTransportG0 p (QuotientAddGroup.mk z) =
      QuotientAddGroup.mk (R0.mulVec z) := by
  rfl

/-- The quotient chart transport is continuous in both directions. -/
def torusTransportG1Continuous (p : PeriodPoint) (hτ : p.τ ≠ 0) :
    ComplexTorusFibre p ≃ₜ+ ComplexTorusFibre (g1 p) :=
  quotientContinuousLinearEquiv (periodLattice p) (periodLattice (g1 p))
    (fibreLinearEquiv (R1 p) (R1_det_ne_zero p hτ)) (R1_maps_periodLattice p hτ)

/-- The order-four quotient chart transport is continuous in both directions. -/
def torusTransportG2Continuous (p : PeriodPoint) (hτ : p.τ ≠ 0) :
    ComplexTorusFibre p ≃ₜ+ ComplexTorusFibre (g2 p) :=
  quotientContinuousLinearEquiv (periodLattice p) (periodLattice (g2 p))
    (fibreLinearEquiv (R2 p) (R2_det_ne_zero p hτ)) (R2_maps_periodLattice p hτ)

/-- The parabolic quotient chart transport is continuous in both directions. -/
def torusTransportG0Continuous (p : PeriodPoint) :
    ComplexTorusFibre p ≃ₜ+ ComplexTorusFibre (g0 p) :=
  quotientContinuousLinearEquiv (periodLattice p) (periodLattice (g0 p))
    (fibreLinearEquiv R0 (by rw [R0_det]; norm_num)) (R0_maps_periodLattice p)

/-! ## The admissible parameter family and its lifted generator returns -/

/-- A base occurrence at which the four periods form the required full lattice. -/
structure AdmissiblePeriodPoint where
  point : PeriodPoint
  upper : 0 < point.τ.im
  negativeDefect : D point < 0

def admissibleG1 (p : AdmissiblePeriodPoint) : AdmissiblePeriodPoint where
  point := g1 p.point
  upper := g1_preserves_upperHalfPlane p.point p.upper
  negativeDefect := by simpa [D_g1 p.point p.upper] using p.negativeDefect

def admissibleG2 (p : AdmissiblePeriodPoint) : AdmissiblePeriodPoint where
  point := g2 p.point
  upper := g2_preserves_upperHalfPlane p.point p.upper
  negativeDefect := by simpa [D_g2 p.point p.upper] using p.negativeDefect

def admissibleG0 (p : AdmissiblePeriodPoint) : AdmissiblePeriodPoint where
  point := g0 p.point
  upper := g0_preserves_upperHalfPlane p.point p.upper
  negativeDefect := by simpa [D_g0 p.point] using p.negativeDefect

abbrev AdmissibleTorusFibre (p : AdmissiblePeriodPoint) := ComplexTorusFibre p.point

/-- The dependent total space over all admissible period parameters before a holomorphic base map
and exceptional fillings are supplied. -/
abbrev AdmissibleTorusFamilyTotal := Σ p : AdmissiblePeriodPoint, AdmissibleTorusFibre p

/-- Lift the order-three base return together with its geometric fibre transport. -/
def familyLiftG1 : AdmissibleTorusFamilyTotal → AdmissibleTorusFamilyTotal
  | ⟨p, z⟩ => ⟨admissibleG1 p,
      torusTransportG1Continuous p.point (by
        intro hp
        have him := congrArg Complex.im hp
        simp at him
        exact p.upper.ne' him) z⟩

/-- Lift the order-four base return together with its geometric fibre transport. -/
def familyLiftG2 : AdmissibleTorusFamilyTotal → AdmissibleTorusFamilyTotal
  | ⟨p, z⟩ => ⟨admissibleG2 p,
      torusTransportG2Continuous p.point (by
        intro hp
        have him := congrArg Complex.im hp
        simp at him
        exact p.upper.ne' him) z⟩

/-- Lift the parabolic return together with its geometric fibre transport. -/
def familyLiftG0 : AdmissibleTorusFamilyTotal → AdmissibleTorusFamilyTotal
  | ⟨p, z⟩ => ⟨admissibleG0 p, torusTransportG0Continuous p.point z⟩

end

end Soma.Holonics.Geometry.SixSphereTorusFibre

section Audit
open Soma.Holonics.Geometry.SixSphereTorusFibre
#print axioms realify_periodColumnVector
#print axioms periodColumnVector_isClosedEmbedding
#print axioms periodLattice_isDiscrete
#print axioms periodLattice_isClosed
#print axioms periodColumnVector_g1_inverseVariance
#print axioms periodColumnVector_g2_inverseVariance
#print axioms periodColumnVector_g0_inverseVariance
#print axioms R1_maps_periodLattice
#print axioms R2_maps_periodLattice
#print axioms R0_maps_periodLattice
#print axioms torusTransportG1_mk
#print axioms torusTransportG2_mk
#print axioms torusTransportG0_mk
end Audit
