import ElementaryHolonics.Millennium.HodgeConstructivePassage
import ElementaryHolonics.Millennium.HodgeProjectiveLineSingularReduction
import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.Topology.KrullDimension
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Module.Submodule.RestrictScalars
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# The genuine smooth-projective Hodge receiver

The original `HodgeConjecture.Datum` deliberately left every source object behind an `Official`
predicate.  That was a safe statement boundary, but it was too coarse for the constructive cut:
an arbitrary module called `CycleSpace` did not expose whether its elements were actual algebraic
cycles on an actual smooth projective complex scheme.

This file removes that ambiguity.  A projective presentation is a closed immersion into the
actual Mathlib scheme `Proj 𝒜`, over a degree-zero base identified with `Spec ℂ`; smoothness is the
actual `AlgebraicGeometry.Smooth` predicate on the resulting structure morphism.  Codimension-`p`
cycles are locally finite integer algebraic cycles supported at points of coheight `p`, then
rationalized exactly by tensoring with `ℚ`.

Mathlib does not yet contain complex analytification, the rational Hodge decomposition, or the
algebraic-cycle/Betti cycle-class comparison for arbitrary schemes. `HodgeSemantics X` exposes
those constructions on one scheme. The universal `SourceDeterminedHodgeTheory` is stricter: it
does not store an arbitrary semantics or cycle-class map, but derives the latter as the typed
composite of a fundamental homology class current and Poincaré duality on the same analytic
carrier. The algebraic source, complete Hodge splitting, and rational singular-cohomology receiver
remain exposed. This is an assumption audit, not a proof of the Hodge conjecture.
-/

noncomputable section

open CategoryTheory
open scoped TensorProduct

namespace Soma.Holonics.Millennium.HodgeSmoothProjectiveReceiver

open AlgebraicGeometry
open Soma.Holonics.Millennium.HodgeConjecture
open Soma.Holonics.Millennium.HodgeConstructivePassage
open Soma.Holonics.Millennium.HodgeProjectiveLineSingularReduction

/-- [definition] The one-point complex base scheme. -/
abbrev ComplexPoint : Scheme := Spec (.of ℂ)

/-- [definition] A bundled graded commutative ring whose `Proj` is an actual Mathlib scheme. -/
structure GradedAmbient where
  Ring : Type
  commRing : CommRing Ring
  Piece : Type
  setLike : SetLike Piece Ring
  addSubgroupClass : AddSubgroupClass Piece Ring
  grading : ℕ → Piece
  gradedRing : GradedRing grading

namespace GradedAmbient

attribute [instance] commRing setLike addSubgroupClass gradedRing

def projectiveScheme (A : GradedAmbient) : Scheme :=
  Proj A.grading

def baseScheme (A : GradedAmbient) : Scheme :=
  Spec (.of <| A.grading 0)

noncomputable def projection (A : GradedAmbient) : A.projectiveScheme ⟶ A.baseScheme :=
  Proj.toSpecZero A.grading

end GradedAmbient

/-- [definition] A projective presentation of `X` over `ℂ` by a closed immersion into an actual
finite-type `Proj`.  `properProjection` records the already-standard properness theorem at the
bundled instance boundary; it is not a Hodge assumption. -/
structure ProjectivePresentation (X : Scheme) where
  ambient : GradedAmbient
  finiteType : Algebra.FiniteType (ambient.grading 0) ambient.Ring
  properProjection : IsProper ambient.projection
  baseIso : ambient.baseScheme ≅ ComplexPoint
  embedding : X ⟶ ambient.projectiveScheme
  closedEmbedding : IsClosedImmersion embedding

namespace ProjectivePresentation

attribute [instance] finiteType properProjection closedEmbedding

noncomputable def structureMap {X : Scheme} (P : ProjectivePresentation X) :
    X ⟶ ComplexPoint :=
  P.embedding ≫ P.ambient.projection ≫ P.baseIso.hom

instance {X : Scheme} (P : ProjectivePresentation X) :
    IsProper P.structureMap := by
  letI := P.finiteType
  letI := P.properProjection
  letI := P.closedEmbedding
  haveI : IsProper P.embedding := inferInstance
  haveI : IsProper P.ambient.projection := P.properProjection
  haveI : IsProper P.baseIso.hom := inferInstance
  change IsProper ((P.embedding ≫ P.ambient.projection) ≫ P.baseIso.hom)
  infer_instance

end ProjectivePresentation

/-- [definition] A smooth projective complex scheme with one retained projective presentation. -/
structure SmoothProjectiveComplexScheme where
  X : Scheme
  projective : ProjectivePresentation X
  smooth : Smooth projective.structureMap

namespace SmoothProjectiveComplexScheme

attribute [instance] smooth

/-- [proved-derived; formal-checked] Projectivity supplies properness of the complex structure
morphism. -/
instance (V : SmoothProjectiveComplexScheme) : IsProper V.projective.structureMap :=
  inferInstance

/-- [proved-standard; formal-checked] Projectivity over the complex point makes the complete
scheme-point carrier compact.  This is the finite-support gate which lets one geometric current
on irreducible occurrences extend over an arbitrary algebraic cycle without enumerating degrees
or source-specific examples. -/
noncomputable instance (V : SmoothProjectiveComplexScheme) : CompactSpace V.X :=
  (quasiCompact_iff_compactSpace V.projective.structureMap).mp inferInstance

end SmoothProjectiveComplexScheme

/-- [definition] Integral codimension-`p` cycles are genuine locally finite algebraic cycles whose
nonzero generic-point coefficients occur at coheight `p`. -/
def IntegralCodimensionCycles (X : Scheme) (p : ℕ) :
    Submodule ℤ (AlgebraicCycle X ℤ) where
  carrier := { cycle | ∀ x, cycle x ≠ 0 → Order.coheight x = p }
  zero_mem' := by simp
  add_mem' := by
    intro left right hleft hright x hsum
    by_cases hx : left x = 0
    · exact hright x (by simpa [hx] using hsum)
    · exact hleft x hx
  smul_mem' := by
    intro scalar cycle hcycle x hscaled
    exact hcycle x (by
      intro hx
      apply hscaled
      simp [hx])

abbrev RationalCodimensionCycles (X : Scheme) (p : ℕ) :=
  ℚ ⊗[ℤ] IntegralCodimensionCycles X p

/-- [definition] One irreducible codimension-`p` occurrence, represented by its generic point. -/
abbrev CodimensionPoint (X : Scheme) (p : ℕ) :=
  { point : X // Order.coheight point = p }

/-- [proved-derived; formal-checked] A codimension point emits its unit integral algebraic-cycle
generator. -/
noncomputable def integralCycleGenerator {X : Scheme} {p : ℕ}
    (point : CodimensionPoint X p) : IntegralCodimensionCycles X p := by
  classical
  refine ⟨Function.locallyFinsuppWithin.single point.1 1, ?_⟩
  intro x hx
  have samePoint : x = point.1 := by
    simpa [Function.locallyFinsuppWithin.single_apply] using hx
  simpa [samePoint] using point.2

/-- [proved-standard; formal-checked] On a compact scheme carrier every locally finite algebraic
cycle has finite support. -/
theorem algebraicCycle_support_finite {X : Scheme} [CompactSpace X]
    (cycle : AlgebraicCycle X ℤ) : cycle.support.Finite := by
  rw [← Set.univ_inter cycle.support]
  exact cycle.locallyFiniteSupport.finite_inter_support_of_isCompact isCompact_univ

section GeneratorCurrent

variable {H : Type*} [AddCommGroup H] [Module ℚ H]

/-- [definition] The coefficient-weighted contribution of one scheme point to a current on
codimension-`p` irreducible occurrences. -/
noncomputable def codimensionPointTerm {X : Scheme} {p : ℕ}
    (current : CodimensionPoint X p → H)
    (cycle : IntegralCodimensionCycles X p) (point : X) : H :=
  if codimension : Order.coheight point = p then
    (cycle : AlgebraicCycle X ℤ) point • current ⟨point, codimension⟩
  else 0

theorem codimensionPointTerm_support_subset {X : Scheme} {p : ℕ}
    (current : CodimensionPoint X p → H)
    (cycle : IntegralCodimensionCycles X p) :
    Function.support (codimensionPointTerm current cycle) ⊆
      (cycle : AlgebraicCycle X ℤ).support := by
  intro point nonzero
  contrapose! nonzero
  simp [codimensionPointTerm, Function.notMem_support.mp nonzero]

theorem codimensionPointTerm_support_finite {X : Scheme} [CompactSpace X] {p : ℕ}
    (current : CodimensionPoint X p → H)
    (cycle : IntegralCodimensionCycles X p) :
    (Function.support (codimensionPointTerm current cycle)).Finite :=
  (algebraicCycle_support_finite (cycle : AlgebraicCycle X ℤ)).subset
    (codimensionPointTerm_support_subset current cycle)

/-- [proved-derived; formal-checked] One current on irreducible codimension occurrences extends
linearly over every integral algebraic cycle by its exact finite coefficient population. -/
noncomputable def extendCodimensionPointCurrent {X : Scheme} [CompactSpace X] {p : ℕ}
    (current : CodimensionPoint X p → H) :
    IntegralCodimensionCycles X p →ₗ[ℤ] H where
  toFun cycle := ∑ᶠ point, codimensionPointTerm current cycle point
  map_add' left right := by
    rw [← finsum_add_distrib
      (codimensionPointTerm_support_finite current left)
      (codimensionPointTerm_support_finite current right)]
    congr 1
    funext point
    simp only [codimensionPointTerm]
    split <;> simp [add_smul]
  map_smul' coefficient cycle := by
    calc
      ∑ᶠ point, codimensionPointTerm current (coefficient • cycle) point =
          ∑ᶠ point, coefficient • codimensionPointTerm current cycle point := by
        congr 1
        funext point
        simp only [codimensionPointTerm]
        split <;> simp [smul_smul]
      _ = coefficient • ∑ᶠ point, codimensionPointTerm current cycle point :=
        ((DistribSMul.toAddMonoidHom H coefficient).map_finsum
          (codimensionPointTerm_support_finite current cycle)).symm

@[simp]
theorem extendCodimensionPointCurrent_generator
    {X : Scheme} [CompactSpace X] {p : ℕ}
    (current : CodimensionPoint X p → H) (point : CodimensionPoint X p) :
    extendCodimensionPointCurrent current (integralCycleGenerator point) = current point := by
  change (∑ᶠ x, codimensionPointTerm current (integralCycleGenerator point) x) = current point
  rw [finsum_eq_single _ point.1]
  · simp [codimensionPointTerm, integralCycleGenerator, point.2]
  · intro x different
    simp [codimensionPointTerm, integralCycleGenerator,
      Function.locallyFinsuppWithin.single_apply, different]

/-- [proved-derived; formal-checked] Scalar multiplication turns an integral current into the
bilinear current needed by the rational tensor extension. -/
noncomputable def rationalScalarCurrent {X : Scheme} {p : ℕ}
    (integralCurrent : IntegralCodimensionCycles X p →ₗ[ℤ] H) :
    ℚ →ₗ[ℚ] IntegralCodimensionCycles X p →ₗ[ℤ] H where
  toFun rational :=
    { toFun := fun cycle => rational • integralCurrent cycle
      map_add' := by intro left right; simp
      map_smul' := by
        intro integer cycle
        rw [integralCurrent.map_smul]
        simp only [RingHom.id_apply]
        exact smul_comm rational integer (integralCurrent cycle) }
  map_add' left right := by
    ext cycle
    simp [add_smul]
  map_smul' scalar rational := by
    ext cycle
    simp [mul_smul]

/-- [proved-derived; formal-checked] Exact tensor rationalization of an integral cycle current. -/
noncomputable def rationalizeIntegralCycleCurrent {X : Scheme} {p : ℕ}
    (integralCurrent : IntegralCodimensionCycles X p →ₗ[ℤ] H) :
    RationalCodimensionCycles X p →ₗ[ℚ] H :=
  TensorProduct.AlgebraTensorModule.lift (rationalScalarCurrent integralCurrent)

/-- [proved-derived; formal-checked] The single irreducible current extends to every rational
codimension cycle; there is no independent whole-cycle map to supply. -/
noncomputable def extendRationalCodimensionPointCurrent
    {X : Scheme} [CompactSpace X] {p : ℕ}
    (current : CodimensionPoint X p → H) :
    RationalCodimensionCycles X p →ₗ[ℚ] H :=
  rationalizeIntegralCycleCurrent (extendCodimensionPointCurrent current)

@[simp]
theorem rationalizeIntegralCycleCurrent_tmul {X : Scheme} {p : ℕ}
    (integralCurrent : IntegralCodimensionCycles X p →ₗ[ℤ] H)
    (rational : ℚ) (cycle : IntegralCodimensionCycles X p) :
    rationalizeIntegralCycleCurrent integralCurrent (rational ⊗ₜ cycle) =
      rational • integralCurrent cycle := by
  rfl

@[simp]
theorem extendRationalCodimensionPointCurrent_generator
    {X : Scheme} [CompactSpace X] {p : ℕ}
    (current : CodimensionPoint X p → H) (point : CodimensionPoint X p) :
    extendRationalCodimensionPointCurrent current
        (1 ⊗ₜ integralCycleGenerator point) = current point := by
  simp [extendRationalCodimensionPointCurrent]

/-- [proved-derived; formal-checked] Every integral cycle current lies in the rational span of
the irreducible geometric currents which constitute it. -/
theorem extendCodimensionPointCurrent_mem_span
    {X : Scheme} [CompactSpace X] {p : ℕ}
    (current : CodimensionPoint X p → H)
    (cycle : IntegralCodimensionCycles X p) :
    extendCodimensionPointCurrent current cycle ∈
      Submodule.span ℚ (Set.range current) := by
  change (∑ᶠ point, codimensionPointTerm current cycle point) ∈
    Submodule.span ℚ (Set.range current)
  rw [finsum_eq_sum _ (codimensionPointTerm_support_finite current cycle)]
  apply Submodule.sum_mem
  intro point _
  simp only [codimensionPointTerm]
  split
  · rw [← Int.cast_smul_eq_zsmul ℚ]
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨_, rfl⟩
  · exact Submodule.zero_mem _

/-- [proved-derived; formal-checked] The range of the complete rational cycle current is exactly
the span of its irreducible geometric generator currents.  This is the degree-independent
local-to-global law: no basis, cardinality, or repeated `H_i` case occurs. -/
theorem extendRationalCodimensionPointCurrent_range
    {X : Scheme} [CompactSpace X] {p : ℕ}
    (current : CodimensionPoint X p → H) :
    LinearMap.range (extendRationalCodimensionPointCurrent current) =
      Submodule.span ℚ (Set.range current) := by
  apply le_antisymm
  · rintro value ⟨cycle, rfl⟩
    induction cycle using TensorProduct.induction_on with
    | zero => exact Submodule.zero_mem _
    | tmul rational integralCycle =>
        rw [extendRationalCodimensionPointCurrent,
          rationalizeIntegralCycleCurrent_tmul]
        exact Submodule.smul_mem _ _
          (extendCodimensionPointCurrent_mem_span current integralCycle)
    | add left right leftMem rightMem =>
        rw [map_add]
        exact Submodule.add_mem _ leftMem rightMem
  · rw [Submodule.span_le]
    rintro value ⟨point, rfl⟩
    exact ⟨1 ⊗ₜ integralCycleGenerator point, by simp⟩

end GeneratorCurrent

/-- [definition] Rational Betti cohomology is represented by the rational dual of genuine
singular homology of the declared analytic carrier. -/
abbrev RationalBettiCohomology (analyticSpace : TopCat) (p : ℕ) : ModuleCat ℚ :=
  ModuleCat.of ℚ
    (Module.Dual ℚ (RationalSingularHomology (2 * p) analyticSpace))

/-! ## The rational Hodge receiver is derived from a complete complex splitting -/

/-- [definition] Complexification of one rational Betti cohomology line. -/
abbrev Complexification (H : ModuleCat ℚ) := ℂ ⊗[ℚ] H

/-- [definition] The canonical rational occurrence map into its complexification. -/
def rationalToComplex (H : ModuleCat ℚ) :
    H →ₗ[ℚ] Complexification H :=
  TensorProduct.mk ℚ ℂ H 1

/-- [definition] Complex conjugation acts on the coefficient incidence and leaves the rational
source occurrence fixed. -/
def complexificationConjugation (H : ModuleCat ℚ) :
    Complexification H →ₗ[ℚ] Complexification H :=
  TensorProduct.map (Complex.conjAe.toLinearMap.restrictScalars ℚ)
    (LinearMap.id (R := ℚ) (M := H))

/-- [definition] The conjugate Hodge address `H^{r,weight-r} ↔ H^{weight-r,r}`. -/
def conjugateHodgeIndex {weight : ℕ}
    (index : Fin (weight + 1)) : Fin (weight + 1) :=
  ⟨weight - index, by omega⟩

/-- [definition] A complete pure Hodge splitting on a rational cohomology carrier.

The component at address `r` is `H^{r,weight-r}`.  `internal` is the exact existence-and-uniqueness
law for reconstructing every complexified class from its components; `conjugation_exchanges`
retains the real/rational descent symmetry.  Thus a purported `(p,p)` carrier can no longer be
chosen independently of the complete decomposition. -/
structure PureHodgeDecomposition (H : ModuleCat ℚ) (weight : ℕ) where
  component : Fin (weight + 1) → Submodule ℂ (Complexification H)
  internal : DirectSum.IsInternal component
  conjugation_exchanges : ∀ index vector,
    vector ∈ component index ↔
      complexificationConjugation H vector ∈
        component (conjugateHodgeIndex index)

/-- [definition] In weight `2p`, the middle address is exactly `(p,p)`. -/
def middleHodgeIndex (p : ℕ) : Fin (2 * p + 1) :=
  ⟨p, by omega⟩

namespace PureHodgeDecomposition

/-- [definition] Rational Hodge classes are the rational occurrences whose complexifications
land in the middle `(p,p)` component.  This is a derived receiver, not a free submodule field. -/
def rationalMiddle {H : ModuleCat ℚ} (p : ℕ)
    (splitting : PureHodgeDecomposition H (2 * p)) : Submodule ℚ H :=
  (splitting.component (middleHodgeIndex p)).restrictScalars ℚ |>.comap
    (rationalToComplex H)

/-- [proved-derived; formal-checked] Membership in the rational receiver is definitionally the
vanishing of every non-middle Hodge difference after complexification. -/
theorem mem_rationalMiddle_iff {H : ModuleCat ℚ} (p : ℕ)
    (splitting : PureHodgeDecomposition H (2 * p)) (hodgeClass : H) :
    hodgeClass ∈ splitting.rationalMiddle p ↔
      rationalToComplex H hodgeClass ∈
        splitting.component (middleHodgeIndex p) := by
  rfl

/-- [definition] The receiver quotient which forgets exactly the middle `(p,p)` component while
retaining every non-middle returned difference. -/
abbrev MiddleHodgeDefect {H : ModuleCat ℚ} (p : ℕ)
    (splitting : PureHodgeDecomposition H (2 * p)) :=
  Complexification H ⧸
    (splitting.component (middleHodgeIndex p)).restrictScalars ℚ

/-- [definition] Complexify one rational class and return its residue modulo the middle
component.  Zero is therefore an exact typed Hodge condition, not a Boolean annotation. -/
def middleDefect {H : ModuleCat ℚ} (p : ℕ)
    (splitting : PureHodgeDecomposition H (2 * p)) :
    H →ₗ[ℚ] MiddleHodgeDefect p splitting :=
  (Submodule.mkQ
      ((splitting.component (middleHodgeIndex p)).restrictScalars ℚ)).comp
    (rationalToComplex H)

/-- [proved-derived; formal-checked] A rational class belongs to the middle Hodge receiver exactly
when its non-middle returned difference is null. -/
theorem mem_rationalMiddle_iff_middleDefect_eq_zero {H : ModuleCat ℚ} (p : ℕ)
    (splitting : PureHodgeDecomposition H (2 * p)) (hodgeClass : H) :
    hodgeClass ∈ splitting.rationalMiddle p ↔
      splitting.middleDefect p hodgeClass = 0 := by
  rw [mem_rationalMiddle_iff]
  change _ ↔
    Submodule.mkQ
      ((splitting.component (middleHodgeIndex p)).restrictScalars ℚ)
        (rationalToComplex H hodgeClass) = 0
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
    Submodule.restrictScalars_mem]

/-- [proved-derived; formal-checked] The rational Hodge carrier is definitionally recoverable as
the kernel of its exact non-middle defect receiver. -/
theorem rationalMiddle_eq_ker_middleDefect {H : ModuleCat ℚ} (p : ℕ)
    (splitting : PureHodgeDecomposition H (2 * p)) :
    splitting.rationalMiddle p = LinearMap.ker (splitting.middleDefect p) := by
  ext hodgeClass
  exact splitting.mem_rationalMiddle_iff_middleDefect_eq_zero p hodgeClass

end PureHodgeDecomposition

/-! ## Source-indexed analytic and cycle-class data -/

/-- [definition] Closed points of the Zariski carrier.  Complex analytification has these points,
not the generic points which also inhabit the underlying topological space of a scheme. -/
abbrev ComplexClosedPoint (X : Scheme) :=
  { point : X // IsClosed ({point} : Set X) }

/-- [definition] The inherited Zariski topology on the closed-point subtype, named explicitly so
it remains distinct from the analytic topology on the same situated population. -/
def complexClosedPointZariskiTopology (X : Scheme) :
    TopologicalSpace (ComplexClosedPoint X) :=
  inferInstance

/-- [definition] Closed complex scheme points with the induced topology, retained as the exact
receiver of analytification's point chart. -/
abbrev ComplexClosedPointTopCat (X : Scheme) : TopCat :=
  @TopCat.of (ComplexClosedPoint X) (complexClosedPointZariskiTopology X)

/-- [proved-derived; formal-checked] Forgetting the closed-point witness is the canonical
continuous inclusion into the complete Zariski point space. -/
def complexClosedPointInclusion (X : Scheme) :
    ComplexClosedPointTopCat X ⟶ (X : TopCat) :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-! ## The algebraic cycle current is a geometric composite -/

/-- [definition] The standard geometric factorization of the rational cycle-class current.

A codimension-`p` algebraic cycle first emits its fundamental homology class in real degree
`2 (dimℂ X - p)`.  Poincaré duality then returns a rational cohomology class in degree `2p`.
The public `cycleClass` below is definitionally this composite, so the universal receiver no
longer stores an unrelated linear map bearing that name.

This structure is an exact construction contract, not an algebraicity assumption: it owes the
fundamental-class and Poincaré-duality maps on the declared analytic carrier, but it does not ask
that those maps be surjective onto rational Hodge classes. -/
structure FundamentalClassPoincarePassage (geometry : SmoothProjectiveComplexScheme)
    (analyticSpace : TopCat)
    (hodgeDecomposition : ∀ p,
      PureHodgeDecomposition (RationalBettiCohomology analyticSpace p) (2 * p)) where
  complexDimension : ℕ
  /-- Exact rational Poincaré duality, with both orientations retained.  An arbitrary or zero
  forward current cannot inhabit this field. -/
  poincareDuality : ∀ (p : ℕ) (_insideDimension : p ≤ complexDimension),
    RationalSingularHomology (2 * (complexDimension - p)) analyticSpace ≅
      RationalBettiCohomology analyticSpace p
  /-- One geometric current on each actual irreducible codimension occurrence.  The whole
  algebraic-cycle current is derived below by finite linear extension and rationalization. -/
  irreducibleHodgeFundamentalClass :
    ∀ (p : ℕ) (insideDimension : p ≤ complexDimension),
      CodimensionPoint geometry.X p →
        ((hodgeDecomposition p).rationalMiddle p |>.comap
          (poincareDuality p insideDimension).hom.hom)

namespace FundamentalClassPoincarePassage

/-- [definition] The exact homology carrier whose Poincaré return lies in the rational middle
Hodge component.  A source occurrence in this carrier retains both its homology class and the
proof that the return has type `(p,p)`. -/
abbrev HodgeFundamentalHomology {geometry : SmoothProjectiveComplexScheme}
    {analyticSpace : TopCat}
    {hodgeDecomposition : ∀ p,
      PureHodgeDecomposition (RationalBettiCohomology analyticSpace p) (2 * p)}
    (passage : FundamentalClassPoincarePassage geometry analyticSpace hodgeDecomposition)
    (p : ℕ) (insideDimension : p ≤ passage.complexDimension) :=
  ((hodgeDecomposition p).rationalMiddle p).comap
    (passage.poincareDuality p insideDimension).hom.hom

/-- [proved-derived; formal-checked] The Hodge-typed current on all rational algebraic cycles is
the exact finite linear extension of the irreducible currents. -/
noncomputable def hodgeFundamentalClass
    {geometry : SmoothProjectiveComplexScheme} {analyticSpace : TopCat}
    {hodgeDecomposition : ∀ p,
      PureHodgeDecomposition (RationalBettiCohomology analyticSpace p) (2 * p)}
    (passage : FundamentalClassPoincarePassage geometry analyticSpace hodgeDecomposition)
    (p : ℕ) (insideDimension : p ≤ passage.complexDimension) :
    ModuleCat.of ℚ (RationalCodimensionCycles geometry.X p) ⟶
      ModuleCat.of ℚ (passage.HodgeFundamentalHomology p insideDimension) :=
  ModuleCat.ofHom
    (extendRationalCodimensionPointCurrent
      (passage.irreducibleHodgeFundamentalClass p insideDimension))

/-- [proved-derived; formal-checked] Forgetting only the Hodge-membership witness returns the
ordinary fundamental homology class current. -/
noncomputable def fundamentalClass
    {geometry : SmoothProjectiveComplexScheme} {analyticSpace : TopCat}
    {hodgeDecomposition : ∀ p,
      PureHodgeDecomposition (RationalBettiCohomology analyticSpace p) (2 * p)}
    (passage : FundamentalClassPoincarePassage geometry analyticSpace hodgeDecomposition)
    (p : ℕ) (insideDimension : p ≤ passage.complexDimension) :
    ModuleCat.of ℚ (RationalCodimensionCycles geometry.X p) ⟶
      RationalSingularHomology (2 * (passage.complexDimension - p)) analyticSpace :=
  passage.hodgeFundamentalClass p insideDimension ≫
    ModuleCat.ofHom (passage.HodgeFundamentalHomology p insideDimension).subtype

/-- [proved-derived; formal-checked] The derived whole-cycle current agrees with the supplied
geometric current on every irreducible generator. -/
@[simp]
theorem hodgeFundamentalClass_generator
    {geometry : SmoothProjectiveComplexScheme} {analyticSpace : TopCat}
    {hodgeDecomposition : ∀ p,
      PureHodgeDecomposition (RationalBettiCohomology analyticSpace p) (2 * p)}
    (passage : FundamentalClassPoincarePassage geometry analyticSpace hodgeDecomposition)
    (p : ℕ) (insideDimension : p ≤ passage.complexDimension)
    (point : CodimensionPoint geometry.X p) :
    (passage.hodgeFundamentalClass p insideDimension).hom
        (1 ⊗ₜ integralCycleGenerator point) =
      passage.irreducibleHodgeFundamentalClass p insideDimension point := by
  simp [hodgeFundamentalClass]

/-- [proved-derived; formal-checked] The complete Hodge-typed fundamental current has no hidden
whole-cycle directions: its range is exactly the rational span of the irreducible geometric
currents. -/
theorem hodgeFundamentalClass_range
    {geometry : SmoothProjectiveComplexScheme} {analyticSpace : TopCat}
    {hodgeDecomposition : ∀ p,
      PureHodgeDecomposition (RationalBettiCohomology analyticSpace p) (2 * p)}
    (passage : FundamentalClassPoincarePassage geometry analyticSpace hodgeDecomposition)
    (p : ℕ) (insideDimension : p ≤ passage.complexDimension) :
    LinearMap.range (passage.hodgeFundamentalClass p insideDimension).hom =
      Submodule.span ℚ
        (Set.range (passage.irreducibleHodgeFundamentalClass p insideDimension)) := by
  exact extendRationalCodimensionPointCurrent_range
    (passage.irreducibleHodgeFundamentalClass p insideDimension)

/-- [definition] The cohomology class returned by one irreducible codimension occurrence after
forgetting its Hodge witness and transporting its fundamental current through Poincaré duality. -/
def irreducibleCycleClass
    {geometry : SmoothProjectiveComplexScheme} {analyticSpace : TopCat}
    {hodgeDecomposition : ∀ p,
      PureHodgeDecomposition (RationalBettiCohomology analyticSpace p) (2 * p)}
    (passage : FundamentalClassPoincarePassage geometry analyticSpace hodgeDecomposition)
    (p : ℕ) (insideDimension : p ≤ passage.complexDimension) :
    CodimensionPoint geometry.X p → RationalBettiCohomology analyticSpace p :=
  fun point =>
    (passage.poincareDuality p insideDimension).hom.hom
      (passage.irreducibleHodgeFundamentalClass p insideDimension point).1

/-- [proved-derived; formal-checked] The rational cycle-class map is the transported fundamental
class followed by Poincaré duality.  There is no independent cycle-current choice. -/
noncomputable def cycleClass {geometry : SmoothProjectiveComplexScheme} {analyticSpace : TopCat}
    {hodgeDecomposition : ∀ p,
      PureHodgeDecomposition (RationalBettiCohomology analyticSpace p) (2 * p)}
    (passage : FundamentalClassPoincarePassage geometry analyticSpace hodgeDecomposition) (p : ℕ) :
    ModuleCat.of ℚ (RationalCodimensionCycles geometry.X p) ⟶
      RationalBettiCohomology analyticSpace p :=
  if insideDimension : p ≤ passage.complexDimension then
    passage.fundamentalClass p insideDimension ≫
      (passage.poincareDuality p insideDimension).hom
  else
    0

/-- [proved-derived; formal-checked] Inside complex dimension the total cycle current is exactly
the fundamental-class/Poincaré composite. -/
theorem cycleClass_of_le {geometry : SmoothProjectiveComplexScheme} {analyticSpace : TopCat}
    {hodgeDecomposition : ∀ p,
      PureHodgeDecomposition (RationalBettiCohomology analyticSpace p) (2 * p)}
    (passage : FundamentalClassPoincarePassage geometry analyticSpace hodgeDecomposition)
    (p : ℕ) (insideDimension : p ≤ passage.complexDimension) :
    passage.cycleClass p =
      passage.fundamentalClass p insideDimension ≫
        (passage.poincareDuality p insideDimension).hom := by
  simp only [cycleClass, dif_pos insideDimension]

/-- [proved-derived; formal-checked] Inside complex dimension the official cycle-class image is
exactly the rational span of the Poincaré-dual irreducible geometric currents.  This is the
universal local-to-global equation; it contains every algebraic cycle without enumerating any
degree, basis, or finite model. -/
theorem cycleClass_range_of_le
    {geometry : SmoothProjectiveComplexScheme} {analyticSpace : TopCat}
    {hodgeDecomposition : ∀ p,
      PureHodgeDecomposition (RationalBettiCohomology analyticSpace p) (2 * p)}
    (passage : FundamentalClassPoincarePassage geometry analyticSpace hodgeDecomposition)
    (p : ℕ) (insideDimension : p ≤ passage.complexDimension) :
    LinearMap.range (passage.cycleClass p).hom =
      Submodule.span ℚ (Set.range (passage.irreducibleCycleClass p insideDimension)) := by
  rw [passage.cycleClass_of_le p insideDimension]
  change LinearMap.range
      ((passage.poincareDuality p insideDimension).hom.hom.comp
        ((passage.HodgeFundamentalHomology p insideDimension).subtype.comp
          (passage.hodgeFundamentalClass p insideDimension).hom)) = _
  rw [LinearMap.range_comp, LinearMap.range_comp,
    passage.hodgeFundamentalClass_range p insideDimension]
  rw [Submodule.map_span, Submodule.map_span]
  congr 1
  ext value
  constructor
  · rintro ⟨homology, ⟨typed, ⟨point, rfl⟩, rfl⟩, rfl⟩
    exact ⟨point, rfl⟩
  · rintro ⟨point, rfl⟩
    exact ⟨_, ⟨_, ⟨point, rfl⟩, rfl⟩, rfl⟩

/-- [proved-derived; formal-checked] In every admissible codimension, the Hodge conclusion is
literally the statement that irreducible geometric classes span the complete rational middle
Hodge receiver. -/
theorem hodgeConclusion_iff_irreducibleCycleClass_span
    {geometry : SmoothProjectiveComplexScheme} {analyticSpace : TopCat}
    {hodgeDecomposition : ∀ p,
      PureHodgeDecomposition (RationalBettiCohomology analyticSpace p) (2 * p)}
    (passage : FundamentalClassPoincarePassage geometry analyticSpace hodgeDecomposition)
    (p : ℕ) (insideDimension : p ≤ passage.complexDimension) :
    (hodgeDecomposition p).rationalMiddle p =
        LinearMap.range (passage.cycleClass p).hom ↔
      (hodgeDecomposition p).rationalMiddle p =
        Submodule.span ℚ
          (Set.range (passage.irreducibleCycleClass p insideDimension)) := by
  rw [passage.cycleClass_range_of_le p insideDimension]

/-- [proved-derived; formal-checked] Above complex dimension the total algebraic-cycle current is
definitionally zero; no truncated `dim - p = 0` Poincaré obligation is emitted. -/
theorem cycleClass_of_dimension_lt {geometry : SmoothProjectiveComplexScheme} {analyticSpace : TopCat}
    {hodgeDecomposition : ∀ p,
      PureHodgeDecomposition (RationalBettiCohomology analyticSpace p) (2 * p)}
    (passage : FundamentalClassPoincarePassage geometry analyticSpace hodgeDecomposition)
    (p : ℕ) (aboveDimension : passage.complexDimension < p) :
    passage.cycleClass p = 0 := by
  simp only [cycleClass, dif_neg (not_le_of_gt aboveDimension)]

/-- [proved-derived; formal-checked] Every emitted cycle class lies in the rational middle Hodge
carrier because its fundamental homology occurrence was typed in the exact Poincaré preimage.
The former free `cycleClassesAreHodge` field is therefore a theorem. -/
theorem cycleClassesAreHodge {geometry : SmoothProjectiveComplexScheme} {analyticSpace : TopCat}
    {hodgeDecomposition : ∀ p,
      PureHodgeDecomposition (RationalBettiCohomology analyticSpace p) (2 * p)}
    (passage : FundamentalClassPoincarePassage geometry analyticSpace hodgeDecomposition) (p : ℕ) :
    LinearMap.range (passage.cycleClass p).hom ≤
      (hodgeDecomposition p).rationalMiddle p := by
  by_cases insideDimension : p ≤ passage.complexDimension
  · rw [passage.cycleClass_of_le p insideDimension]
    rintro _ ⟨cycle, rfl⟩
    exact ((passage.hodgeFundamentalClass p insideDimension).hom cycle).property
  · rw [cycleClass, dif_neg insideDimension]
    rintro _ ⟨cycle, rfl⟩
    simp

end FundamentalClassPoincarePassage

/-- [definition] The complete data presented by one analytic/Hodge/cycle-class receiver on a
fixed scheme.

The continuous map `toZariski` lands at closed points, and `toClosedPoint_bijective` retains the
exact common population of analytic points and closed complex scheme points.  It deliberately does
not identify the analytic population with generic scheme points.  The analytic topology may be
strictly finer than the induced Zariski topology.  The rational Hodge carrier and the cycle class
are data derived on this same addressed source; no predicate can approve an unrelated topological
space, submodule, or map.  Construction of this structure from a general smooth projective complex
scheme remains a visible standard-mathematics obligation. -/
structure HodgeSemantics (X : Scheme) where
  /-- The single complex-dimension occurrence consumed by Poincaré and Lefschetz transport. -/
  complexDimension : ℕ
  analyticSpace : TopCat
  toZariski : analyticSpace ⟶ (X : TopCat)
  toZariski_closed : ∀ point,
    IsClosed ({toZariski point} : Set X)
  toClosedPoint_bijective : Function.Bijective fun point =>
    (⟨toZariski point, toZariski_closed point⟩ : ComplexClosedPoint X)
  hodgeDecomposition : ∀ p,
    PureHodgeDecomposition (RationalBettiCohomology analyticSpace p) (2 * p)
  cycleClass : ∀ p,
    ModuleCat.of ℚ (RationalCodimensionCycles X p) ⟶
      RationalBettiCohomology analyticSpace p
  cycleClassesAreHodge : ∀ p,
    LinearMap.range (cycleClass p).hom ≤
      (hodgeDecomposition p).rationalMiddle p

/-- [definition] One source-indexed candidate realization of all codimensions of the Hodge receiver on a
fixed smooth projective complex scheme.

The source of `cycleClass p` is definitionally the rationalization of actual Mathlib algebraic
cycles on `geometry.X`; its target is definitionally rational singular cohomology of the admitted
analytic carrier. -/
structure Realization where
  geometry : SmoothProjectiveComplexScheme
  semantics : HodgeSemantics geometry.X

/-! ## One source-determined semantics current -/

/-- [definition] The analytic topology on the already situated closed complex-point population.
Its only comparison datum is continuity of identity toward the inherited Zariski topology. -/
structure AnalyticClosedPointCarrier (X : Scheme) where
  topology : TopologicalSpace (ComplexClosedPoint X)
  identityToZariskiContinuous :
    @Continuous (ComplexClosedPoint X) (ComplexClosedPoint X)
      topology (complexClosedPointZariskiTopology X) id

namespace AnalyticClosedPointCarrier

/-- [definition] The closed-point population equipped with its analytic topology. -/
def toTopCat {X : Scheme} (carrier : AnalyticClosedPointCarrier X) : TopCat :=
  @TopCat.of (ComplexClosedPoint X) carrier.topology

/-- [proved-derived; formal-checked] Identity changes only the topology chart. -/
def toClosedPointChart {X : Scheme} (carrier : AnalyticClosedPointCarrier X) :
    carrier.toTopCat ⟶ ComplexClosedPointTopCat X :=
  @TopCat.ofHom (ComplexClosedPoint X) (ComplexClosedPoint X)
    carrier.topology (complexClosedPointZariskiTopology X)
    (@ContinuousMap.mk (ComplexClosedPoint X) (ComplexClosedPoint X)
      carrier.topology (complexClosedPointZariskiTopology X) id (by
        exact carrier.identityToZariskiContinuous))

/-- [proved-derived; formal-checked] The analytic and Zariski charts retain the same situated
point population. -/
theorem toClosedPointChart_bijective {X : Scheme}
    (carrier : AnalyticClosedPointCarrier X) :
    Function.Bijective carrier.toClosedPointChart :=
  by
    change Function.Bijective id
    exact Function.bijective_id

end AnalyticClosedPointCarrier

/-- [definition] A single semantics current indexed by every situated smooth-projective source.

This deletes the freedom to approve unrelated `Realization` values one at a time through an
arbitrary predicate.  It does not claim to construct the classical current: an inhabitant still
owes analytification, the Hodge splitting, and the fundamental-class cycle map for every source.
Those are standard geometric construction obligations, kept separate from primitive algebraicity.
-/
structure SourceDeterminedHodgeTheory where
  analyticCarrier : (geometry : SmoothProjectiveComplexScheme) →
    AnalyticClosedPointCarrier geometry.X
  hodgeDecomposition : ∀ geometry p,
    PureHodgeDecomposition
      (RationalBettiCohomology (analyticCarrier geometry).toTopCat p) (2 * p)
  cyclePassage : ∀ geometry,
    FundamentalClassPoincarePassage geometry
      (analyticCarrier geometry).toTopCat
      (hodgeDecomposition geometry)

namespace SourceDeterminedHodgeTheory

/-- [proved-derived; formal-checked] The analytic carrier is the source's own closed complex-point
population equipped with the declared finer topology. -/
def analyticSpace (theory : SourceDeterminedHodgeTheory)
    (geometry : SmoothProjectiveComplexScheme) : TopCat :=
  (theory.analyticCarrier geometry).toTopCat

/-- [proved-derived; formal-checked] The analytic-to-closed-point chart is identity on occurrences;
only the topology changes. -/
def closedPointChart (theory : SourceDeterminedHodgeTheory)
    (geometry : SmoothProjectiveComplexScheme) :
    theory.analyticSpace geometry ⟶ ComplexClosedPointTopCat geometry.X :=
  (theory.analyticCarrier geometry).toClosedPointChart

/-- [proved-derived; formal-checked] Population faithfulness is no longer a supplied field: the
identity chart is bijective by construction. -/
theorem closedPointChart_bijective (theory : SourceDeterminedHodgeTheory)
    (geometry : SmoothProjectiveComplexScheme) :
    Function.Bijective (theory.closedPointChart geometry) :=
  (theory.analyticCarrier geometry).toClosedPointChart_bijective

/-- [proved-derived; formal-checked] The analytic-to-Zariski map is the typed closed-point chart
followed by witness erasure. -/
def toZariski (theory : SourceDeterminedHodgeTheory)
    (geometry : SmoothProjectiveComplexScheme) :
    theory.analyticSpace geometry ⟶ (geometry.X : TopCat) :=
  theory.closedPointChart geometry ≫ complexClosedPointInclusion geometry.X

/-- [proved-derived; formal-checked] Every point emitted by the universal analytic chart is closed
because closedness belongs to its codomain occurrence, not to an independent proof family. -/
theorem toZariski_closed (theory : SourceDeterminedHodgeTheory)
    (geometry : SmoothProjectiveComplexScheme)
    (point : theory.analyticSpace geometry) :
    IsClosed ({theory.toZariski geometry point} : Set geometry.X) :=
  (theory.closedPointChart geometry point).property

/-- [proved-derived; formal-checked] Reconstructing the closed-point occurrence after projection
returns exactly the original typed chart output. -/
@[simp]
theorem toClosedPoint_eq_chart (theory : SourceDeterminedHodgeTheory)
    (geometry : SmoothProjectiveComplexScheme)
    (point : theory.analyticSpace geometry) :
    (⟨theory.toZariski geometry point,
      theory.toZariski_closed geometry point⟩ : ComplexClosedPoint geometry.X) =
        theory.closedPointChart geometry point :=
  rfl

/-- [proved-derived; formal-checked] The analytic/closed-point population bijection is inherited
from the one typed chart. -/
theorem toClosedPoint_bijective (theory : SourceDeterminedHodgeTheory)
    (geometry : SmoothProjectiveComplexScheme) :
    Function.Bijective fun point =>
      (⟨theory.toZariski geometry point,
        theory.toZariski_closed geometry point⟩ : ComplexClosedPoint geometry.X) := by
  simpa only [theory.toClosedPoint_eq_chart geometry] using
    theory.closedPointChart_bijective geometry

/-- [proved-derived; formal-checked] The semantics emitted at one source is assembled from its
analytic chart, complete Hodge splitting, and the derived fundamental-class/Poincaré composite.
No arbitrary `HodgeSemantics` or cycle-class map is selected here. -/
def semantics (theory : SourceDeterminedHodgeTheory)
    (geometry : SmoothProjectiveComplexScheme) : HodgeSemantics geometry.X where
  complexDimension := (theory.cyclePassage geometry).complexDimension
  analyticSpace := theory.analyticSpace geometry
  toZariski := theory.toZariski geometry
  toZariski_closed := theory.toZariski_closed geometry
  toClosedPoint_bijective := theory.toClosedPoint_bijective geometry
  hodgeDecomposition := theory.hodgeDecomposition geometry
  cycleClass := (theory.cyclePassage geometry).cycleClass
  cycleClassesAreHodge := (theory.cyclePassage geometry).cycleClassesAreHodge

@[simp]
theorem semantics_cycleClass_of_le (theory : SourceDeterminedHodgeTheory)
    (geometry : SmoothProjectiveComplexScheme) (p : ℕ)
    (insideDimension : p ≤ (theory.cyclePassage geometry).complexDimension) :
    (theory.semantics geometry).cycleClass p =
      (theory.cyclePassage geometry).fundamentalClass p insideDimension ≫
        ((theory.cyclePassage geometry).poincareDuality p insideDimension).hom := by
  exact (theory.cyclePassage geometry).cycleClass_of_le p insideDimension

@[simp]
theorem semantics_cycleClass_of_dimension_lt (theory : SourceDeterminedHodgeTheory)
    (geometry : SmoothProjectiveComplexScheme) (p : ℕ)
    (aboveDimension : (theory.cyclePassage geometry).complexDimension < p) :
    (theory.semantics geometry).cycleClass p = 0 := by
  exact (theory.cyclePassage geometry).cycleClass_of_dimension_lt p aboveDimension

/-- [definition] The unique realization emitted by the declared source current at one situated
smooth-projective geometry. -/
def realization (theory : SourceDeterminedHodgeTheory)
    (geometry : SmoothProjectiveComplexScheme) : Realization where
  geometry := geometry
  semantics := theory.semantics geometry

/-- [definition] Source-determined admission: a realization is admitted exactly when its
semantics is the value emitted at its own complete geometric source. -/
def Canonical (theory : SourceDeterminedHodgeTheory) (R : Realization) : Prop :=
  R.semantics = theory.semantics R.geometry

@[simp]
theorem canonical_realization (theory : SourceDeterminedHodgeTheory)
    (geometry : SmoothProjectiveComplexScheme) :
    theory.Canonical (theory.realization geometry) :=
  rfl

end SourceDeterminedHodgeTheory

namespace Realization

/-- [definition] One realization owns one complex-dimension occurrence; downstream systems may
not author an independent integer chart. -/
abbrev complexDimension (R : Realization) : ℕ := R.semantics.complexDimension

/-- [definition] The analytic carrier retained by the source-indexed semantics. -/
abbrev analyticSpace (R : Realization) : TopCat := R.semantics.analyticSpace

/-- [definition] The complete Hodge splitting at one codimension. -/
abbrev hodgeDecomposition (R : Realization) (p : ℕ) :=
  R.semantics.hodgeDecomposition p

/-- [definition] The cycle-class passage on genuine rational codimension cycles. -/
abbrev cycleClass (R : Realization) (p : ℕ) :=
  R.semantics.cycleClass p

/-- [proved-derived; formal-checked] Actual cycle classes land in the derived middle Hodge
receiver because that inclusion is carried by the same source-indexed semantics. -/
theorem cycleClassesAreHodge (R : Realization) (p : ℕ) :
    LinearMap.range (R.cycleClass p).hom ≤
      (R.hodgeDecomposition p).rationalMiddle p :=
  R.semantics.cycleClassesAreHodge p

/-- [proved-derived; formal-checked] Forget only the source-specific geometry while retaining the
exact Hodge datum consumed by the existing universal primitive passage. -/
def datum (R : Realization) (p : ℕ) : Datum where
  Variety := R.geometry.X
  codimension := p
  CycleSpace := ModuleCat.of ℚ (RationalCodimensionCycles R.geometry.X p)
  Cohomology := RationalBettiCohomology R.analyticSpace p
  cycleClass := R.cycleClass p
  rationalHodgeClasses := (R.hodgeDecomposition p).rationalMiddle p
  cycleClassesAreHodge := R.cycleClassesAreHodge p

@[simp]
theorem datum_codimension (R : Realization) (p : ℕ) :
    (R.datum p).codimension = p := rfl

end Realization

/-- [definition] The canonically admitted source-indexed family.  `Canonical R` is the still-visible proof
that the supplied analytic carrier, Hodge splitting, and cycle-class data are the geometric ones
attached to `R.geometry`; source indexing alone does not establish that fact. -/
def SmoothProjectiveDatum (Canonical : Realization → Prop) (D : Datum) : Prop :=
  ∃ (R : Realization) (p : ℕ), Canonical R ∧ D = R.datum p

/-- [definition] The classical Hodge conclusion over every canonically admitted source-indexed
smooth-projective realization. -/
def TheHodgeConjecture (Canonical : Realization → Prop) : Prop :=
  ∀ (R : Realization), Canonical R → ∀ p : ℕ, (R.datum p).Conclusion

namespace SourceDeterminedHodgeTheory

/-- [definition] The universal Hodge receiver attached to one source-determined semantics
current, with no free admission predicate. -/
def Conclusion (theory : SourceDeterminedHodgeTheory) : Prop :=
  ∀ (geometry : SmoothProjectiveComplexScheme) (p : ℕ),
    ((theory.realization geometry).datum p).Conclusion

/-- [proved-derived; formal-checked] The source-determined official conclusion at one admissible
codimension is exactly the irreducible-generator span equation.  All algebraic-cycle addition,
rationalization, and local-to-global passage have been eliminated from the remaining obligation. -/
theorem conclusionAt_iff_irreducibleCycleClass_span
    (theory : SourceDeterminedHodgeTheory)
    (geometry : SmoothProjectiveComplexScheme) (p : ℕ)
    (insideDimension : p ≤ (theory.cyclePassage geometry).complexDimension) :
    ((theory.realization geometry).datum p).Conclusion ↔
      (theory.hodgeDecomposition geometry p).rationalMiddle p =
        Submodule.span ℚ
          (Set.range
            ((theory.cyclePassage geometry).irreducibleCycleClass p insideDimension)) := by
  change
    (theory.hodgeDecomposition geometry p).rationalMiddle p =
        LinearMap.range ((theory.cyclePassage geometry).cycleClass p).hom ↔ _
  exact (theory.cyclePassage geometry).hodgeConclusion_iff_irreducibleCycleClass_span
    p insideDimension

/-- [proved-derived; formal-checked] The source-indexed universal receiver is exactly the earlier
predicate receiver specialized to equality with the single semantics current.  This theorem
removes arbitrary canonical-family selection; it does not assume or prove primitive algebraicity.
-/
theorem conclusion_iff_theHodgeConjecture
    (theory : SourceDeterminedHodgeTheory) :
    theory.Conclusion ↔ TheHodgeConjecture theory.Canonical := by
  constructor
  · rintro conclusion ⟨geometry, semantics⟩ hcanonical p
    unfold SourceDeterminedHodgeTheory.Canonical at hcanonical
    change semantics = theory.semantics geometry at hcanonical
    subst semantics
    exact conclusion geometry p
  · intro hodge geometry p
    exact hodge (theory.realization geometry)
      (theory.canonical_realization geometry) p

end SourceDeterminedHodgeTheory

/-- [proved-derived; formal-checked] The canonically admitted source-indexed formulation is exactly
the existing official-family formulation for the family selected by `Canonical`. -/
theorem theHodgeConjecture_iff_officialFamily (Canonical : Realization → Prop) :
    TheHodgeConjecture Canonical ↔
      TheHodgeConjectureIn (SmoothProjectiveDatum Canonical) := by
  constructor
  · intro h D hD
    obtain ⟨R, p, hcanonical, rfl⟩ := hD
    exact h R hcanonical p
  · intro h R hcanonical p
    exact h (R.datum p) ⟨R, p, hcanonical, rfl⟩

/-! ## Exact primitive residual on the genuine source -/

/-- [definition] One source-indexed Lefschetz injection between consecutive codimensions.

The source map acts on genuine algebraic cycles, the receiver map acts on the derived rational
Hodge carriers, and the square commutes with the source-typed cycle-class maps.  Injectivity is the
standard hard-Lefschetz input in the increasing range.  No primitive submodule or decomposition is
stored: both will be reconstructed from this transport. -/
structure InjectiveLefschetzStep (R : Realization) (p : ℕ) where
  cycleTransport : (R.datum p).CycleSpace →ₗ[ℚ] (R.datum (p + 1)).CycleSpace
  hodgeTransport :
    (R.datum p).rationalHodgeClasses →ₗ[ℚ]
      (R.datum (p + 1)).rationalHodgeClasses
  cycleClass_commutes : ∀ cycle : (R.datum p).CycleSpace,
    (R.datum (p + 1)).cycleClass.hom (cycleTransport cycle) =
      (hodgeTransport
        ⟨(R.datum p).cycleClass.hom cycle,
          (R.datum p).cycleClassesAreHodge ⟨cycle, rfl⟩⟩ :
        (R.datum (p + 1)).Cohomology)
  hodgeTransport_injective : Function.Injective hodgeTransport

namespace InjectiveLefschetzStep

variable {R : Realization} {p : ℕ}

/-- [definition] The exact receiver return selected from an injective Lefschetz transport. -/
noncomputable def lowerReturn (step : InjectiveLefschetzStep R p) :
    (R.datum (p + 1)).rationalHodgeClasses →ₗ[ℚ]
      (R.datum p).rationalHodgeClasses :=
  step.hodgeTransport.leftInverse

/-- [proved-derived; formal-checked] Returning immediately after the Lefschetz transport
reconstructs the lower occurrence exactly. -/
theorem lowerReturn_hodgeTransport (step : InjectiveLefschetzStep R p)
    (lowerClass : (R.datum p).rationalHodgeClasses) :
    step.lowerReturn (step.hodgeTransport lowerClass) = lowerClass := by
  exact LinearMap.leftInverse_apply_of_inj
    (LinearMap.ker_eq_bot.mpr step.hodgeTransport_injective) lowerClass

/-- [definition] The primitive returned difference is the kernel of the exact lower receiver. -/
def Primitive (step : InjectiveLefschetzStep R p) :
    Submodule ℚ (R.datum (p + 1)).rationalHodgeClasses :=
  LinearMap.ker step.lowerReturn

/-- [definition] Subtract the transported receiver return from an upper Hodge occurrence. -/
def primitivePart (step : InjectiveLefschetzStep R p)
    (upperClass : (R.datum (p + 1)).rationalHodgeClasses) :
    step.Primitive :=
  ⟨upperClass - step.hodgeTransport (step.lowerReturn upperClass), by
    simp only [Primitive, LinearMap.mem_ker, map_sub,
      step.lowerReturn_hodgeTransport, sub_self]⟩

/-- [proved-derived; formal-checked] Every upper occurrence is reconstructed exactly from its
kernel-valued returned difference and its transported lower receiver.  The former free
`Primitive` and `decompose` fields have disappeared. -/
theorem primitivePart_add_transport (step : InjectiveLefschetzStep R p)
    (upperClass : (R.datum (p + 1)).rationalHodgeClasses) :
    (step.primitivePart upperClass : (R.datum (p + 1)).rationalHodgeClasses) +
        step.hodgeTransport (step.lowerReturn upperClass) = upperClass := by
  simp [primitivePart]

/-- [proved-derived; formal-checked] An injective source Lefschetz transport constructs the exact
primitive step consumed by the local-to-global algebraicity passage. -/
noncomputable def toPrimitiveHodgeStep (step : InjectiveLefschetzStep R p) :
    PrimitiveHodgeStep (R.datum p) (R.datum (p + 1)) where
  cycleTransport := step.cycleTransport
  hodgeTransport := step.hodgeTransport
  cycleClass_commutes := step.cycleClass_commutes
  Primitive := step.Primitive
  decompose := by
    intro upperClass
    exact ⟨step.primitivePart upperClass, step.lowerReturn upperClass,
      step.primitivePart_add_transport upperClass⟩

end InjectiveLefschetzStep

/-- [definition] A Lefschetz staircase on one genuine smooth-projective realization.  Its steps
act on the actual rational algebraic-cycle sources and actual singular-cohomology receivers fixed
above.  Constructing these steps from cup product and the Lefschetz adjoint is a visible standard
theorem obligation, rather than part of the conjectural primitive algebraicity law. -/
structure PrimitiveLefschetzStaircase (R : Realization) where
  baseConclusion : (R.datum 0).Conclusion
  step : ∀ p, PrimitiveHodgeStep (R.datum p) (R.datum (p + 1))

namespace PrimitiveLefschetzStaircase

variable {R : Realization}

/-- [proved-derived; formal-checked] A family of genuine injective Lefschetz transports supplies
the entire primitive staircase; no independently authored primitive population or decomposition
remains. -/
noncomputable def ofInjectiveSteps
    (baseConclusion : (R.datum 0).Conclusion)
    (steps : ∀ p, InjectiveLefschetzStep R p) :
    PrimitiveLefschetzStaircase R where
  baseConclusion := baseConclusion
  step p := (steps p).toPrimitiveHodgeStep

/-- [definition] The only conjectural source obligation after a staircase has been constructed. -/
def AllPrimitiveLiftable (staircase : PrimitiveLefschetzStaircase R) : Prop :=
  ∀ p, (staircase.step p).PrimitiveLiftable

/-- [proved-derived; formal-checked] On a genuine source realization with a Lefschetz staircase,
the complete Hodge conclusion in every codimension is equivalent to liftability of every
primitive remainder.  This deletes every global-basis, dimension-count, and abstract-cycle-space
obligation from the official receiver. -/
theorem allConclusions_iff_allPrimitiveLiftable
    (staircase : PrimitiveLefschetzStaircase R) :
    (∀ p, (R.datum p).Conclusion) ↔ staircase.AllPrimitiveLiftable := by
  constructor
  · intro allConclusions p
    exact
      ((staircase.step p).hodgeConclusion_iff_primitiveLiftable_of_lower
        (allConclusions p)).mp (allConclusions (p + 1))
  · intro allPrimitive
    exact primitiveHodgeStaircaseConclusion
      R.datum staircase.step staircase.baseConclusion allPrimitive

/-- [proved-derived; formal-checked] A polarized algebraic interaction on every genuine primitive
remainder constructs every required algebraic cycle and closes the complete codimension tower. -/
theorem allConclusions_of_primitiveAlgebraicInteractions
    (staircase : PrimitiveLefschetzStaircase R)
    (interaction : ∀ p, PrimitiveAlgebraicInteraction (staircase.step p)) :
    ∀ p, (R.datum p).Conclusion := by
  apply staircase.allConclusions_iff_allPrimitiveLiftable.mpr
  intro p
  exact (interaction p).primitiveLiftable

end PrimitiveLefschetzStaircase

/-! ## Source-bearing primitive detection -/

/-- [definition] The primitive detector with the algebraic source occurrence retained.

Unlike `PrimitiveAlgebraicInteraction.detects`, `detects` here does not return only a class already
known to lie in an algebraic range.  It returns the primitive class together with an actual element
of its `CycleLiftFibre`.  For a `Realization`, that element is a rational combination of genuine
locally finite codimension cycles on the smooth projective scheme. -/
structure SourcePrimitiveAlgebraicInteraction {lower upper : Datum}
    (step : PrimitiveHodgeStep lower upper) where
  finiteDimensional : FiniteDimensional ℚ step.Primitive
  intersection : LinearMap.BilinForm ℚ step.Primitive
  reflexive : intersection.IsRefl
  algebraicNondegenerate :
    (intersection.restrict (primitiveAlgebraicClasses step)).Nondegenerate
  detects : ∀ primitive : step.Primitive, primitive ≠ 0 →
    ∃ algebraicPrimitive : step.Primitive,
      Nonempty (CycleLiftFibre upper
        (algebraicPrimitive : upper.rationalHodgeClasses)) ∧
      intersection algebraicPrimitive primitive ≠ 0

namespace SourcePrimitiveAlgebraicInteraction

variable {lower upper : Datum} {step : PrimitiveHodgeStep lower upper}

/-- [proved-derived; formal-checked] Forgetting the chosen source witness yields the earlier
interaction receiver; no algebraicity assertion is added. -/
def toPrimitiveAlgebraicInteraction
    (sourceInteraction : SourcePrimitiveAlgebraicInteraction step) :
    PrimitiveAlgebraicInteraction step where
  finiteDimensional := sourceInteraction.finiteDimensional
  intersection := sourceInteraction.intersection
  reflexive := sourceInteraction.reflexive
  algebraicNondegenerate := sourceInteraction.algebraicNondegenerate
  detects := by
    intro primitive hprimitive
    obtain ⟨algebraicPrimitive, ⟨sourceLift⟩, detected⟩ :=
      sourceInteraction.detects primitive hprimitive
    have algebraicMembership :
        algebraicPrimitive ∈ primitiveAlgebraicClasses step := by
      change
        ((algebraicPrimitive : step.Primitive) : upper.rationalHodgeClasses) ∈
          algebraicHodgeClasses upper
      change
        (((algebraicPrimitive : step.Primitive) : upper.rationalHodgeClasses) :
          upper.Cohomology) ∈ upper.algebraicSpan
      exact ⟨sourceLift.1, sourceLift.2⟩
    exact ⟨⟨algebraicPrimitive, algebraicMembership⟩, detected⟩

/-- [proved-derived; formal-checked] A source-bearing detector constructs every primitive cycle
lift through the exact interaction cut. -/
theorem primitiveLiftable
    (sourceInteraction : SourcePrimitiveAlgebraicInteraction step) :
    step.PrimitiveLiftable :=
  sourceInteraction.toPrimitiveAlgebraicInteraction.primitiveLiftable

end SourcePrimitiveAlgebraicInteraction

/-- [proved-derived; formal-checked] A uniform choice of genuine Lefschetz staircases and
primitive algebraic interactions proves the Hodge statement over the canonically admitted family.  The two
arguments display, without an `Official` catch-all, the exact standard and conjectural obligations
still to be constructed. -/
theorem theHodgeConjecture_of_primitiveAlgebraicInteractions
    (Canonical : Realization → Prop)
    (staircase : ∀ (R : Realization), Canonical R → PrimitiveLefschetzStaircase R)
    (interaction : ∀ (R : Realization) (hR : Canonical R) (p : ℕ),
      PrimitiveAlgebraicInteraction (((staircase R hR).step p))) :
    TheHodgeConjecture Canonical := by
  intro R hR
  exact (staircase R hR).allConclusions_of_primitiveAlgebraicInteractions
    (interaction R hR)

/-- [proved-derived; formal-checked] The universal theorem with source-bearing detectors.  Every
detector occurrence carries an actual rational algebraic cycle on the admitted scheme. -/
theorem theHodgeConjecture_of_sourcePrimitiveAlgebraicInteractions
    (Canonical : Realization → Prop)
    (staircase : ∀ (R : Realization), Canonical R → PrimitiveLefschetzStaircase R)
    (interaction : ∀ (R : Realization) (hR : Canonical R) (p : ℕ),
      SourcePrimitiveAlgebraicInteraction (((staircase R hR).step p))) :
    TheHodgeConjecture Canonical := by
  apply theHodgeConjecture_of_primitiveAlgebraicInteractions Canonical staircase
  intro R hR p
  exact (interaction R hR p).toPrimitiveAlgebraicInteraction

section Audit

#print axioms ProjectivePresentation.instIsProperStructureMap
#print axioms complexClosedPointInclusion
#print axioms AnalyticClosedPointCarrier.toClosedPointChart
#print axioms AnalyticClosedPointCarrier.toClosedPointChart_bijective
#print axioms SourceDeterminedHodgeTheory.closedPointChart
#print axioms SourceDeterminedHodgeTheory.closedPointChart_bijective
#print axioms SourceDeterminedHodgeTheory.toZariski
#print axioms SourceDeterminedHodgeTheory.toZariski_closed
#print axioms SourceDeterminedHodgeTheory.toClosedPoint_bijective
#print axioms extendCodimensionPointCurrent_generator
#print axioms extendRationalCodimensionPointCurrent_generator
#print axioms extendRationalCodimensionPointCurrent_range
#print axioms FundamentalClassPoincarePassage.hodgeFundamentalClass_generator
#print axioms FundamentalClassPoincarePassage.hodgeFundamentalClass_range
#print axioms FundamentalClassPoincarePassage.cycleClass_range_of_le
#print axioms FundamentalClassPoincarePassage.hodgeConclusion_iff_irreducibleCycleClass_span
#print axioms FundamentalClassPoincarePassage.fundamentalClass
#print axioms FundamentalClassPoincarePassage.cycleClass
#print axioms FundamentalClassPoincarePassage.cycleClass_of_le
#print axioms FundamentalClassPoincarePassage.cycleClass_of_dimension_lt
#print axioms FundamentalClassPoincarePassage.cycleClassesAreHodge
#print axioms SourceDeterminedHodgeTheory.semantics_cycleClass_of_le
#print axioms SourceDeterminedHodgeTheory.semantics_cycleClass_of_dimension_lt
#print axioms SourceDeterminedHodgeTheory.canonical_realization
#print axioms SourceDeterminedHodgeTheory.conclusionAt_iff_irreducibleCycleClass_span
#print axioms SourceDeterminedHodgeTheory.conclusion_iff_theHodgeConjecture
#print axioms theHodgeConjecture_iff_officialFamily
#print axioms InjectiveLefschetzStep.lowerReturn_hodgeTransport
#print axioms InjectiveLefschetzStep.primitivePart_add_transport
#print axioms InjectiveLefschetzStep.toPrimitiveHodgeStep
#print axioms PrimitiveLefschetzStaircase.ofInjectiveSteps
#print axioms PrimitiveLefschetzStaircase.allConclusions_iff_allPrimitiveLiftable
#print axioms PrimitiveLefschetzStaircase.allConclusions_of_primitiveAlgebraicInteractions
#print axioms SourcePrimitiveAlgebraicInteraction.toPrimitiveAlgebraicInteraction
#print axioms SourcePrimitiveAlgebraicInteraction.primitiveLiftable
#print axioms theHodgeConjecture_of_primitiveAlgebraicInteractions
#print axioms theHodgeConjecture_of_sourcePrimitiveAlgebraicInteractions

end Audit

end Soma.Holonics.Millennium.HodgeSmoothProjectiveReceiver
