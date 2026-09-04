import ElementaryHolonics.Millennium.HodgeSpherePowerRulingHomology
import ElementaryHolonics.Millennium.HodgeProjectiveLineRealization

/-!
# Genuine degree-four coordinate-pair classes on finite sphere powers

The first Hodge source not supplied by divisors occurs at codimension two in complex dimension
four.  On the projective-line power receiver, its topological shadow is the six addressed
coordinate pairs of `(S²)^4`.

This file constructs those addresses without storing the number six in the carrier.  For every
finite factor count, `CoordinatePair factorCount` is the population of strictly ordered pairs.
Each pair gives a genuine continuous insertion `S² × S² → (S²)^factorCount`, its functorial
singular-chain map, and transport of any closed source degree-four chain into a genuine rational
singular-homology class.  At factor count four, the address population is proved to have cardinal
six.

The standing surface and whole-power cellular reductions, if supplied, construct the common closed
source from the degree-four cellular generator.  Pair projections separate every returned class,
and the whole-graded power carrier upgrades the complete coordinate-pair map to a linear
equivalence in one theorem.  These are genuine topological homology classes; realizing them as
codimension-two algebraic cycles remains a separate source obligation.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgeSpherePowerPairHomology

open CategoryTheory CategoryTheory.Limits
open Simplicial
open Soma.Holonics.DiagonalChainTransport
open Soma.Holonics.Millennium.HodgeProjectiveLineSingularReduction
open Soma.Holonics.Millennium.HodgeSpherePowerRulingHomology
open Soma.Holonics.Millennium.HodgeSphereProductRulingCycles
open Soma.Holonics.Millennium.HodgeSphereProductRulingProjections
open Soma.Holonics.Millennium.HodgeSphereProductFiniteComplex
open Soma.Holonics.Millennium.HodgeProjectiveLineRealization

/-- [definition] Two distinct factor addresses in increasing order.  Ordering removes the
duplicate orientation of an unordered coordinate plane without inserting a magic cardinal. -/
abbrev CoordinatePair (factorCount : ℕ) :=
  { pair : Fin factorCount × Fin factorCount // pair.1 < pair.2 }

/-- [proved-derived; formal-checked] A four-factor power carries exactly six coordinate-pair
addresses. -/
theorem coordinatePair_four_card : Fintype.card (CoordinatePair 4) = 6 := by
  decide

/-- [definition] Insert `S² × S²` into the two addressed coordinates and hold every other
coordinate at the retained sphere basepoint. -/
def pairCoordinateContinuousMap {factorCount : ℕ}
    (pair : CoordinatePair factorCount) :
    C(sphereProductTopCat, SpherePower factorCount) where
  toFun point coordinate :=
    if coordinate = pair.1.1 then point.1
    else if coordinate = pair.1.2 then point.2
    else sphereBasepoint
  continuous_toFun := by
    apply continuous_pi
    intro coordinate
    by_cases hfirst : coordinate = pair.1.1
    · simp only [hfirst, if_pos]
      exact continuous_fst
    · by_cases hsecond : coordinate = pair.1.2
      · have secondNeFirst : pair.1.2 ≠ pair.1.1 := ne_of_gt pair.2
        simp only [hsecond, secondNeFirst, if_false, if_pos]
        exact continuous_snd
      · simp only [hfirst, hsecond]
        exact (continuous_const : Continuous
          (fun _ : TwoSphere × TwoSphere => sphereBasepoint))

/-- [definition] The corresponding map in the topological receiver chart. -/
def pairCoordinateTopMap {factorCount : ℕ}
    (pair : CoordinatePair factorCount) :
    sphereProductTopCat ⟶ spherePowerTopCat factorCount :=
  TopCat.ofHom (pairCoordinateContinuousMap pair)

/-- [definition] Project a finite sphere power back to one addressed coordinate pair. -/
def pairCoordinateProjectionContinuousMap {factorCount : ℕ}
    (pair : CoordinatePair factorCount) :
    C(SpherePower factorCount, TwoSphere × TwoSphere) where
  toFun point := (point pair.1.1, point pair.1.2)
  continuous_toFun :=
    (continuous_apply pair.1.1).prodMk (continuous_apply pair.1.2)

/-- [definition] The pair projection in the topological receiver chart. -/
def pairCoordinateProjectionTopMap {factorCount : ℕ}
    (pair : CoordinatePair factorCount) :
    spherePowerTopCat factorCount ⟶ sphereProductTopCat :=
  TopCat.ofHom (pairCoordinateProjectionContinuousMap pair)

/-- [proved-derived; formal-checked] Insertion followed by its matching pair projection is the
identity on the complete two-sphere product, so the addressed transport retains both geometric
coordinates. -/
theorem pairCoordinate_then_matching_projection {factorCount : ℕ}
    (pair : CoordinatePair factorCount) :
    pairCoordinateTopMap pair ≫ pairCoordinateProjectionTopMap pair =
      𝟙 sphereProductTopCat := by
  ext point
  change
    ((if pair.1.1 = pair.1.1 then point.1
      else if pair.1.1 = pair.1.2 then point.2 else sphereBasepoint),
     (if pair.1.2 = pair.1.1 then point.1
      else if pair.1.2 = pair.1.2 then point.2 else sphereBasepoint)) = point
  have secondNeFirst : pair.1.2 ≠ pair.1.1 := ne_of_gt pair.2
  simp only [if_pos, secondNeFirst, if_false]
  exact Prod.eta point

/-- [definition] Functorial transport on genuine rational singular chains. -/
def pairCoordinateChainMap {factorCount : ℕ}
    (pair : CoordinatePair factorCount) :
    SphereProductSingularChainComplex ⟶ SpherePowerChains factorCount :=
  ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℚ)).obj
    rationalCoefficient).map (pairCoordinateTopMap pair)

/-- [definition] Functorial singular-chain projection to one addressed coordinate pair. -/
def pairCoordinateProjectionChainMap {factorCount : ℕ}
    (pair : CoordinatePair factorCount) :
    SpherePowerChains factorCount ⟶ SphereProductSingularChainComplex :=
  ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℚ)).obj
    rationalCoefficient).map (pairCoordinateProjectionTopMap pair)

/-- [proved-derived; formal-checked] Matching pair transport is already an exact retraction at
chain level; no homology quotient is needed to repair it. -/
theorem pairCoordinateChainMap_matching_retract {factorCount : ℕ}
    (pair : CoordinatePair factorCount) :
    pairCoordinateChainMap pair ≫ pairCoordinateProjectionChainMap pair =
      𝟙 SphereProductSingularChainComplex := by
  change
    ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℚ)).obj
        rationalCoefficient).map (pairCoordinateTopMap pair) ≫
      ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℚ)).obj
        rationalCoefficient).map (pairCoordinateProjectionTopMap pair) = _
  rw [← Functor.map_comp, pairCoordinate_then_matching_projection]
  simp

/-- [definition] A genuine closed degree-four source occurrence on `S² × S²`. -/
structure SourceFourCycle where
  chain : SphereProductSingularChainComplex.X 4
  closed : SphereProductSingularChainComplex.d 4 3 chain = 0

/-- [definition] Transport a closed source chain into one addressed coordinate plane. -/
def pairCoordinateChain {factorCount : ℕ}
    (pair : CoordinatePair factorCount) (source : SourceFourCycle) :
    (SpherePowerChains factorCount).X 4 :=
  (pairCoordinateChainMap pair).f 4 source.chain

/-- [proved-derived; formal-checked] Functorial transport preserves the degree-four cycle law. -/
theorem pairCoordinateChain_closed {factorCount : ℕ}
    (pair : CoordinatePair factorCount) (source : SourceFourCycle) :
    (SpherePowerChains factorCount).d 4 3 (pairCoordinateChain pair source) = 0 := by
  change ((pairCoordinateChainMap pair).f 4 ≫
    (SpherePowerChains factorCount).d 4 3) source.chain = 0
  rw [(pairCoordinateChainMap pair).comm 4 3]
  change (pairCoordinateChainMap pair).f 3
    (SphereProductSingularChainComplex.d 4 3 source.chain) = 0
  rw [source.closed, map_zero]

/-- [definition] Genuine degree-four singular homology of a finite sphere power. -/
abbrev SpherePowerH4 (factorCount : ℕ) : ModuleCat ℚ :=
  HomologicalComplex.homology (SpherePowerChains factorCount) 4

/-- [definition] Genuine degree-four rational singular homology of `S² × S²`. -/
abbrev SphereProductH4 : ModuleCat ℚ :=
  HomologicalComplex.homology SphereProductSingularChainComplex 4

/-- [definition] The scalar source morphism for one transported degree-four cycle. -/
def pairCoordinateHomologyMorphism {factorCount : ℕ}
    (pair : CoordinatePair factorCount) (source : SourceFourCycle) :
    ScalarModule ⟶ SpherePowerH4 factorCount :=
  ((SpherePowerChains factorCount).liftCycles
      (ModuleCat.ofHom
        (LinearMap.toSpanSingleton ℚ _ (pairCoordinateChain pair source)))
      3 (by simp)
      (by
        ext
        change (SpherePowerChains factorCount).d 4 3
          ((1 : ℚ) • pairCoordinateChain pair source) = 0
        simpa using pairCoordinateChain_closed pair source)) ≫
    (SpherePowerChains factorCount).homologyπ 4

/-- [definition] The genuine homology class returned at one coordinate-pair address. -/
def pairCoordinateHomologyClass {factorCount : ℕ}
    (pair : CoordinatePair factorCount) (source : SourceFourCycle) :
    SpherePowerH4 factorCount :=
  pairCoordinateHomologyMorphism pair source 1

/-- [definition] Homology projection from a finite sphere power to one addressed coordinate
pair. -/
def pairCoordinateProjectionHomologyMap {factorCount : ℕ}
    (pair : CoordinatePair factorCount) :
    SpherePowerH4 factorCount ⟶ SphereProductH4 :=
  HomologicalComplex.homologyMap (pairCoordinateProjectionChainMap pair) 4

/-- [proved-derived; formal-checked] The matching pair projection is a left inverse on genuine
degree-four rational singular homology. -/
theorem pairCoordinateHomologyMap_matching_retract {factorCount : ℕ}
    (pair : CoordinatePair factorCount) :
    HomologicalComplex.homologyMap (pairCoordinateChainMap pair) 4 ≫
        pairCoordinateProjectionHomologyMap pair =
      𝟙 SphereProductH4 := by
  unfold pairCoordinateProjectionHomologyMap
  rw [← HomologicalComplex.homologyMap_comp]
  rw [pairCoordinateChainMap_matching_retract]
  exact HomologicalComplex.homologyMap_id SphereProductSingularChainComplex 4

/-- [proved-derived; formal-checked] Transport into one coordinate pair is injective on genuine
degree-four homology, witnessed by the matching geometric projection. -/
theorem pairCoordinateHomologyMap_injective {factorCount : ℕ}
    (pair : CoordinatePair factorCount) :
    Function.Injective
      (HomologicalComplex.homologyMap (pairCoordinateChainMap pair) 4) := by
  intro left right hequal
  have returned := congrArg
    (fun received => pairCoordinateProjectionHomologyMap pair received) hequal
  change
    (HomologicalComplex.homologyMap (pairCoordinateChainMap pair) 4 ≫
      pairCoordinateProjectionHomologyMap pair) left =
    (HomologicalComplex.homologyMap (pairCoordinateChainMap pair) 4 ≫
      pairCoordinateProjectionHomologyMap pair) right at returned
  rw [pairCoordinateHomologyMap_matching_retract] at returned
  exact returned

/-! ## Crossed coordinate pairs factor through one sphere

Two distinct increasing coordinate pairs share at most one coordinate.  Their insert--project
composite therefore carries at most one live sphere coordinate.  The following theorem retains
that statement as an exact factorization through `S²`; it does not assume the still-missing
degree-four vanishing theorem for the sphere.
-/

/-- [definition] The constant basepoint insertion from one sphere into the sphere product. -/
def constantSphereProductTopMap :
    HodgeTwoSphereFundamentalCycle.sphereTopCat ⟶ sphereProductTopCat :=
  TopCat.ofHom
    { toFun := fun _ => (sphereBasepoint, sphereBasepoint)
      continuous_toFun := continuous_const }

/-- [proved-derived; formal-checked] Distinct coordinate-pair transport has at most one live
coordinate and hence factors through one copy of `S²`. -/
theorem crossedPairTopMap_factorsThroughSphere {factorCount : ℕ}
    (source target : CoordinatePair factorCount) (hne : source ≠ target) :
    ∃ (left : sphereProductTopCat ⟶
        HodgeTwoSphereFundamentalCycle.sphereTopCat)
      (right : HodgeTwoSphereFundamentalCycle.sphereTopCat ⟶
        sphereProductTopCat),
      pairCoordinateTopMap source ≫ pairCoordinateProjectionTopMap target =
        left ≫ right := by
  by_cases h11 : target.1.1 = source.1.1
  · have h22 : target.1.2 ≠ source.1.2 := by
      intro h
      apply hne
      apply Subtype.ext
      exact Prod.ext h11.symm h.symm
    have h21 : target.1.2 ≠ source.1.1 := by
      intro h
      exact (ne_of_lt target.2) (h11.trans h.symm)
    refine ⟨firstProjectionTopMap, firstRulingTopMap, ?_⟩
    ext point
    change
      ((if target.1.1 = source.1.1 then point.1
        else if target.1.1 = source.1.2 then point.2 else sphereBasepoint),
       (if target.1.2 = source.1.1 then point.1
        else if target.1.2 = source.1.2 then point.2 else sphereBasepoint)) =
      (point.1, sphereBasepoint)
    simp [h11, h21, h22]
  · by_cases h12 : target.1.1 = source.1.2
    · have h21 : target.1.2 ≠ source.1.1 := by
        intro h
        have : source.1.2 < source.1.1 := h12 ▸ h ▸ target.2
        exact (not_lt_of_ge (Nat.le_of_lt source.2)) this
      have h22 : target.1.2 ≠ source.1.2 := by
        intro h
        exact (ne_of_lt target.2) (h12.trans h.symm)
      refine ⟨secondProjectionTopMap, firstRulingTopMap, ?_⟩
      ext point
      change
        ((if target.1.1 = source.1.1 then point.1
          else if target.1.1 = source.1.2 then point.2 else sphereBasepoint),
         (if target.1.2 = source.1.1 then point.1
          else if target.1.2 = source.1.2 then point.2 else sphereBasepoint)) =
        (point.2, sphereBasepoint)
      have sourceSecondNeFirst : source.1.2 ≠ source.1.1 := ne_of_gt source.2
      simp [h12, h21, h22, sourceSecondNeFirst]
    · by_cases h21 : target.1.2 = source.1.1
      · refine ⟨firstProjectionTopMap, secondRulingTopMap, ?_⟩
        ext point
        change
          ((if target.1.1 = source.1.1 then point.1
            else if target.1.1 = source.1.2 then point.2 else sphereBasepoint),
           (if target.1.2 = source.1.1 then point.1
            else if target.1.2 = source.1.2 then point.2 else sphereBasepoint)) =
          (sphereBasepoint, point.1)
        simp [h11, h12, h21]
      · by_cases h22 : target.1.2 = source.1.2
        · refine ⟨secondProjectionTopMap, secondRulingTopMap, ?_⟩
          ext point
          change
            ((if target.1.1 = source.1.1 then point.1
              else if target.1.1 = source.1.2 then point.2 else sphereBasepoint),
             (if target.1.2 = source.1.1 then point.1
              else if target.1.2 = source.1.2 then point.2 else sphereBasepoint)) =
            (sphereBasepoint, point.2)
          have sourceSecondNeFirst : source.1.2 ≠ source.1.1 := ne_of_gt source.2
          simp [h11, h12, h22, sourceSecondNeFirst]
        · refine ⟨firstProjectionTopMap, constantSphereProductTopMap, ?_⟩
          ext point
          change
            ((if target.1.1 = source.1.1 then point.1
              else if target.1.1 = source.1.2 then point.2 else sphereBasepoint),
             (if target.1.2 = source.1.1 then point.1
              else if target.1.2 = source.1.2 then point.2 else sphereBasepoint)) =
            (sphereBasepoint, sphereBasepoint)
          simp [h11, h12, h21, h22]

/-- [proved-derived; formal-checked] The crossed factorization transports functorially to the
actual rational singular-chain complexes. -/
theorem crossedPairChainMap_factorsThroughSphere {factorCount : ℕ}
    (source target : CoordinatePair factorCount) (hne : source ≠ target) :
    ∃ (left : SphereProductSingularChainComplex ⟶
        HodgeTwoSphereFundamentalCycle.SphereSingularChainComplex)
      (right : HodgeTwoSphereFundamentalCycle.SphereSingularChainComplex ⟶
        SphereProductSingularChainComplex),
      pairCoordinateChainMap source ≫ pairCoordinateProjectionChainMap target =
        left ≫ right := by
  obtain ⟨left, right, factor⟩ := crossedPairTopMap_factorsThroughSphere source target hne
  let singular :=
    (AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℚ)).obj
      rationalCoefficient
  refine ⟨singular.map left, singular.map right, ?_⟩
  change singular.map (pairCoordinateTopMap source) ≫
      singular.map (pairCoordinateProjectionTopMap target) =
    singular.map left ≫ singular.map right
  rw [← singular.map_comp, ← singular.map_comp, factor]

/-- [definition] Genuine degree-four rational singular homology of `S²`. -/
abbrev SphereH4 : ModuleCat ℚ :=
  HomologicalComplex.homology
    HodgeTwoSphereFundamentalCycle.SphereSingularChainComplex 4

/-- [proved-derived; formal-checked] The existing higher-even sphere filling family supplies the
precise degree-four vanishing instance consumed by crossed pair transport. -/
def sphereH4SubsingletonOfFillings (fillings : SphereHigherEvenCycleFillings) :
    Subsingleton SphereH4 :=
  ModuleCat.isZero_iff_subsingleton.mp
    (sphereHigherEvenHomology_isZero_of_fillings fillings (p := 2) (by omega))

/-- [proved-derived; formal-checked] Every crossed pair map factors through genuine rational
`H₄(S²)`. -/
theorem crossedPairHomologyMap_factorsThroughSphereH4 {factorCount : ℕ}
    (source target : CoordinatePair factorCount) (hne : source ≠ target) :
    ∃ (left : SphereProductH4 ⟶ SphereH4)
      (right : SphereH4 ⟶ SphereProductH4),
      HomologicalComplex.homologyMap (pairCoordinateChainMap source) 4 ≫
          pairCoordinateProjectionHomologyMap target = left ≫ right := by
  obtain ⟨left, right, factor⟩ := crossedPairChainMap_factorsThroughSphere source target hne
  refine ⟨HomologicalComplex.homologyMap left 4,
    HomologicalComplex.homologyMap right 4, ?_⟩
  unfold pairCoordinateProjectionHomologyMap
  rw [← HomologicalComplex.homologyMap_comp,
    ← HomologicalComplex.homologyMap_comp, factor]

/-- [proved-derived; formal-checked] Once the genuine sphere degree-four receiver is zero, every
crossed coordinate-pair projection vanishes.  This isolates the remaining topological theorem
without storing it in the pair carrier. -/
theorem crossedPairHomologyMap_eq_zero_of_sphereH4_subsingleton
    [Subsingleton SphereH4] {factorCount : ℕ}
    (source target : CoordinatePair factorCount) (hne : source ≠ target) :
    HomologicalComplex.homologyMap (pairCoordinateChainMap source) 4 ≫
        pairCoordinateProjectionHomologyMap target = 0 := by
  obtain ⟨left, right, factor⟩ :=
    crossedPairHomologyMap_factorsThroughSphereH4 source target hne
  rw [factor]
  ext received
  have leftZero : left received = 0 := Subsingleton.elim _ _
  change right (left received) = 0
  rw [leftZero, map_zero]

/-- [definition] Transport one common source `H₄` class through every coordinate-pair address. -/
def coordinatePairClassMap (factorCount : ℕ) (sourceClass : SphereProductH4) :
    (CoordinatePair factorCount → ℚ) →ₗ[ℚ] SpherePowerH4 factorCount where
  toFun coefficients := ∑ pair,
    coefficients pair •
      HomologicalComplex.homologyMap (pairCoordinateChainMap pair) 4 sourceClass
  map_add' left right := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' coefficient coefficients := by
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul, mul_smul,
      Finset.smul_sum]

/-- [proved-derived; formal-checked] Sphere degree-four vanishing and one nonzero source class
make the complete coordinate-pair transport injective.  At factor count four this is the exact
six-way independence receiver. -/
theorem coordinatePairClassMap_injective [Subsingleton SphereH4]
    {factorCount : ℕ} (sourceClass : SphereProductH4) (hsource : sourceClass ≠ 0) :
    Function.Injective (coordinatePairClassMap factorCount sourceClass) := by
  intro left right hequal
  ext target
  have projected := congrArg
    (fun received => pairCoordinateProjectionHomologyMap target received) hequal
  change
    pairCoordinateProjectionHomologyMap target
        (∑ pair, left pair •
          HomologicalComplex.homologyMap (pairCoordinateChainMap pair) 4 sourceClass) =
      pairCoordinateProjectionHomologyMap target
        (∑ pair, right pair •
          HomologicalComplex.homologyMap (pairCoordinateChainMap pair) 4 sourceClass) at projected
  simp only [map_sum, map_smul] at projected
  have reduce (coefficients : CoordinatePair factorCount → ℚ) :
      ∑ pair, coefficients pair •
          pairCoordinateProjectionHomologyMap target
            (HomologicalComplex.homologyMap (pairCoordinateChainMap pair) 4 sourceClass) =
        coefficients target • sourceClass := by
    rw [Finset.sum_eq_single target]
    · change coefficients target •
          (HomologicalComplex.homologyMap (pairCoordinateChainMap target) 4 ≫
            pairCoordinateProjectionHomologyMap target) sourceClass =
        coefficients target • sourceClass
      rw [pairCoordinateHomologyMap_matching_retract]
      rfl
    · intro pair _ hpair
      change coefficients pair •
          (HomologicalComplex.homologyMap (pairCoordinateChainMap pair) 4 ≫
            pairCoordinateProjectionHomologyMap target) sourceClass = 0
      rw [crossedPairHomologyMap_eq_zero_of_sphereH4_subsingleton pair target hpair]
      change coefficients pair • (0 : SphereProductH4) = 0
      exact smul_zero _
    · simp
  rw [reduce left, reduce right] at projected
  by_contra hcoeff
  have differenceNonzero : left target - right target ≠ 0 := sub_ne_zero.mpr hcoeff
  have annihilates : (left target - right target) • sourceClass = 0 := by
    rw [sub_smul, projected, sub_self]
  exact hsource ((smul_eq_zero.mp annihilates).resolve_left differenceNonzero)

/-! ## The cellular reduction returns the common nonzero source class -/

/-- [proved-derived; formal-checked] Degree-four homology of the exact even cellular complex is
the retained scalar top-cell carrier. -/
def surfaceCellHomologyIsoQFour :
    surfaceCellComplex.homology 4 ≅ ModuleCat.of ℚ ℚ :=
  (surfaceCellComplex.isoHomologyπ 5 4 (by simp)
      (surfaceCellComplex_d 4)).symm ≪≫
    surfaceCellComplex.iCyclesIso 4 3 (by simp)
      (surfaceCellComplex_d 3)

/-- [proved-derived; formal-checked] A cellular reduction identifies genuine sphere-product
degree-four homology with the scalar top-cell carrier. -/
def sphereProductH4EquivQOfReduction (reduction : SphereProductCellularReduction) :
    SphereProductH4 ≃ₗ[ℚ] ℚ :=
  (reduction.toHomologyIso 4).toLinearEquiv.trans
    surfaceCellHomologyIsoQFour.toLinearEquiv

/-- [proved-derived; formal-checked] Pull the cellular top-cell unit back to a genuine
`H₄(S²×S²;ℚ)` occurrence. -/
def sourceFourHomologyClassOfReduction (reduction : SphereProductCellularReduction) :
    SphereProductH4 :=
  (sphereProductH4EquivQOfReduction reduction).symm 1

/-- [proved-derived; formal-checked] The returned source class is nonzero because the exact
cellular comparison sends it back to the scalar unit. -/
theorem sourceFourHomologyClassOfReduction_ne_zero
    (reduction : SphereProductCellularReduction) :
    sourceFourHomologyClassOfReduction reduction ≠ 0 := by
  intro hzero
  have returned := congrArg (sphereProductH4EquivQOfReduction reduction) hzero
  simpa [sourceFourHomologyClassOfReduction] using returned

/-- [definition] The complete coordinate-pair transport generated by the cellular top class. -/
def coordinatePairClassMapOfReduction (factorCount : ℕ)
    (reduction : SphereProductCellularReduction) :
    (CoordinatePair factorCount → ℚ) →ₗ[ℚ] SpherePowerH4 factorCount :=
  coordinatePairClassMap factorCount (sourceFourHomologyClassOfReduction reduction)

/-- [proved-derived; formal-checked] The standing sphere filling and product cellular reduction
obligations jointly return the complete independent coordinate-pair population.  At four factors
its source has the already-derived cardinal six. -/
theorem coordinatePairClassMapOfReduction_injective
    (fillings : SphereHigherEvenCycleFillings)
    (reduction : SphereProductCellularReduction) :
    Function.Injective (coordinatePairClassMapOfReduction 4 reduction) := by
  letI : Subsingleton SphereH4 := sphereH4SubsingletonOfFillings fillings
  change Function.Injective
    (coordinatePairClassMap 4 (sourceFourHomologyClassOfReduction reduction))
  exact coordinatePairClassMap_injective _
    (sourceFourHomologyClassOfReduction_ne_zero reduction)

/-- [proved-derived; formal-checked] The whole-graded fourfold reduction supplies the missing
global dimension return, so the already separated coordinate-pair classes span genuine
`H₄((S²)^4;ℚ)`.  This is one source-family theorem, not six surjectivity checks. -/
theorem coordinatePairClassMapOfReductions_surjective
    (fillings : SphereHigherEvenCycleFillings)
    (sourceReduction : SphereProductCellularReduction)
    (powerReduction : SpherePowerCellularReduction 4) :
    Function.Surjective (coordinatePairClassMapOfReduction 4 sourceReduction) := by
  letI : FiniteDimensional ℚ (SpherePowerH4 4) :=
    FiniteDimensional.of_injective
      (spherePowerHomologyEquivCellModule 4 powerReduction 4).toLinearMap
      (spherePowerHomologyEquivCellModule 4 powerReduction 4).injective
  have coordinateFinrank :
      Module.finrank ℚ (CoordinatePair 4 → ℚ) = Nat.choose 4 2 := by
    rw [Module.finrank_fintype_fun_eq_card, coordinatePair_four_card]
    norm_num [Nat.choose]
  have homologyFinrank :
      Module.finrank ℚ (SpherePowerH4 4) = Nat.choose 4 2 := by
    calc
      Module.finrank ℚ (SpherePowerH4 4) =
          Module.finrank ℚ (spherePowerCellModule 4 4) :=
        (spherePowerHomologyEquivCellModule 4 powerReduction 4).finrank_eq
      _ = Nat.choose 4 2 := by
        exact spherePowerCellModule_finrank_even 4 2
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (coordinateFinrank.trans homologyFinrank.symm)).mp
      (coordinatePairClassMapOfReduction_injective fillings sourceReduction)

/-- [proved-derived; formal-checked] The six coordinate planes are therefore an exact reversible
chart on genuine degree-four sphere-power homology once the two source-level reductions are
provided. -/
def coordinatePairHomologyEquivOfReductions
    (fillings : SphereHigherEvenCycleFillings)
    (sourceReduction : SphereProductCellularReduction)
    (powerReduction : SpherePowerCellularReduction 4) :
    (CoordinatePair 4 → ℚ) ≃ₗ[ℚ] SpherePowerH4 4 :=
  LinearEquiv.ofBijective (coordinatePairClassMapOfReduction 4 sourceReduction)
    ⟨coordinatePairClassMapOfReduction_injective fillings sourceReduction,
      coordinatePairClassMapOfReductions_surjective fillings sourceReduction powerReduction⟩

/-- [definition] The complete addressed family returned by one common source cycle. -/
def pairCoordinateHomologyFamily {factorCount : ℕ} (source : SourceFourCycle) :
    CoordinatePair factorCount → SpherePowerH4 factorCount :=
  fun pair => pairCoordinateHomologyClass pair source

/-! ## The standing cellular residual supplies the source conditionally -/

/-- [definition] The degree-four generator in the exact finite cellular complex. -/
def cellFourGenerator : surfaceCellComplex.X 4 := (1 : ℚ)

/-- [proved-derived; formal-checked] The cellular generator is closed because the adjacent
differential is exactly zero. -/
theorem cellFourGenerator_closed :
    surfaceCellComplex.d 4 3 cellFourGenerator = 0 := by
  rw [surfaceCellComplex_d]
  rfl

/-- [proved-derived; formal-checked] A genuine cellular reduction transports the finite generator
to a closed singular degree-four source occurrence. -/
def sourceFourCycleOfReduction
    (reduction : SphereProductCellularReduction) : SourceFourCycle where
  chain := reduction.inv.f 4 cellFourGenerator
  closed := by
    change (reduction.inv.f 4 ≫
      SphereProductSingularChainComplex.d 4 3) cellFourGenerator = 0
    rw [reduction.inv.comm 4 3]
    change reduction.inv.f 3
      (surfaceCellComplex.d 4 3 cellFourGenerator) = 0
    rw [cellFourGenerator_closed, map_zero]

/-- [proved-derived; formal-checked] A cellular reduction therefore constructs all six genuine
degree-four coordinate-pair classes on the fourfold sphere power. -/
def fourfoldPairClassesOfReduction (reduction : SphereProductCellularReduction) :
    CoordinatePair 4 → SpherePowerH4 4 :=
  pairCoordinateHomologyFamily (sourceFourCycleOfReduction reduction)

section Audit

#print axioms coordinatePair_four_card
#print axioms pairCoordinate_then_matching_projection
#print axioms pairCoordinateChainMap_matching_retract
#print axioms pairCoordinateChain_closed
#print axioms pairCoordinateHomologyMap_matching_retract
#print axioms pairCoordinateHomologyMap_injective
#print axioms crossedPairTopMap_factorsThroughSphere
#print axioms crossedPairChainMap_factorsThroughSphere
#print axioms crossedPairHomologyMap_factorsThroughSphereH4
#print axioms crossedPairHomologyMap_eq_zero_of_sphereH4_subsingleton
#print axioms coordinatePairClassMap_injective
#print axioms sphereH4SubsingletonOfFillings
#print axioms surfaceCellHomologyIsoQFour
#print axioms sphereProductH4EquivQOfReduction
#print axioms sourceFourHomologyClassOfReduction_ne_zero
#print axioms coordinatePairClassMapOfReduction_injective
#print axioms coordinatePairClassMapOfReductions_surjective
#print axioms coordinatePairHomologyEquivOfReductions
#print axioms cellFourGenerator_closed
#print axioms sourceFourCycleOfReduction
#print axioms fourfoldPairClassesOfReduction

end Audit

end Soma.Holonics.Millennium.HodgeSpherePowerPairHomology
