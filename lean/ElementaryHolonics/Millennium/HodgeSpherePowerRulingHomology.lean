import ElementaryHolonics.Millennium.HodgeProjectiveLinePowerType11
import ElementaryHolonics.Millennium.HodgeRefinedBoundaryObstruction
import ElementaryHolonics.Millennium.HodgeSphereHomologyEquivalence
import ElementaryHolonics.Millennium.HodgeProductRulingDecomposition
import ElementaryHolonics.Millennium.HodgeSphereProductFiniteComplex
import Mathlib.Data.Fintype.Powerset

/-!
# Genuine coordinate ruling classes on every finite sphere power

The finite-power analytic ledger is now attached to actual rational singular-homology classes.
For every factor of `(S²)^n`, the tetrahedral fundamental cycle is pushed through the coordinate
inclusion with every other coordinate fixed at the retained basepoint.  Coordinate projections
return the matching sphere cycle and annihilate every crossed ruling already at chain level.

Consequently the complete coordinate-ruling map `Fin n → ℚ ⟶ H₂((S²)^n; ℚ)` is injective for
every finite `n`.  The source-level product normalization then propagates exact surjectivity from
the first two powers across every positive finite successor, returning a genuine linear
equivalence rather than a dimension count.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgeSpherePowerRulingHomology

open CategoryTheory CategoryTheory.Limits
open Simplicial
open Soma.Holonics.Millennium.HodgeProjectiveLineSingularReduction
open Soma.Holonics.Millennium.HodgeTwoSphereFundamentalCycle
open Soma.Holonics.Millennium.HodgeSphereProductRulingCycles
open Soma.Holonics.Millennium.HodgeSphereProductRulingProjections
open Soma.Holonics.Millennium.HodgeSphereHomologyEquivalence
open Soma.Holonics.Millennium.HodgeSphereProductRulingHomology
open Soma.Holonics.Millennium.HodgeProductRulingDecomposition
open Soma.Holonics.Millennium.HodgeProductDiagonal
open Soma.Holonics.Millennium.HodgeProductMixedFilling
open Soma.Holonics.Millennium.HodgeSphereProductFiniteComplex
open Soma.Holonics.DiagonalChainTransport

/-- [definition] The actual finite product of two-spheres. -/
abbrev SpherePower (factorCount : ℕ) :=
  Fin factorCount → HodgeTwoSphereFundamentalCycle.TwoSphere

/-- [definition] The topological carrier of the finite sphere power. -/
abbrev spherePowerTopCat (factorCount : ℕ) : TopCat :=
  TopCat.of (SpherePower factorCount)

/-- [definition] Genuine rational singular chains on the finite sphere power. -/
abbrev SpherePowerChains (factorCount : ℕ) :=
  ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℚ)).obj
    rationalCoefficient).obj (spherePowerTopCat factorCount)

/-! ## The complete graded cell family behind every finite sphere power -/

/-- [definition] A degree-`d` cell in `(S²)^n` is the exact subset of sphere factors contributing
their two-dimensional cell, with the equality `2 * card = d` retained as incidence data. -/
abbrev SpherePowerCellIndex (factorCount degree : ℕ) :=
  { support : Finset (Fin factorCount) // 2 * support.card = degree }

/-- [definition] The rational current carried by all addressed cells at one degree. -/
def spherePowerCellModule (factorCount degree : ℕ) : ModuleCat ℚ :=
  ModuleCat.of ℚ (SpherePowerCellIndex factorCount degree → ℚ)

/-- [definition] The whole finite sphere-power cellular complex.  Every boundary is zero because
each factor contributes cells only in degrees zero and two. -/
def spherePowerCellComplex (factorCount : ℕ) : ChainComplex (ModuleCat ℚ) ℕ :=
  ChainComplex.of (spherePowerCellModule factorCount) (fun _ => 0) (fun _ => by simp)

theorem spherePowerCellComplex_d (factorCount degree : ℕ) :
    (spherePowerCellComplex factorCount).d (degree + 1) degree = 0 := by
  exact ChainComplex.of_d (spherePowerCellModule factorCount) (fun _ => 0) degree

/-- [proved-derived; formal-checked] One theorem computes cellular homology in every degree. -/
def spherePowerCellHomologyIsoModule (factorCount degree : ℕ) :
    (spherePowerCellComplex factorCount).homology degree ≅
      spherePowerCellModule factorCount degree :=
  match degree with
  | 0 =>
      ((spherePowerCellComplex factorCount).isoHomologyπ 1 0 (by simp)
        (spherePowerCellComplex_d factorCount 0)).symm ≪≫
        (spherePowerCellComplex factorCount).cycles₀Iso
  | degree + 1 =>
      ((spherePowerCellComplex factorCount).isoHomologyπ
        (degree + 2) (degree + 1) (by simp)
        (spherePowerCellComplex_d factorCount (degree + 1))).symm ≪≫
        (spherePowerCellComplex factorCount).iCyclesIso
          (degree + 1) degree (by simp)
          (spherePowerCellComplex_d factorCount degree)

/-- [definition] The single source residual for the whole graded family. -/
abbrev SpherePowerCellularReduction (factorCount : ℕ) :=
  HomotopyEquiv (SpherePowerChains factorCount) (spherePowerCellComplex factorCount)

/-- [proved-derived; formal-checked] One cellular reduction computes genuine rational singular
homology at every degree. -/
def spherePowerHomologyEquivCellModule (factorCount : ℕ)
    (reduction : SpherePowerCellularReduction factorCount) (degree : ℕ) :
    (SpherePowerChains factorCount).homology degree ≃ₗ[ℚ]
      SpherePowerCellIndex factorCount degree → ℚ :=
  (reduction.toHomologyIso degree).toLinearEquiv.trans
    (spherePowerCellHomologyIsoModule factorCount degree).toLinearEquiv

/-- [proved-derived; formal-checked] Even degree `2k` has one cell for each exact `k`-subset. -/
def spherePowerEvenCellIndexEquiv (factorCount halfDegree : ℕ) :
    SpherePowerCellIndex factorCount (2 * halfDegree) ≃
      { support : Finset (Fin factorCount) // support.card = halfDegree } where
  toFun cell := ⟨cell.1, by omega⟩
  invFun support := ⟨support.1, by omega⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem spherePowerEvenCellIndex_card (factorCount halfDegree : ℕ) :
    Fintype.card (SpherePowerCellIndex factorCount (2 * halfDegree)) =
      Nat.choose factorCount halfDegree := by
  rw [Fintype.card_congr (spherePowerEvenCellIndexEquiv factorCount halfDegree)]
  simpa using (Fintype.card_finset_len (α := Fin factorCount) halfDegree)

theorem spherePowerCellModule_finrank_even (factorCount halfDegree : ℕ) :
    Module.finrank ℚ (spherePowerCellModule factorCount (2 * halfDegree)) =
      Nat.choose factorCount halfDegree := by
  change Module.finrank ℚ
    (SpherePowerCellIndex factorCount (2 * halfDegree) → ℚ) = _
  rw [Module.finrank_fintype_fun_eq_card,
    spherePowerEvenCellIndex_card factorCount halfDegree]

theorem spherePowerOddCellIndex_isEmpty (factorCount halfDegree : ℕ) :
    IsEmpty (SpherePowerCellIndex factorCount (2 * halfDegree + 1)) := by
  constructor
  intro cell
  omega

theorem spherePowerCellModule_finrank_odd (factorCount halfDegree : ℕ) :
    Module.finrank ℚ (spherePowerCellModule factorCount (2 * halfDegree + 1)) = 0 := by
  letI : IsEmpty (SpherePowerCellIndex factorCount (2 * halfDegree + 1)) :=
    spherePowerOddCellIndex_isEmpty factorCount halfDegree
  change Module.finrank ℚ
    (SpherePowerCellIndex factorCount (2 * halfDegree + 1) → ℚ) = 0
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_eq_zero]

/-- [proved-derived; formal-checked] The rank receiver of adjoining one sphere obeys Pascal
induction, the binary partition according to whether the new factor participates. -/
theorem spherePowerCellModule_pascal (factorCount halfDegree : ℕ) :
    Module.finrank ℚ
        (spherePowerCellModule (factorCount + 1) (2 * (halfDegree + 1))) =
      Module.finrank ℚ
          (spherePowerCellModule factorCount (2 * halfDegree)) +
        Module.finrank ℚ
          (spherePowerCellModule factorCount (2 * (halfDegree + 1))) := by
  rw [spherePowerCellModule_finrank_even,
    spherePowerCellModule_finrank_even,
    spherePowerCellModule_finrank_even]
  exact Nat.choose_succ_succ' factorCount halfDegree

/-- [definition] Insert one sphere into an addressed coordinate and hold every other coordinate
at the retained geometric basepoint. -/
def coordinateRulingContinuousMap {factorCount : ℕ} (index : Fin factorCount) :
    C(HodgeTwoSphereFundamentalCycle.TwoSphere, SpherePower factorCount) where
  toFun point coordinate := if coordinate = index then point else sphereBasepoint
  continuous_toFun := by
    apply continuous_pi
    intro coordinate
    by_cases hcoordinate : coordinate = index
    · simp only [hcoordinate, if_pos]
      exact continuous_id'
    · simp only [hcoordinate]
      exact continuous_const

/-- [definition] Project the finite sphere power to one addressed coordinate. -/
def coordinateProjectionContinuousMap {factorCount : ℕ} (index : Fin factorCount) :
    C(SpherePower factorCount, HodgeTwoSphereFundamentalCycle.TwoSphere) where
  toFun point := point index
  continuous_toFun := continuous_apply index

def coordinateRulingTopMap {factorCount : ℕ} (index : Fin factorCount) :
    sphereTopCat ⟶ spherePowerTopCat factorCount :=
  TopCat.ofHom (coordinateRulingContinuousMap index)

def coordinateProjectionTopMap {factorCount : ℕ} (index : Fin factorCount) :
    spherePowerTopCat factorCount ⟶ sphereTopCat :=
  TopCat.ofHom (coordinateProjectionContinuousMap index)

/-- [proved-derived; formal-checked] Matching inclusion and projection are an exact retraction. -/
theorem coordinate_ruling_then_matching_projection {factorCount : ℕ}
    (index : Fin factorCount) :
    coordinateRulingTopMap index ≫ coordinateProjectionTopMap index = 𝟙 sphereTopCat := by
  ext point
  change (if index = index then point else sphereBasepoint) = point
  simp

/-- [proved-derived; formal-checked] On the one-factor power, the matching projection and
coordinate insertion are inverse in the opposite order as well.  This is the exact base case for
the finite-power successor construction. -/
theorem singleton_projection_then_coordinate_ruling :
    coordinateProjectionTopMap (0 : Fin 1) ≫ coordinateRulingTopMap (0 : Fin 1) =
      𝟙 (spherePowerTopCat 1) := by
  ext point coordinate
  have hcoordinate : coordinate = (0 : Fin 1) := Subsingleton.elim _ _
  subst coordinate
  rfl

/-- [proved-derived; formal-checked] A crossed coordinate projection is the retained constant
sphere map. -/
theorem coordinate_ruling_then_crossed_projection {factorCount : ℕ}
    {source target : Fin factorCount} (hne : target ≠ source) :
    coordinateRulingTopMap source ≫ coordinateProjectionTopMap target =
      constantSphereTopMap := by
  ext point
  change (if target = source then
      (point : HodgeTwoSphereFundamentalCycle.TwoSphere) else sphereBasepoint) =
    sphereBasepoint
  simp only [hne]
  simp
  apply Subtype.ext
  rfl

/-- [definition] Functorial singular-chain insertion into one coordinate. -/
def coordinateRulingChainMap {factorCount : ℕ} (index : Fin factorCount) :
    SphereSingularChainComplex ⟶ SpherePowerChains factorCount :=
  ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℚ)).obj
    rationalCoefficient).map (coordinateRulingTopMap index)

/-- [definition] Functorial singular-chain projection from one coordinate. -/
def coordinateProjectionChainMap {factorCount : ℕ} (index : Fin factorCount) :
    SpherePowerChains factorCount ⟶ SphereSingularChainComplex :=
  ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℚ)).obj
    rationalCoefficient).map (coordinateProjectionTopMap index)

/-- [proved-derived; formal-checked] Matching chain transport is the identity. -/
theorem coordinateRulingChainMap_matching_retract {factorCount : ℕ}
    (index : Fin factorCount) :
    coordinateRulingChainMap index ≫ coordinateProjectionChainMap index =
      𝟙 SphereSingularChainComplex := by
  change
    ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℚ)).obj
        rationalCoefficient).map (coordinateRulingTopMap index) ≫
      ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℚ)).obj
        rationalCoefficient).map (coordinateProjectionTopMap index) = _
  rw [← Functor.map_comp, coordinate_ruling_then_matching_projection]
  simp

/-- [proved-derived; formal-checked] The one-factor projection followed by insertion is the
identity on the genuine singular-chain complex. -/
theorem singleton_projectionChainMap_then_coordinateRulingChainMap :
    coordinateProjectionChainMap (0 : Fin 1) ≫
        coordinateRulingChainMap (0 : Fin 1) =
      𝟙 (SpherePowerChains 1) := by
  change
    ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℚ)).obj
        rationalCoefficient).map (coordinateProjectionTopMap (0 : Fin 1)) ≫
      ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℚ)).obj
        rationalCoefficient).map (coordinateRulingTopMap (0 : Fin 1)) = _
  rw [← Functor.map_comp, singleton_projection_then_coordinate_ruling]
  simp

/-- [proved-derived; formal-checked] Crossed chain transport is the constant sphere chain map. -/
theorem coordinateRulingChainMap_crossed_retract {factorCount : ℕ}
    {source target : Fin factorCount} (hne : target ≠ source) :
    coordinateRulingChainMap source ≫ coordinateProjectionChainMap target =
      constantSphereChainMap := by
  change
    ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℚ)).obj
        rationalCoefficient).map (coordinateRulingTopMap source) ≫
      ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℚ)).obj
        rationalCoefficient).map (coordinateProjectionTopMap target) = _
  rw [← Functor.map_comp, coordinate_ruling_then_crossed_projection hne]
  rfl

/-- [definition] The actual tetrahedral sphere cycle in one finite-power coordinate. -/
def coordinateRulingCycle {factorCount : ℕ} (index : Fin factorCount) :
    (SpherePowerChains factorCount).X 2 :=
  (coordinateRulingChainMap index).f 2 sphereFundamentalCandidate

/-- [proved-derived; formal-checked] Every coordinate ruling is a genuine singular cycle. -/
theorem coordinateRulingCycle_boundary_zero {factorCount : ℕ}
    (index : Fin factorCount) :
    (SpherePowerChains factorCount).d 2 1 (coordinateRulingCycle index) = 0 := by
  change ((coordinateRulingChainMap index).f 2 ≫
    (SpherePowerChains factorCount).d 2 1) sphereFundamentalCandidate = 0
  rw [(coordinateRulingChainMap index).comm 2 1]
  change (coordinateRulingChainMap index).f 1
    (SphereSingularChainComplex.d 2 1 sphereFundamentalCandidate) = 0
  rw [sphereFundamentalCandidate_boundary_zero, map_zero]

/-- [proved-derived; formal-checked] Matching projection returns the exact source cycle. -/
theorem matching_projection_coordinateRulingCycle {factorCount : ℕ}
    (index : Fin factorCount) :
    (coordinateProjectionChainMap index).f 2 (coordinateRulingCycle index) =
      sphereFundamentalCandidate := by
  change (coordinateRulingChainMap index ≫ coordinateProjectionChainMap index).f 2
    sphereFundamentalCandidate = sphereFundamentalCandidate
  rw [coordinateRulingChainMap_matching_retract]
  rfl

/-- [proved-derived; formal-checked] Every crossed projection vanishes at chain level. -/
theorem crossed_projection_coordinateRulingCycle {factorCount : ℕ}
    {source target : Fin factorCount} (hne : target ≠ source) :
    (coordinateProjectionChainMap target).f 2 (coordinateRulingCycle source) = 0 := by
  change (coordinateRulingChainMap source ≫ coordinateProjectionChainMap target).f 2
    sphereFundamentalCandidate = 0
  rw [coordinateRulingChainMap_crossed_retract hne]
  exact constantSphereChainMap_fundamentalCandidate_zero

abbrev ScalarModule := ModuleCat.of ℚ ℚ

/-- [definition] Genuine rational degree-two singular homology of the finite sphere power. -/
abbrev SpherePowerH2 (factorCount : ℕ) : ModuleCat ℚ :=
  HomologicalComplex.homology (SpherePowerChains factorCount) 2

/-- [definition] The exact categorical target used by the sphere chain complex. -/
abbrev SphereH2 : ModuleCat ℚ :=
  HomologicalComplex.homology SphereSingularChainComplex 2

def powerChainElementMorphism {factorCount : ℕ}
    (chain : (SpherePowerChains factorCount).X 2) :
    ScalarModule ⟶ (SpherePowerChains factorCount).X 2 :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ _ chain)

theorem powerChainElementMorphism_comp_boundary_eq_zero {factorCount : ℕ}
    (chain : (SpherePowerChains factorCount).X 2)
    (hchain : (SpherePowerChains factorCount).d 2 1 chain = 0) :
    powerChainElementMorphism chain ≫ (SpherePowerChains factorCount).d 2 1 = 0 := by
  ext
  change (SpherePowerChains factorCount).d 2 1 ((1 : ℚ) • chain) = 0
  simpa using hchain

def powerCycleLift {factorCount : ℕ}
    (chain : (SpherePowerChains factorCount).X 2)
    (hchain : (SpherePowerChains factorCount).d 2 1 chain = 0) :
    ScalarModule ⟶ (SpherePowerChains factorCount).cycles 2 :=
  (SpherePowerChains factorCount).liftCycles (powerChainElementMorphism chain) 1 (by simp)
    (powerChainElementMorphism_comp_boundary_eq_zero chain hchain)

theorem powerCycleLift_i {factorCount : ℕ}
    (chain : (SpherePowerChains factorCount).X 2)
    (hchain : (SpherePowerChains factorCount).d 2 1 chain = 0) :
    powerCycleLift chain hchain ≫ (SpherePowerChains factorCount).iCycles 2 =
      powerChainElementMorphism chain := by
  apply HomologicalComplex.liftCycles_i

def coordinateRulingHomologyMorphism {factorCount : ℕ} (index : Fin factorCount) :
    ScalarModule ⟶ SpherePowerH2 factorCount :=
  powerCycleLift (coordinateRulingCycle index)
      (coordinateRulingCycle_boundary_zero index) ≫
    (SpherePowerChains factorCount).homologyπ 2

def coordinateRulingHomologyClass {factorCount : ℕ} (index : Fin factorCount) :
    SpherePowerH2 factorCount :=
  coordinateRulingHomologyMorphism index 1

def coordinateProjectionHomologyMap {factorCount : ℕ} (index : Fin factorCount) :
    SpherePowerH2 factorCount ⟶
      SphereH2 :=
  HomologicalComplex.homologyMap (coordinateProjectionChainMap index) 2

/-- [definition] The tetrahedral sphere class in the exact homology object returned by the
standing sphere chain complex. -/
def sphereFundamentalH2Morphism : ScalarModule ⟶ SphereH2 :=
  sphereCycleLift ≫ SphereSingularChainComplex.homologyπ 2

def sphereFundamentalH2Class : SphereH2 :=
  sphereFundamentalH2Morphism 1

theorem sphereFundamentalH2Class_ne_zero : sphereFundamentalH2Class ≠ 0 := by
  exact HodgeRefinedBoundaryObstruction.sphereFundamentalHomologyClass_ne_zero

theorem coordinateRuling_cyclesMap_matching {factorCount : ℕ}
    (index : Fin factorCount) :
    powerCycleLift (coordinateRulingCycle index)
          (coordinateRulingCycle_boundary_zero index) ≫
        HomologicalComplex.cyclesMap (coordinateProjectionChainMap index) 2 =
      sphereCycleLift := by
  apply (cancel_mono (SphereSingularChainComplex.iCycles 2)).1
  rw [Category.assoc, HomologicalComplex.cyclesMap_i]
  rw [← Category.assoc, powerCycleLift_i, sphereCycleLift_i]
  ext
  change (coordinateProjectionChainMap index).f 2
      ((1 : ℚ) • coordinateRulingCycle index) =
    (1 : ℚ) • sphereFundamentalCandidate
  simpa using matching_projection_coordinateRulingCycle index

theorem coordinateRuling_cyclesMap_crossed {factorCount : ℕ}
    {source target : Fin factorCount} (hne : target ≠ source) :
    powerCycleLift (coordinateRulingCycle source)
          (coordinateRulingCycle_boundary_zero source) ≫
        HomologicalComplex.cyclesMap (coordinateProjectionChainMap target) 2 = 0 := by
  apply (cancel_mono (SphereSingularChainComplex.iCycles 2)).1
  rw [Category.assoc, HomologicalComplex.cyclesMap_i, zero_comp]
  rw [← Category.assoc, powerCycleLift_i]
  ext
  change (coordinateProjectionChainMap target).f 2
      ((1 : ℚ) • coordinateRulingCycle source) = 0
  simpa using crossed_projection_coordinateRulingCycle hne

/-- [proved-derived; formal-checked] Matching projection returns the genuine sphere homology
class. -/
theorem coordinateProjection_coordinateRulingHomologyClass {factorCount : ℕ}
    (index : Fin factorCount) :
    coordinateProjectionHomologyMap index (coordinateRulingHomologyClass index) =
      sphereFundamentalH2Class := by
  have hraw :
      (powerCycleLift (coordinateRulingCycle index)
          (coordinateRulingCycle_boundary_zero index) ≫
        (SpherePowerChains factorCount).homologyπ 2) ≫
          coordinateProjectionHomologyMap index =
        sphereFundamentalH2Morphism := by
    unfold coordinateProjectionHomologyMap
    rw [Category.assoc, HomologicalComplex.homologyπ_naturality]
    rw [← Category.assoc, coordinateRuling_cyclesMap_matching]
    rfl
  change ((powerCycleLift (coordinateRulingCycle index)
      (coordinateRulingCycle_boundary_zero index) ≫
        (SpherePowerChains factorCount).homologyπ 2) ≫
      coordinateProjectionHomologyMap index) 1 =
    sphereFundamentalH2Morphism 1
  rw [hraw]

/-- [proved-derived; formal-checked] Crossed projection annihilates the genuine ruling homology
class. -/
theorem coordinateProjection_crossedRulingHomologyClass {factorCount : ℕ}
    {source target : Fin factorCount} (hne : target ≠ source) :
    coordinateProjectionHomologyMap target (coordinateRulingHomologyClass source) = 0 := by
  have hraw :
      (powerCycleLift (coordinateRulingCycle source)
          (coordinateRulingCycle_boundary_zero source) ≫
        (SpherePowerChains factorCount).homologyπ 2) ≫
          coordinateProjectionHomologyMap target = 0 := by
    unfold coordinateProjectionHomologyMap
    rw [Category.assoc, HomologicalComplex.homologyπ_naturality]
    rw [← Category.assoc, coordinateRuling_cyclesMap_crossed hne, zero_comp]
  change ((powerCycleLift (coordinateRulingCycle source)
      (coordinateRulingCycle_boundary_zero source) ≫
        (SpherePowerChains factorCount).homologyπ 2) ≫
      coordinateProjectionHomologyMap target) 1 = 0
  rw [hraw]
  rfl

/-- [proved-derived; formal-checked] The one-factor coordinate projection is injective on genuine
rational singular homology because its coordinate insertion is an actual chain-level inverse. -/
theorem singleton_coordinateProjectionHomologyMap_injective :
    Function.Injective (coordinateProjectionHomologyMap (0 : Fin 1)) := by
  intro left right hequal
  have hinverse :
      coordinateProjectionHomologyMap (0 : Fin 1) ≫
          HomologicalComplex.homologyMap
            (coordinateRulingChainMap (0 : Fin 1)) 2 =
        𝟙 (SpherePowerH2 1) := by
    unfold coordinateProjectionHomologyMap
    rw [← HomologicalComplex.homologyMap_comp]
    rw [singleton_projectionChainMap_then_coordinateRulingChainMap]
    exact HomologicalComplex.homologyMap_id (SpherePowerChains 1) 2
  have := congrArg
    (fun received =>
      (HomologicalComplex.homologyMap
        (coordinateRulingChainMap (0 : Fin 1)) 2) received) hequal
  change
    (coordinateProjectionHomologyMap (0 : Fin 1) ≫
      HomologicalComplex.homologyMap
        (coordinateRulingChainMap (0 : Fin 1)) 2) left =
    (coordinateProjectionHomologyMap (0 : Fin 1) ≫
      HomologicalComplex.homologyMap
        (coordinateRulingChainMap (0 : Fin 1)) 2) right at this
  rw [hinverse] at this
  exact this

/-- [definition] The complete finite coordinate population mapped to genuine rational singular
homology. -/
def spherePowerRulingHomologyMap (factorCount : ℕ) :
    (Fin factorCount → ℚ) →ₗ[ℚ]
      SpherePowerH2 factorCount where
  toFun coefficients := ∑ index, coefficients index • coordinateRulingHomologyClass index
  map_add' left right := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' coefficient coefficients := by
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul, mul_smul,
      Finset.smul_sum]

/-- [proved-derived; formal-checked] Each coordinate projection reads exactly one coefficient
times the nonzero sphere class. -/
theorem coordinateProjection_spherePowerRulingHomologyMap {factorCount : ℕ}
    (coefficients : Fin factorCount → ℚ) (index : Fin factorCount) :
    coordinateProjectionHomologyMap index
      (spherePowerRulingHomologyMap factorCount coefficients) =
      coefficients index • sphereFundamentalH2Class := by
  classical
  change coordinateProjectionHomologyMap index
      (∑ source, coefficients source • coordinateRulingHomologyClass source) = _
  rw [map_sum]
  simp_rw [map_smul]
  rw [Finset.sum_eq_single index]
  · rw [coordinateProjection_coordinateRulingHomologyClass]
  · intro source _ hsource
    rw [coordinateProjection_crossedRulingHomologyClass
      (source := source) (target := index) hsource.symm, smul_zero]
  · simp

/-- [proved-derived; formal-checked] Coordinate ruling classes are linearly independent in the
genuine rational singular homology of every finite sphere power. -/
theorem spherePowerRulingHomologyMap_injective (factorCount : ℕ) :
    Function.Injective (spherePowerRulingHomologyMap factorCount) := by
  intro left right hequal
  funext index
  have hprojection := congrArg
    (fun received => coordinateProjectionHomologyMap index received) hequal
  rw [coordinateProjection_spherePowerRulingHomologyMap,
    coordinateProjection_spherePowerRulingHomologyMap] at hprojection
  have hzero : (left index - right index) • sphereFundamentalH2Class = 0 := by
    rw [sub_smul, hprojection, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp hzero).resolve_right
    sphereFundamentalH2Class_ne_zero)

/-- [proved-derived; formal-checked] The genuine coordinate ruling map is onto for the one-factor
power.  This closes the nontrivial base of the finite-power Künneth induction using the already
proved exact sphere `H₂` coordinate, not a dimension count. -/
theorem spherePowerRulingHomologyMap_surjective_one :
    Function.Surjective (spherePowerRulingHomologyMap 1) := by
  intro received
  let projected : RationalSingularHomology 2 sphereTopCat :=
    coordinateProjectionHomologyMap (0 : Fin 1) received
  let coefficient : ℚ := sphereH2EquivQ projected
  let coefficients : Fin 1 → ℚ := fun _ => coefficient
  refine ⟨coefficients, singleton_coordinateProjectionHomologyMap_injective ?_⟩
  rw [coordinateProjection_spherePowerRulingHomologyMap]
  change coefficient • sphereFundamentalHomologyClass = projected
  apply sphereH2EquivQ.injective
  rw [map_smul]
  change coefficient * sphereH2EquivQ sphereFundamentalH2Class = coefficient
  rw [show sphereFundamentalH2Class = sphereFundamentalHomologyClass by rfl,
    sphereH2EquivQ_fundamental, mul_one]

/-- [proved-derived; formal-checked] A successor power is exactly the preceding power together
with one new addressed sphere.  The last coordinate is retained rather than silently reordered. -/
def spherePowerSuccessorHomeomorph (factorCount : ℕ) :
    (SpherePower factorCount ×
      HodgeProjectiveLineSingularReduction.TwoSphere) ≃ₜ
      SpherePower (factorCount + 1) where
  toFun pair := Fin.lastCases pair.2 pair.1
  invFun power :=
    (fun index => power index.castSucc, power (Fin.last factorCount))
  left_inv pair := by
    apply Prod.ext
    · funext index
      simp
    · simp
  right_inv power := by
    funext index
    cases index using Fin.lastCases <;> simp
  continuous_toFun := by
    apply continuous_pi
    intro index
    refine Fin.lastCases ?_ (fun previous => ?_) index
    · simpa only [Fin.lastCases_last] using
        (continuous_snd : Continuous
          (fun pair : SpherePower factorCount ×
            HodgeProjectiveLineSingularReduction.TwoSphere => pair.2))
    · simp only [Fin.lastCases_castSucc]
      fun_prop
  continuous_invFun :=
    (continuous_pi fun index => continuous_apply index.castSucc).prodMk
      (continuous_apply (Fin.last factorCount))

/-- Insert the preceding power into the successor while holding the new last coordinate at the
same geometric basepoint used by every ruling. -/
def spherePowerPrefixContinuousMap (factorCount : ℕ) :
    C(SpherePower factorCount, SpherePower (factorCount + 1)) where
  toFun point := Fin.lastCases sphereBasepoint point
  continuous_toFun := by
    apply continuous_pi
    intro index
    refine Fin.lastCases ?_ (fun previous => ?_) index
    · simpa only [Fin.lastCases_last] using
        (continuous_const : Continuous
          (fun _ : SpherePower factorCount => sphereBasepoint))
    · simpa only [Fin.lastCases_castSucc] using continuous_apply previous

def spherePowerPrefixTopMap (factorCount : ℕ) :
    spherePowerTopCat factorCount ⟶ spherePowerTopCat (factorCount + 1) :=
  TopCat.ofHom (spherePowerPrefixContinuousMap factorCount)

def spherePowerPrefixChainMap (factorCount : ℕ) :
    SpherePowerChains factorCount ⟶ SpherePowerChains (factorCount + 1) :=
  ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℚ)).obj
    rationalCoefficient).map (spherePowerPrefixTopMap factorCount)

/-- [proved-derived; formal-checked] Prefix insertion preserves every old addressed ruling and
changes only its coordinate name from `i` to `i.castSucc`. -/
theorem coordinateRuling_then_spherePowerPrefix {factorCount : ℕ}
    (index : Fin factorCount) :
    coordinateRulingTopMap index ≫ spherePowerPrefixTopMap factorCount =
      coordinateRulingTopMap index.castSucc := by
  apply ConcreteCategory.hom_ext
  intro point
  funext coordinate
  let base : (sphereTopCat : Type) := sphereBasepoint
  change Fin.lastCases base
      (fun previous => if previous = index then point else base) coordinate =
    (if coordinate = index.castSucc then point else base)
  cases coordinate using Fin.lastCases
  · simp only [Fin.lastCases_last]
    have hne : Fin.last factorCount ≠ index.castSucc := by
      intro equality
      have valueEquality := congrArg Fin.val equality
      simp at valueEquality
      omega
    rw [if_neg hne]
  · simp only [Fin.lastCases_castSucc, Fin.castSucc_inj]

/-- [proved-derived; formal-checked] The same old-coordinate law holds on the complete singular
chain, before passage to homology. -/
theorem coordinateRulingChainMap_then_spherePowerPrefix {factorCount : ℕ}
    (index : Fin factorCount) :
    coordinateRulingChainMap index ≫ spherePowerPrefixChainMap factorCount =
      coordinateRulingChainMap index.castSucc := by
  change
    ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℚ)).obj
        rationalCoefficient).map (coordinateRulingTopMap index) ≫
      ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℚ)).obj
        rationalCoefficient).map (spherePowerPrefixTopMap factorCount) = _
  rw [← Functor.map_comp, coordinateRuling_then_spherePowerPrefix]
  rfl

/-- [proved-derived; formal-checked] The successor homeomorphism, oriented from the actual
successor carrier back to the preceding power and its last sphere factor. -/
def spherePowerSuccessorProductIso (factorCount : ℕ) :
    spherePowerTopCat (factorCount + 1) ≅
      topologicalProductTopCat (spherePowerTopCat factorCount) sphereTopCat :=
  (TopCat.isoOfHomeo (spherePowerSuccessorHomeomorph factorCount)).symm

/-- [proved-derived; formal-checked] Splitting prefix insertion through the successor chart and
then reading the preceding-power coordinate is exactly the identity passage. -/
theorem spherePowerPrefix_then_successorFirstProjection (factorCount : ℕ) :
    spherePowerPrefixTopMap factorCount ≫
        (spherePowerSuccessorProductIso factorCount).hom ≫
        topologicalFirstProjection (spherePowerTopCat factorCount) sphereTopCat =
      𝟙 (spherePowerTopCat factorCount) := by
  apply ConcreteCategory.hom_ext
  intro point
  simp [spherePowerPrefixTopMap, spherePowerPrefixContinuousMap,
    spherePowerSuccessorProductIso, spherePowerSuccessorHomeomorph,
    topologicalFirstProjection, topologicalFirstProjectionContinuousMap,
    TopCat.isoOfHomeo]
  change (fun index => Fin.lastCases sphereBasepoint point index.castSucc) = point
  funext index
  simp

/-- [proved-derived; formal-checked] The complementary successor coordinate of prefix insertion
is exactly the declared geometric basepoint. -/
theorem spherePowerPrefix_then_successorSecondProjection (factorCount : ℕ) :
    spherePowerPrefixTopMap factorCount ≫
        (spherePowerSuccessorProductIso factorCount).hom ≫
        topologicalSecondProjection (spherePowerTopCat factorCount) sphereTopCat =
      TopCat.const sphereBasepoint := by
  apply ConcreteCategory.hom_ext
  intro point
  simp [spherePowerPrefixTopMap, spherePowerPrefixContinuousMap,
    spherePowerSuccessorProductIso, spherePowerSuccessorHomeomorph,
    topologicalSecondProjection, topologicalSecondProjectionContinuousMap,
    TopCat.isoOfHomeo, TopCat.const]
  change Fin.lastCases sphereBasepoint point (Fin.last factorCount) = sphereBasepoint
  simp

/-- [proved-derived; formal-checked] The last-coordinate ruling becomes the all-basepoint
preceding power under the first successor projection. -/
theorem lastCoordinateRuling_then_successorFirstProjection (factorCount : ℕ) :
    coordinateRulingTopMap (Fin.last factorCount) ≫
        (spherePowerSuccessorProductIso factorCount).hom ≫
        topologicalFirstProjection (spherePowerTopCat factorCount) sphereTopCat =
      TopCat.const (fun _ : Fin factorCount => sphereBasepoint) := by
  apply ConcreteCategory.hom_ext
  intro point
  change (fun index : Fin factorCount =>
      if index.castSucc = Fin.last factorCount then point else sphereBasepoint) =
    fun _ => sphereBasepoint
  funext index
  simp
  rfl

/-- [proved-derived; formal-checked] The last-coordinate ruling is the identity on the new sphere
under the complementary successor projection. -/
theorem lastCoordinateRuling_then_successorSecondProjection (factorCount : ℕ) :
    coordinateRulingTopMap (Fin.last factorCount) ≫
        (spherePowerSuccessorProductIso factorCount).hom ≫
        topologicalSecondProjection (spherePowerTopCat factorCount) sphereTopCat =
      𝟙 sphereTopCat := by
  apply ConcreteCategory.hom_ext
  intro point
  change (if Fin.last factorCount = Fin.last factorCount then point else sphereBasepoint) = point
  simp

/-- [proved-derived; formal-checked] The same successor split on the exact rational coordinate
ledger.  This is the coefficient-side chart consumed by the future product reconstruction. -/
def spherePowerSuccessorCoefficients (factorCount : ℕ) :
    ((Fin factorCount → ℚ) × ℚ) ≃ₗ[ℚ] (Fin (factorCount + 1) → ℚ) where
  toFun pair := Fin.lastCases pair.2 pair.1
  invFun coefficients :=
    (fun index => coefficients index.castSucc,
      coefficients (Fin.last factorCount))
  left_inv pair := by
    apply Prod.ext
    · funext index
      simp
    · simp
  right_inv coefficients := by
    funext index
    cases index using Fin.lastCases <;> simp
  map_add' left right := by
    funext index
    cases index using Fin.lastCases <;> simp
  map_smul' coefficient coefficients := by
    funext index
    cases index using Fin.lastCases <;> simp

@[simp]
theorem spherePowerSuccessorCoefficients_castSucc (factorCount : ℕ)
    (coefficients : Fin factorCount → ℚ) (lastCoefficient : ℚ)
    (index : Fin factorCount) :
    spherePowerSuccessorCoefficients factorCount (coefficients, lastCoefficient)
        index.castSucc = coefficients index := by
  simp [spherePowerSuccessorCoefficients]

@[simp]
theorem spherePowerSuccessorCoefficients_last (factorCount : ℕ)
    (coefficients : Fin factorCount → ℚ) (lastCoefficient : ℚ) :
    spherePowerSuccessorCoefficients factorCount (coefficients, lastCoefficient)
        (Fin.last factorCount) = lastCoefficient := by
  simp [spherePowerSuccessorCoefficients]

/-- [proved-derived; formal-checked] The ordinary ordered pair and the two-address sphere power
are the same topological carrier, with the complete coordinate ordering retained. -/
def sphereProductPowerTwoHomeomorph :
    (HodgeProjectiveLineSingularReduction.TwoSphere ×
      HodgeProjectiveLineSingularReduction.TwoSphere) ≃ₜ SpherePower 2 where
  toFun pair index := Fin.cases pair.1 (fun _ => pair.2) index
  invFun power := (power 0, power 1)
  left_inv pair := by ext <;> rfl
  right_inv power := by
    funext index
    fin_cases index <;> rfl
  continuous_toFun := by
    apply continuous_pi
    intro index
    fin_cases index
    · exact continuous_fst
    · exact continuous_snd
  continuous_invFun := (continuous_apply 0).prodMk (continuous_apply 1)

def sphereProductPowerTwoTopIso :
    sphereProductTopCat ≅ spherePowerTopCat 2 :=
  TopCat.isoOfHomeo sphereProductPowerTwoHomeomorph

/-- [proved-derived; formal-checked] The actual two-address sphere power, oriented back to its
two factor chart for source-level contraction. -/
def spherePowerTwoProductIso :
    spherePowerTopCat 2 ≅
      topologicalProductTopCat sphereTopCat sphereTopCat :=
  sphereProductPowerTwoTopIso.symm

/-- The two-factor base realization for the recursive low-degree contraction. -/
def spherePowerTwoSimplexRealization :
    ProductSimplexRealization
      (topologicalFactorSSet (spherePowerTopCat 2)) SphereSSet SphereSSet :=
  homeomorphicTopologicalProductSimplexRealization
    (spherePowerTopCat 2) sphereTopCat sphereTopCat spherePowerTwoProductIso

/-- The successor realization retains the preceding finite power as its first factor and the
new addressed sphere as its second factor. -/
def spherePowerSuccessorSimplexRealization (factorCount : ℕ) :
    ProductSimplexRealization
      (topologicalFactorSSet (spherePowerTopCat (factorCount + 1)))
      (topologicalFactorSSet (spherePowerTopCat factorCount)) SphereSSet :=
  homeomorphicTopologicalProductSimplexRealization
    (spherePowerTopCat (factorCount + 1)) (spherePowerTopCat factorCount) sphereTopCat
    (spherePowerSuccessorProductIso factorCount)

/-- [proved-derived; formal-checked] Under the genuine successor product chart, inserting an
old-power simplex at the geometric basepoint is exactly the old simplex paired with the repeated
basepoint triangle. -/
theorem spherePowerPrefix_successorSimplexEquiv (factorCount : ℕ)
    (simplex : FactorSimplex
      (topologicalFactorSSet (spherePowerTopCat factorCount)) 2) :
    (spherePowerSuccessorSimplexRealization factorCount).simplexEquiv 2
        (topologicalSimplexMap (spherePowerPrefixTopMap factorCount) 2 simplex) =
      (simplex, repeatVertexTriangle rulingBasepointSimplex) := by
  apply Prod.ext
  · change topologicalSimplexMap
        (topologicalFirstProjection (spherePowerTopCat factorCount) sphereTopCat) 2
        (topologicalSimplexMap
          (spherePowerSuccessorProductIso factorCount).hom 2
          (topologicalSimplexMap (spherePowerPrefixTopMap factorCount) 2 simplex)) = simplex
    rw [← topologicalSimplexMap_comp, ← topologicalSimplexMap_comp,
      spherePowerPrefix_then_successorFirstProjection, topologicalSimplexMap_id]
  · change topologicalSimplexMap
        (topologicalSecondProjection (spherePowerTopCat factorCount) sphereTopCat) 2
        (topologicalSimplexMap
          (spherePowerSuccessorProductIso factorCount).hom 2
          (topologicalSimplexMap (spherePowerPrefixTopMap factorCount) 2 simplex)) =
      repeatVertexTriangle rulingBasepointSimplex
    rw [← topologicalSimplexMap_comp, ← topologicalSimplexMap_comp,
      spherePowerPrefix_then_successorSecondProjection]
    apply (TopCat.toSSetObjEquiv sphereTopCat
      (Opposite.op (SimplexCategory.mk 2))).injective
    apply ContinuousMap.ext
    intro point
    rfl

/-- [proved-derived; formal-checked] Prefix transport of a degree-two generator is literally the
normalized old-factor axis in the successor product current. -/
theorem spherePowerPrefixCurrentMap_generator (factorCount : ℕ)
    (simplex : FactorSimplex
      (topologicalFactorSSet (spherePowerTopCat factorCount)) 2) :
    topologicalCurrentMap (spherePowerPrefixTopMap factorCount) 2
        (generator simplex) =
      (realizedProductCurrentEquiv
        (spherePowerSuccessorSimplexRealization factorCount) 2).symm
        (rejoinTwo _ _
          (rightAxis
            (pairSecondBase sphereLowDegreeCurrentDatum (generator simplex)))) := by
  apply (realizedProductCurrentEquiv
    (spherePowerSuccessorSimplexRealization factorCount) 2).injective
  rw [topologicalCurrentMap_generator,
    realizedProductCurrentEquiv_generator, LinearEquiv.apply_symm_apply,
    spherePowerPrefix_successorSimplexEquiv]
  simp [DiagonalChainTransport.rightAxis, pairSecondBase, rejoinTwo,
    rejoinTwoAtom, sphereLowDegreeCurrentDatum]

/-- [proved-derived; formal-checked] The prefix identity holds for every finite addressed current,
not only for one generator. -/
theorem spherePowerPrefixCurrentMap (factorCount : ℕ)
    (current : FactorCurrent
      (topologicalFactorSSet (spherePowerTopCat factorCount)) 2) :
    topologicalCurrentMap (spherePowerPrefixTopMap factorCount) 2 current =
      (realizedProductCurrentEquiv
        (spherePowerSuccessorSimplexRealization factorCount) 2).symm
        (rejoinTwo _ _
          (rightAxis (pairSecondBase sphereLowDegreeCurrentDatum current))) := by
  induction current using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright =>
      simp only [map_add, hleft, hright]
  | single simplex coefficient =>
      rw [show Finsupp.single simplex coefficient =
          coefficient • generator simplex by simp [generator]]
      simp only [map_smul, spherePowerPrefixCurrentMap_generator]

/-- [proved-derived; formal-checked] Every finite sphere power with at least two factors carries
the exact degree-zero and degree-one contraction required by the degree-two product reduction.
The recursion composes genuine simplex charts, rather than repeating a separate left/right
calculation for every power. -/
noncomputable def spherePowerLowDegreeCurrentDatumFromTwo
    (extraFactorCount : ℕ) :
    LowDegreeCurrentDatum
      (topologicalFactorSSet (spherePowerTopCat (extraFactorCount + 2))) := by
  induction extraFactorCount with
  | zero =>
      exact realizedProductLowDegreeCurrentDatum spherePowerTwoSimplexRealization
        sphereLowDegreeCurrentDatum sphereLowDegreeCurrentDatum
  | succ preceding ih =>
      exact realizedProductLowDegreeCurrentDatum
        (spherePowerSuccessorSimplexRealization (preceding + 2)) ih
        sphereLowDegreeCurrentDatum

/-- The literal all-basepoint zero-simplex of a finite sphere power. -/
noncomputable def spherePowerBasepointSimplex (factorCount : ℕ) :
    Simplex (topologicalFactorSSet (spherePowerTopCat factorCount)) 0 :=
  TopCat.toSSetObj₀Equiv.symm (fun _ => sphereBasepoint)

/-- [proved-derived; formal-checked] Recursive low-degree contraction never drifts to a
choice-dependent origin: its retained basepoint is exactly the all-basepoint geometric
occurrence in every power. -/
theorem spherePowerLowDegreeCurrentDatumFromTwo_basepoint (extra : ℕ) :
    (spherePowerLowDegreeCurrentDatumFromTwo extra).basepoint =
      spherePowerBasepointSimplex (extra + 2) := by
  induction extra with
  | zero =>
      simp [spherePowerLowDegreeCurrentDatumFromTwo, spherePowerBasepointSimplex,
        spherePowerTwoSimplexRealization, spherePowerTwoProductIso,
        sphereProductPowerTwoTopIso, sphereProductPowerTwoHomeomorph,
        realizedProductLowDegreeCurrentDatum, realizedProductBasepoint,
        sphereLowDegreeCurrentDatum, rulingBasepointSimplex,
        homeomorphicTopologicalProductSimplexRealization,
        homeomorphicTopologicalProductSimplexEquiv]
      apply TopCat.toSSetObj₀Equiv.injective
      change (fun index : Fin 2 =>
        Fin.cases sphereBasepoint (fun _ => sphereBasepoint) index) =
          fun _ => sphereBasepoint
      funext index
      fin_cases index <;> rfl
  | succ preceding ih =>
      simp only [spherePowerLowDegreeCurrentDatumFromTwo]
      change realizedProductBasepoint
          (spherePowerSuccessorSimplexRealization (preceding + 2))
          (spherePowerLowDegreeCurrentDatumFromTwo preceding)
          sphereLowDegreeCurrentDatum = _
      unfold realizedProductBasepoint
      simp only [ih]
      simp [spherePowerBasepointSimplex, spherePowerSuccessorSimplexRealization,
        spherePowerSuccessorProductIso, spherePowerSuccessorHomeomorph,
        homeomorphicTopologicalProductSimplexRealization,
        homeomorphicTopologicalProductSimplexEquiv,
        sphereLowDegreeCurrentDatum, rulingBasepointSimplex]
      apply TopCat.toSSetObj₀Equiv.injective
      change Fin.lastCases sphereBasepoint (fun _ => sphereBasepoint) =
        fun _ => sphereBasepoint
      funext index
      cases index using Fin.lastCases <;> simp

/-- [proved-derived; formal-checked] Under the genuine successor product chart, the newest
coordinate ruling is the repeated all-basepoint simplex of the preceding power paired with the
original sphere simplex. -/
theorem lastCoordinateRuling_successorSimplexEquiv (factorCount : ℕ)
    (simplex : FactorSimplex SphereSSet 2) :
    (spherePowerSuccessorSimplexRealization factorCount).simplexEquiv 2
        (topologicalSimplexMap
          (coordinateRulingTopMap (Fin.last factorCount)) 2 simplex) =
      (repeatVertexTriangle (spherePowerBasepointSimplex factorCount), simplex) := by
  apply Prod.ext
  · change topologicalSimplexMap
        (topologicalFirstProjection (spherePowerTopCat factorCount) sphereTopCat) 2
        (topologicalSimplexMap
          (spherePowerSuccessorProductIso factorCount).hom 2
          (topologicalSimplexMap
            (coordinateRulingTopMap (Fin.last factorCount)) 2 simplex)) =
      repeatVertexTriangle (spherePowerBasepointSimplex factorCount)
    rw [← topologicalSimplexMap_comp, ← topologicalSimplexMap_comp,
      lastCoordinateRuling_then_successorFirstProjection]
    apply (TopCat.toSSetObjEquiv (spherePowerTopCat factorCount)
      (Opposite.op (SimplexCategory.mk 2))).injective
    apply ContinuousMap.ext
    intro point
    rfl
  · change topologicalSimplexMap
        (topologicalSecondProjection (spherePowerTopCat factorCount) sphereTopCat) 2
        (topologicalSimplexMap
          (spherePowerSuccessorProductIso factorCount).hom 2
          (topologicalSimplexMap
            (coordinateRulingTopMap (Fin.last factorCount)) 2 simplex)) = simplex
    rw [← topologicalSimplexMap_comp, ← topologicalSimplexMap_comp,
      lastCoordinateRuling_then_successorSecondProjection, topologicalSimplexMap_id]

/-- [proved-derived; formal-checked] Transport of a newest-coordinate generator is literally the
normalized new-factor axis in the successor product current.  The recursive datum contributes no
choice because its basepoint has already been identified with the all-basepoint simplex. -/
theorem lastCoordinateRulingCurrentMap_generator (extra : ℕ)
    (simplex : FactorSimplex SphereSSet 2) :
    topologicalCurrentMap
        (coordinateRulingTopMap (Fin.last (extra + 2))) 2 (generator simplex) =
      (realizedProductCurrentEquiv
        (spherePowerSuccessorSimplexRealization (extra + 2)) 2).symm
        (rejoinTwo _ _
          (leftAxis
            (DiagonalChainTransport.pairFirstBase
              (spherePowerLowDegreeCurrentDatumFromTwo extra)
              (generator simplex)))) := by
  apply (realizedProductCurrentEquiv
    (spherePowerSuccessorSimplexRealization (extra + 2)) 2).injective
  rw [topologicalCurrentMap_generator,
    realizedProductCurrentEquiv_generator, LinearEquiv.apply_symm_apply,
    lastCoordinateRuling_successorSimplexEquiv]
  simp [DiagonalChainTransport.leftAxis, DiagonalChainTransport.pairFirstBase, rejoinTwo,
    rejoinTwoAtom, spherePowerLowDegreeCurrentDatumFromTwo_basepoint]

/-- [proved-derived; formal-checked] The newest-coordinate identity holds for every finite sphere
current. -/
theorem lastCoordinateRulingCurrentMap (extra : ℕ)
    (current : FactorCurrent SphereSSet 2) :
    topologicalCurrentMap
        (coordinateRulingTopMap (Fin.last (extra + 2))) 2 current =
      (realizedProductCurrentEquiv
        (spherePowerSuccessorSimplexRealization (extra + 2)) 2).symm
        (rejoinTwo _ _
          (leftAxis
            (DiagonalChainTransport.pairFirstBase
              (spherePowerLowDegreeCurrentDatumFromTwo extra) current))) := by
  induction current using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright =>
      simp only [map_add, hleft, hright]
  | single simplex coefficient =>
      rw [show Finsupp.single simplex coefficient =
          coefficient • generator simplex by simp [generator]]
      simp only [map_smul, lastCoordinateRulingCurrentMap_generator]

/-- [proved-derived; formal-checked] Every closed degree-two chain on a successor sphere power
returns two closed factor chains and one explicit degree-three reconstruction witness.  This is
the source-specific local-to-global passage: the preceding-power and newest-sphere currents are
transported through their genuine geometric inclusions, and their difference from the received
chain is an exact boundary. -/
theorem exists_spherePowerSuccessorChainDecomposition (extra : ℕ)
    (sourceChain : (SpherePowerChains ((extra + 2) + 1)).X 2)
    (closed : (SpherePowerChains ((extra + 2) + 1)).d 2 1 sourceChain = 0) :
    ∃ (factorChain : (SpherePowerChains (extra + 2)).X 2)
      (sphereChain : SphereSingularChainComplex.X 2)
      (witness : (SpherePowerChains ((extra + 2) + 1)).X 3),
      (SpherePowerChains (extra + 2)).d 2 1 factorChain = 0 ∧
      SphereSingularChainComplex.d 2 1 sphereChain = 0 ∧
      (SpherePowerChains ((extra + 2) + 1)).d 3 2 witness =
        sourceChain -
          ((coordinateRulingChainMap (Fin.last (extra + 2))).f 2 sphereChain +
            (spherePowerPrefixChainMap (extra + 2)).f 2 factorChain) := by
  let sourceCurrent := topologicalChainEquivCurrent
    (spherePowerTopCat ((extra + 2) + 1)) 2 sourceChain
  let datumX := spherePowerLowDegreeCurrentDatumFromTwo extra
  let realization := spherePowerSuccessorSimplexRealization (extra + 2)
  let factorCurrent := realizedProductFirstFactorDegreeTwoCurrent
    realization datumX sphereLowDegreeCurrentDatum sourceCurrent
  let sphereCurrent := realizedProductSecondFactorDegreeTwoCurrent
    realization datumX sphereLowDegreeCurrentDatum sourceCurrent
  let factorChain := topologicalCurrentToChain
    (spherePowerTopCat (extra + 2)) 2 factorCurrent
  let sphereChain := topologicalCurrentToChain sphereTopCat 2 sphereCurrent
  let witness := topologicalCurrentToChain
    (spherePowerTopCat ((extra + 2) + 1)) 3
    (realizedProductDegreeTwoNormalizationFiller
      realization datumX sphereLowDegreeCurrentDatum sourceCurrent)
  have sourceCurrentClosed : factorBoundary
      (topologicalFactorSSet (spherePowerTopCat ((extra + 2) + 1))) 1
      sourceCurrent = 0 := by
    rw [← topologicalChainEquivCurrent_boundary]
    simp [closed]
  have factorCurrentClosed : factorBoundary
      (topologicalFactorSSet (spherePowerTopCat (extra + 2))) 1
      factorCurrent = 0 := by
    exact realizedProductFirstFactorDegreeTwoCurrent_closed
      realization datumX sphereLowDegreeCurrentDatum sourceCurrent sourceCurrentClosed
  have sphereCurrentClosed : factorBoundary SphereSSet 1 sphereCurrent = 0 := by
    exact realizedProductSecondFactorDegreeTwoCurrent_closed
      realization datumX sphereLowDegreeCurrentDatum sourceCurrent sourceCurrentClosed
  refine ⟨factorChain, sphereChain, witness, ?_, ?_, ?_⟩
  · apply (topologicalChainEquivCurrent (spherePowerTopCat (extra + 2)) 1).injective
    rw [topologicalChainEquivCurrent_boundary]
    rw [show topologicalChainEquivCurrent
          (spherePowerTopCat (extra + 2)) 2 factorChain = factorCurrent by
      change topologicalChainToCurrent (spherePowerTopCat (extra + 2)) 2
          (topologicalCurrentToChain (spherePowerTopCat (extra + 2)) 2 factorCurrent) =
        factorCurrent
      exact topologicalChain_current_roundtrip _ _ _]
    simpa using factorCurrentClosed
  · apply (topologicalChainEquivCurrent sphereTopCat 1).injective
    rw [topologicalChainEquivCurrent_boundary]
    rw [show topologicalChainEquivCurrent sphereTopCat 2 sphereChain = sphereCurrent by
      change topologicalChainToCurrent sphereTopCat 2
          (topologicalCurrentToChain sphereTopCat 2 sphereCurrent) = sphereCurrent
      exact topologicalChain_current_roundtrip _ _ _]
    simpa using sphereCurrentClosed
  · apply (topologicalChainEquivCurrent
      (spherePowerTopCat ((extra + 2) + 1)) 2).injective
    rw [topologicalChainEquivCurrent_boundary]
    rw [show topologicalChainEquivCurrent
          (spherePowerTopCat ((extra + 2) + 1)) 3 witness =
        realizedProductDegreeTwoNormalizationFiller
          realization datumX sphereLowDegreeCurrentDatum sourceCurrent by
      change topologicalChainToCurrent
          (spherePowerTopCat ((extra + 2) + 1)) 3
          (topologicalCurrentToChain
            (spherePowerTopCat ((extra + 2) + 1)) 3
            (realizedProductDegreeTwoNormalizationFiller
              realization datumX sphereLowDegreeCurrentDatum sourceCurrent)) = _
      exact topologicalChain_current_roundtrip _ _ _]
    simp only [map_sub, map_add]
    unfold coordinateRulingChainMap spherePowerPrefixChainMap
    rw [topologicalChainEquivCurrent_map, topologicalChainEquivCurrent_map]
    rw [show topologicalChainEquivCurrent
          (spherePowerTopCat ((extra + 2) + 1)) 2 sourceChain = sourceCurrent by rfl]
    rw [show topologicalChainEquivCurrent sphereTopCat 2 sphereChain = sphereCurrent by
      change topologicalChainToCurrent sphereTopCat 2
          (topologicalCurrentToChain sphereTopCat 2 sphereCurrent) = sphereCurrent
      exact topologicalChain_current_roundtrip _ _ _]
    rw [show topologicalChainEquivCurrent
          (spherePowerTopCat (extra + 2)) 2 factorChain = factorCurrent by
      change topologicalChainToCurrent (spherePowerTopCat (extra + 2)) 2
          (topologicalCurrentToChain
            (spherePowerTopCat (extra + 2)) 2 factorCurrent) = factorCurrent
      exact topologicalChain_current_roundtrip _ _ _]
    rw [lastCoordinateRulingCurrentMap, spherePowerPrefixCurrentMap]
    simpa only [map_add] using
      (realizedProductDegreeTwoNormalizationFiller_boundary
        realization datumX sphereLowDegreeCurrentDatum sourceCurrent sourceCurrentClosed)

/-- [proved-derived; formal-checked] The exact successor boundary witness descends to genuine
rational singular homology: every received class is the sum of one transported preceding-power
class and one transported newest-sphere class. -/
theorem exists_spherePowerSuccessorHomologyDecomposition (extra : ℕ)
    (received : SpherePowerH2 ((extra + 2) + 1)) :
    ∃ (factorClass : SpherePowerH2 (extra + 2)) (sphereClass : SphereH2),
      received =
        HomologicalComplex.homologyMap
            (coordinateRulingChainMap (Fin.last (extra + 2))) 2 sphereClass +
          HomologicalComplex.homologyMap
            (spherePowerPrefixChainMap (extra + 2)) 2 factorClass := by
  obtain ⟨sourceCycle, sourceClass⟩ :=
    (ModuleCat.epi_iff_surjective
      ((SpherePowerChains ((extra + 2) + 1)).homologyπ 2)).mp
        inferInstance received
  let sourceChain := (SpherePowerChains ((extra + 2) + 1)).iCycles 2 sourceCycle
  have sourceClosed :
      (SpherePowerChains ((extra + 2) + 1)).d 2 1 sourceChain = 0 := by
    change ((SpherePowerChains ((extra + 2) + 1)).iCycles 2 ≫
      (SpherePowerChains ((extra + 2) + 1)).d 2 1) sourceCycle = 0
    rw [(SpherePowerChains ((extra + 2) + 1)).iCycles_d]
    rfl
  obtain ⟨factorChain, sphereChain, witness,
      factorClosed, sphereClosed, boundary⟩ :=
    exists_spherePowerSuccessorChainDecomposition extra sourceChain sourceClosed
  let factorCycle := powerCycleLift factorChain factorClosed 1
  let sphereElementMorphism : ScalarModule ⟶ SphereSingularChainComplex.X 2 :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton ℚ _ sphereChain)
  have sphereElementBoundary : sphereElementMorphism ≫
      SphereSingularChainComplex.d 2 1 = 0 := by
    ext
    change SphereSingularChainComplex.d 2 1 ((1 : ℚ) • sphereChain) = 0
    simpa using sphereClosed
  let sphereCycleMorphism : ScalarModule ⟶ SphereSingularChainComplex.cycles 2 :=
    SphereSingularChainComplex.liftCycles sphereElementMorphism 1 (by simp)
      sphereElementBoundary
  let sphereCycle := sphereCycleMorphism 1
  let targetCycle : (SpherePowerChains ((extra + 2) + 1)).cycles 2 :=
    HomologicalComplex.cyclesMap
        (coordinateRulingChainMap (Fin.last (extra + 2))) 2 sphereCycle +
      HomologicalComplex.cyclesMap
        (spherePowerPrefixChainMap (extra + 2)) 2 factorCycle
  have factorInclusion :
      (SpherePowerChains (extra + 2)).iCycles 2 factorCycle = factorChain := by
    have law := congrArg (fun morphism => morphism (1 : ℚ))
      (powerCycleLift_i factorChain factorClosed)
    change (SpherePowerChains (extra + 2)).iCycles 2 factorCycle =
      (1 : ℚ) • factorChain at law
    simpa using law
  have sphereInclusion :
      SphereSingularChainComplex.iCycles 2 sphereCycle = sphereChain := by
    have liftLaw : sphereCycleMorphism ≫
        SphereSingularChainComplex.iCycles 2 = sphereElementMorphism := by
      apply HomologicalComplex.liftCycles_i
    have law := congrArg (fun morphism => morphism (1 : ℚ)) liftLaw
    change SphereSingularChainComplex.iCycles 2 sphereCycle =
      (1 : ℚ) • sphereChain at law
    simpa using law
  have targetInclusion :
      (SpherePowerChains ((extra + 2) + 1)).iCycles 2 targetCycle =
        (coordinateRulingChainMap (Fin.last (extra + 2))).f 2 sphereChain +
          (spherePowerPrefixChainMap (extra + 2)).f 2 factorChain := by
    simp only [targetCycle, map_add]
    change
      (HomologicalComplex.cyclesMap
          (coordinateRulingChainMap (Fin.last (extra + 2))) 2 ≫
        (SpherePowerChains ((extra + 2) + 1)).iCycles 2) sphereCycle +
      (HomologicalComplex.cyclesMap
          (spherePowerPrefixChainMap (extra + 2)) 2 ≫
        (SpherePowerChains ((extra + 2) + 1)).iCycles 2) factorCycle = _
    rw [HomologicalComplex.cyclesMap_i, HomologicalComplex.cyclesMap_i]
    change
      (coordinateRulingChainMap (Fin.last (extra + 2))).f 2
          (SphereSingularChainComplex.iCycles 2 sphereCycle) +
        (spherePowerPrefixChainMap (extra + 2)).f 2
          ((SpherePowerChains (extra + 2)).iCycles 2 factorCycle) = _
    rw [sphereInclusion, factorInclusion]
  have differenceIsBoundary :
      sourceCycle - targetCycle =
        (SpherePowerChains ((extra + 2) + 1)).toCycles 3 2 witness := by
    apply (ModuleCat.mono_iff_injective
      ((SpherePowerChains ((extra + 2) + 1)).iCycles 2)).mp inferInstance
    rw [map_sub, targetInclusion]
    change sourceChain -
        ((coordinateRulingChainMap (Fin.last (extra + 2))).f 2 sphereChain +
          (spherePowerPrefixChainMap (extra + 2)).f 2 factorChain) =
      ((SpherePowerChains ((extra + 2) + 1)).toCycles 3 2 ≫
        (SpherePowerChains ((extra + 2) + 1)).iCycles 2) witness
    rw [(SpherePowerChains ((extra + 2) + 1)).toCycles_i, boundary]
  have differenceVanishes :
      (SpherePowerChains ((extra + 2) + 1)).homologyπ 2
          (sourceCycle - targetCycle) = 0 := by
    rw [differenceIsBoundary]
    change ((SpherePowerChains ((extra + 2) + 1)).toCycles 3 2 ≫
      (SpherePowerChains ((extra + 2) + 1)).homologyπ 2) witness = 0
    rw [(SpherePowerChains ((extra + 2) + 1)).toCycles_comp_homologyπ]
    rfl
  have sameClass :
      (SpherePowerChains ((extra + 2) + 1)).homologyπ 2 sourceCycle =
        (SpherePowerChains ((extra + 2) + 1)).homologyπ 2 targetCycle := by
    rw [map_sub, sub_eq_zero] at differenceVanishes
    exact differenceVanishes
  let factorClass := (SpherePowerChains (extra + 2)).homologyπ 2 factorCycle
  let sphereClass := SphereSingularChainComplex.homologyπ 2 sphereCycle
  refine ⟨factorClass, sphereClass, ?_⟩
  have targetClass :
      (SpherePowerChains ((extra + 2) + 1)).homologyπ 2 targetCycle =
        HomologicalComplex.homologyMap
            (coordinateRulingChainMap (Fin.last (extra + 2))) 2 sphereClass +
          HomologicalComplex.homologyMap
            (spherePowerPrefixChainMap (extra + 2)) 2 factorClass := by
    simp only [targetCycle, map_add]
    change
      (HomologicalComplex.cyclesMap
          (coordinateRulingChainMap (Fin.last (extra + 2))) 2 ≫
        (SpherePowerChains ((extra + 2) + 1)).homologyπ 2) sphereCycle +
      (HomologicalComplex.cyclesMap
          (spherePowerPrefixChainMap (extra + 2)) 2 ≫
        (SpherePowerChains ((extra + 2) + 1)).homologyπ 2) factorCycle = _
    rw [← HomologicalComplex.homologyπ_naturality,
      ← HomologicalComplex.homologyπ_naturality]
    rfl
  exact sourceClass.symm.trans (sameClass.trans targetClass)

/-- [proved-derived; formal-checked] Prefix transport carries each ruling cycle to the same
address under `Fin.castSucc`. -/
theorem coordinateRulingCyclesMap_then_spherePowerPrefix {factorCount : ℕ}
    (index : Fin factorCount) :
    powerCycleLift (coordinateRulingCycle index)
          (coordinateRulingCycle_boundary_zero index) ≫
        HomologicalComplex.cyclesMap (spherePowerPrefixChainMap factorCount) 2 =
      powerCycleLift (coordinateRulingCycle index.castSucc)
        (coordinateRulingCycle_boundary_zero index.castSucc) := by
  apply (cancel_mono ((SpherePowerChains (factorCount + 1)).iCycles 2)).1
  rw [Category.assoc, HomologicalComplex.cyclesMap_i]
  rw [← Category.assoc, powerCycleLift_i, powerCycleLift_i]
  ext
  change (spherePowerPrefixChainMap factorCount).f 2
      ((1 : ℚ) • coordinateRulingCycle index) =
    (1 : ℚ) • coordinateRulingCycle index.castSucc
  simp only [one_smul]
  have mapLaw := congrArg
    (fun chainMap => chainMap.f 2 sphereFundamentalCandidate)
    (coordinateRulingChainMap_then_spherePowerPrefix index)
  simpa [coordinateRulingCycle] using mapLaw

/-- [proved-derived; formal-checked] The same old-coordinate law descends to genuine rational
singular homology. -/
theorem spherePowerPrefixHomologyMap_coordinateRuling {factorCount : ℕ}
    (index : Fin factorCount) :
    HomologicalComplex.homologyMap (spherePowerPrefixChainMap factorCount) 2
        (coordinateRulingHomologyClass index) =
      coordinateRulingHomologyClass index.castSucc := by
  have hraw :
      coordinateRulingHomologyMorphism index ≫
          HomologicalComplex.homologyMap (spherePowerPrefixChainMap factorCount) 2 =
        coordinateRulingHomologyMorphism index.castSucc := by
    unfold coordinateRulingHomologyMorphism
    rw [Category.assoc, HomologicalComplex.homologyπ_naturality]
    rw [← Category.assoc, coordinateRulingCyclesMap_then_spherePowerPrefix]
  change (coordinateRulingHomologyMorphism index ≫
      HomologicalComplex.homologyMap (spherePowerPrefixChainMap factorCount) 2) 1 = _
  rw [hraw]
  rfl

/-- [proved-derived; formal-checked] Inserting the fundamental sphere cycle into the newest
coordinate gives exactly that coordinate's finite-power ruling cycle. -/
theorem sphereCycleMap_lastCoordinateRuling (factorCount : ℕ) :
    sphereCycleLift ≫
        HomologicalComplex.cyclesMap
          (coordinateRulingChainMap (Fin.last factorCount)) 2 =
      powerCycleLift (coordinateRulingCycle (Fin.last factorCount))
        (coordinateRulingCycle_boundary_zero (Fin.last factorCount)) := by
  apply (cancel_mono ((SpherePowerChains (factorCount + 1)).iCycles 2)).1
  rw [Category.assoc, HomologicalComplex.cyclesMap_i]
  rw [← Category.assoc, sphereCycleLift_i, powerCycleLift_i]
  ext
  change (coordinateRulingChainMap (Fin.last factorCount)).f 2
      ((1 : ℚ) • sphereFundamentalCandidate) =
    (1 : ℚ) • coordinateRulingCycle (Fin.last factorCount)
  simp [coordinateRulingCycle]

/-- [proved-derived; formal-checked] The newest-coordinate homology inclusion sends the sphere
fundamental class to the newest ruling class exactly. -/
theorem lastCoordinateRulingHomologyMap_fundamental (factorCount : ℕ) :
    HomologicalComplex.homologyMap
        (coordinateRulingChainMap (Fin.last factorCount)) 2 sphereFundamentalH2Class =
      coordinateRulingHomologyClass (Fin.last factorCount) := by
  have hraw : sphereFundamentalH2Morphism ≫
        HomologicalComplex.homologyMap
          (coordinateRulingChainMap (Fin.last factorCount)) 2 =
      coordinateRulingHomologyMorphism (Fin.last factorCount) := by
    unfold sphereFundamentalH2Morphism coordinateRulingHomologyMorphism
    rw [Category.assoc, HomologicalComplex.homologyπ_naturality]
    rw [← Category.assoc, sphereCycleMap_lastCoordinateRuling]
  change (sphereFundamentalH2Morphism ≫
      HomologicalComplex.homologyMap
        (coordinateRulingChainMap (Fin.last factorCount)) 2) 1 = _
  rw [hraw]
  rfl

/-- [proved-derived; formal-checked] Successor coefficient assembly is exact on genuine rational
singular homology.  The older coordinate current is transported through the prefix chart, while
the new addressed coefficient is transported through the last-coordinate ruling; no coordinate
population or reconstruction data is identified by a dimension count. -/
theorem spherePowerSuccessorHomologyMap_assembly (factorCount : ℕ)
    (oldCoefficients : Fin factorCount → ℚ) (lastCoefficient : ℚ) :
    spherePowerRulingHomologyMap (factorCount + 1)
        (spherePowerSuccessorCoefficients factorCount
          (oldCoefficients, lastCoefficient)) =
      HomologicalComplex.homologyMap
          (coordinateRulingChainMap (Fin.last factorCount)) 2
          (lastCoefficient • sphereFundamentalH2Class) +
        HomologicalComplex.homologyMap
          (spherePowerPrefixChainMap factorCount) 2
          (spherePowerRulingHomologyMap factorCount oldCoefficients) := by
  classical
  change
    (∑ index,
      spherePowerSuccessorCoefficients factorCount
          (oldCoefficients, lastCoefficient) index •
        coordinateRulingHomologyClass index) =
      HomologicalComplex.homologyMap
          (coordinateRulingChainMap (Fin.last factorCount)) 2
          (lastCoefficient • sphereFundamentalH2Class) +
        HomologicalComplex.homologyMap
          (spherePowerPrefixChainMap factorCount) 2
          (∑ index,
            oldCoefficients index • coordinateRulingHomologyClass index)
  rw [Fin.sum_univ_castSucc]
  simp only [spherePowerSuccessorCoefficients_castSucc,
    spherePowerSuccessorCoefficients_last]
  rw [map_sum, map_smul]
  simp_rw [map_smul, spherePowerPrefixHomologyMap_coordinateRuling]
  rw [lastCoordinateRulingHomologyMap_fundamental]
  module

/-- [proved-derived; formal-checked] Surjectivity propagates across one exact finite-power
successor.  The proof reconstructs the preceding coordinate population and the new sphere
coordinate separately from the source-level boundary witness, then rejoins them through the
ordered successor coefficient chart. -/
theorem spherePowerRulingHomologyMap_surjective_successor (extra : ℕ)
    (inductionHypothesis :
      Function.Surjective (spherePowerRulingHomologyMap (extra + 2))) :
    Function.Surjective
      (spherePowerRulingHomologyMap ((extra + 2) + 1)) := by
  intro received
  obtain ⟨factorClass, sphereClass, decomposition⟩ :=
    exists_spherePowerSuccessorHomologyDecomposition extra received
  obtain ⟨oldCoefficients, oldCoefficients_eq⟩ :=
    inductionHypothesis factorClass
  let sphereCoordinate : RationalSingularHomology 2 sphereTopCat := sphereClass
  let lastCoefficient : ℚ := sphereH2EquivQ sphereCoordinate
  have sphereClass_eq :
      sphereClass = lastCoefficient • sphereFundamentalH2Class := by
    change sphereCoordinate = lastCoefficient • sphereFundamentalHomologyClass
    apply sphereH2EquivQ.injective
    rw [map_smul, sphereH2EquivQ_fundamental]
    change sphereH2EquivQ sphereCoordinate = sphereH2EquivQ sphereCoordinate * 1
    rw [mul_one]
  refine ⟨spherePowerSuccessorCoefficients (extra + 2)
    (oldCoefficients, lastCoefficient), ?_⟩
  rw [spherePowerSuccessorHomologyMap_assembly, oldCoefficients_eq,
    ← sphereClass_eq]
  exact decomposition.symm

/-- [proved-derived; formal-checked] Genuine singular `H₂` transports across the exact ordered
pair/two-address homeomorphism. -/
def sphereProductPowerTwoHomologyIso :
    RationalSingularHomology 2 sphereProductTopCat ≅ SpherePowerH2 2 :=
  (((AlgebraicTopology.singularHomologyFunctor (ModuleCat ℚ) 2).obj
    rationalCoefficient).mapIso sphereProductPowerTwoTopIso)

def sphereProductPowerTwoHomologyEquiv :
    RationalSingularHomology 2 sphereProductTopCat ≃ₗ[ℚ] SpherePowerH2 2 :=
  sphereProductPowerTwoHomologyIso.toLinearEquiv

/-- [proved-derived; formal-checked] The first geometric ruling becomes coordinate zero under the
ordered-pair chart. -/
theorem firstRuling_then_powerTwoTopMap :
    firstRulingTopMap ≫ sphereProductPowerTwoTopIso.hom =
      coordinateRulingTopMap (0 : Fin 2) := by
  apply ConcreteCategory.hom_ext
  intro point
  funext coordinate
  change sphereProductPowerTwoHomeomorph (point, sphereBasepoint) coordinate =
    (if coordinate = (0 : Fin 2) then point else sphereBasepoint)
  fin_cases coordinate <;> rfl

/-- [proved-derived; formal-checked] The second geometric ruling becomes coordinate one under the
same chart. -/
theorem secondRuling_then_powerTwoTopMap :
    secondRulingTopMap ≫ sphereProductPowerTwoTopIso.hom =
      coordinateRulingTopMap (1 : Fin 2) := by
  apply ConcreteCategory.hom_ext
  intro point
  funext coordinate
  change sphereProductPowerTwoHomeomorph (sphereBasepoint, point) coordinate =
    (if coordinate = (1 : Fin 2) then point else sphereBasepoint)
  fin_cases coordinate <;> rfl

def sphereProductPowerTwoChainMap :=
  ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℚ)).obj
    rationalCoefficient).map sphereProductPowerTwoTopIso.hom

theorem firstRulingChainMap_then_powerTwo :
    firstRulingChainMap ≫ sphereProductPowerTwoChainMap =
      coordinateRulingChainMap (0 : Fin 2) := by
  change
    ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℚ)).obj
        rationalCoefficient).map firstRulingTopMap ≫
      ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℚ)).obj
        rationalCoefficient).map sphereProductPowerTwoTopIso.hom = _
  rw [← Functor.map_comp, firstRuling_then_powerTwoTopMap]
  rfl

theorem secondRulingChainMap_then_powerTwo :
    secondRulingChainMap ≫ sphereProductPowerTwoChainMap =
      coordinateRulingChainMap (1 : Fin 2) := by
  change
    ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℚ)).obj
        rationalCoefficient).map secondRulingTopMap ≫
      ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℚ)).obj
        rationalCoefficient).map sphereProductPowerTwoTopIso.hom = _
  rw [← Functor.map_comp, secondRuling_then_powerTwoTopMap]
  rfl

theorem firstRulingCycle_powerTwo :
    (sphereProductPowerTwoChainMap.f 2) firstRulingCycle =
      coordinateRulingCycle (0 : Fin 2) := by
  change (firstRulingChainMap ≫ sphereProductPowerTwoChainMap).f 2
      sphereFundamentalCandidate = _
  rw [firstRulingChainMap_then_powerTwo]
  rfl

theorem secondRulingCycle_powerTwo :
    (sphereProductPowerTwoChainMap.f 2) secondRulingCycle =
      coordinateRulingCycle (1 : Fin 2) := by
  change (secondRulingChainMap ≫ sphereProductPowerTwoChainMap).f 2
      sphereFundamentalCandidate = _
  rw [secondRulingChainMap_then_powerTwo]
  rfl

theorem firstRuling_cyclesMap_powerTwo :
    cycleLift firstRulingCycle firstRulingCycle_boundary_zero ≫
        HomologicalComplex.cyclesMap sphereProductPowerTwoChainMap 2 =
      powerCycleLift (coordinateRulingCycle (0 : Fin 2))
        (coordinateRulingCycle_boundary_zero (0 : Fin 2)) := by
  apply (cancel_mono ((SpherePowerChains 2).iCycles 2)).1
  rw [Category.assoc, HomologicalComplex.cyclesMap_i]
  rw [← Category.assoc, cycleLift_i, powerCycleLift_i]
  ext
  change sphereProductPowerTwoChainMap.f 2 ((1 : ℚ) • firstRulingCycle) =
    (1 : ℚ) • coordinateRulingCycle (0 : Fin 2)
  simpa using firstRulingCycle_powerTwo

theorem secondRuling_cyclesMap_powerTwo :
    cycleLift secondRulingCycle secondRulingCycle_boundary_zero ≫
        HomologicalComplex.cyclesMap sphereProductPowerTwoChainMap 2 =
      powerCycleLift (coordinateRulingCycle (1 : Fin 2))
        (coordinateRulingCycle_boundary_zero (1 : Fin 2)) := by
  apply (cancel_mono ((SpherePowerChains 2).iCycles 2)).1
  rw [Category.assoc, HomologicalComplex.cyclesMap_i]
  rw [← Category.assoc, cycleLift_i, powerCycleLift_i]
  ext
  change sphereProductPowerTwoChainMap.f 2 ((1 : ℚ) • secondRulingCycle) =
    (1 : ℚ) • coordinateRulingCycle (1 : Fin 2)
  simpa using secondRulingCycle_powerTwo

theorem sphereProductPowerTwoHomologyEquiv_firstRuling :
    sphereProductPowerTwoHomologyEquiv firstRulingHomologyClass =
      coordinateRulingHomologyClass (0 : Fin 2) := by
  have hraw :
      (cycleLift firstRulingCycle firstRulingCycle_boundary_zero ≫
          ProductChains.homologyπ 2) ≫
        HomologicalComplex.homologyMap sphereProductPowerTwoChainMap 2 =
      coordinateRulingHomologyMorphism (0 : Fin 2) := by
    rw [Category.assoc, HomologicalComplex.homologyπ_naturality]
    rw [← Category.assoc, firstRuling_cyclesMap_powerTwo]
    rfl
  change
    ((cycleLift firstRulingCycle firstRulingCycle_boundary_zero ≫
        ProductChains.homologyπ 2) ≫
      HomologicalComplex.homologyMap sphereProductPowerTwoChainMap 2) 1 = _
  rw [hraw]
  rfl

theorem sphereProductPowerTwoHomologyEquiv_secondRuling :
    sphereProductPowerTwoHomologyEquiv secondRulingHomologyClass =
      coordinateRulingHomologyClass (1 : Fin 2) := by
  have hraw :
      (cycleLift secondRulingCycle secondRulingCycle_boundary_zero ≫
          ProductChains.homologyπ 2) ≫
        HomologicalComplex.homologyMap sphereProductPowerTwoChainMap 2 =
      coordinateRulingHomologyMorphism (1 : Fin 2) := by
    rw [Category.assoc, HomologicalComplex.homologyπ_naturality]
    rw [← Category.assoc, secondRuling_cyclesMap_powerTwo]
    rfl
  change
    ((cycleLift secondRulingCycle secondRulingCycle_boundary_zero ≫
        ProductChains.homologyπ 2) ≫
      HomologicalComplex.homologyMap sphereProductPowerTwoChainMap 2) 1 = _
  rw [hraw]
  rfl

/-- [proved-derived; formal-checked] The old two-ruling map and the finite-power coordinate map are
the same passage after exact topological transport. -/
theorem sphereProductPowerTwoHomologyEquiv_rulingHomologyMap
    (coefficients : Fin 2 → ℚ) :
    sphereProductPowerTwoHomologyEquiv (rulingHomologyMap coefficients) =
      spherePowerRulingHomologyMap 2 coefficients := by
  rw [show rulingHomologyMap coefficients =
      coefficients 0 • firstRulingHomologyClass +
        coefficients 1 • secondRulingHomologyClass by rfl]
  rw [map_add, map_smul, map_smul,
    sphereProductPowerTwoHomologyEquiv_firstRuling,
    sphereProductPowerTwoHomologyEquiv_secondRuling]
  change _ = ∑ index, coefficients index • coordinateRulingHomologyClass index
  rw [Fin.sum_univ_two]

/-- [proved-derived; formal-checked] The finite-power ruling map is onto at two factors, by exact
transport of the already completed source-level product decomposition. -/
theorem spherePowerRulingHomologyMap_surjective_two :
    Function.Surjective (spherePowerRulingHomologyMap 2) := by
  intro received
  obtain ⟨productClass, productClass_eq⟩ :=
    sphereProductPowerTwoHomologyEquiv.surjective received
  obtain ⟨coefficients, coefficients_eq⟩ := rulingHomologyMap_surjective productClass
  refine ⟨coefficients, ?_⟩
  rw [← sphereProductPowerTwoHomologyEquiv_rulingHomologyMap,
    coefficients_eq, productClass_eq]

/-- [proved-derived; formal-checked] Every finite sphere power from two factors onward is
generated by its addressed coordinate rulings.  The induction step is the exact source-level
successor reconstruction above, rather than a dimension recurrence. -/
theorem spherePowerRulingHomologyMap_surjective_from_two (extra : ℕ) :
    Function.Surjective (spherePowerRulingHomologyMap (extra + 2)) := by
  induction extra with
  | zero => simpa using spherePowerRulingHomologyMap_surjective_two
  | succ preceding inductionHypothesis =>
      simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using
        spherePowerRulingHomologyMap_surjective_successor preceding
          inductionHypothesis

/-- [proved-derived; formal-checked] Uniform finite-power surjectivity: for every positive number
of sphere factors, every genuine rational singular degree-two homology class has an exact finite
coordinate-ruling reconstruction. -/
theorem spherePowerRulingHomologyMap_surjective (factorCount : ℕ)
    (positive : 0 < factorCount) :
    Function.Surjective (spherePowerRulingHomologyMap factorCount) := by
  cases factorCount with
  | zero => omega
  | succ preceding =>
      cases preceding with
      | zero => simpa using spherePowerRulingHomologyMap_surjective_one
      | succ extra =>
          simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using
            spherePowerRulingHomologyMap_surjective_from_two extra

/-- [proved-derived; formal-checked] Exact addressed ruling coordinates on the genuine rational
singular degree-two homology of every positive finite sphere power.  Injectivity is read by the
coordinate receivers; surjectivity retains the recursive source boundary and reconstruction
witnesses used above. -/
def spherePowerRulingHomologyEquiv (factorCount : ℕ) (positive : 0 < factorCount) :
    (Fin factorCount → ℚ) ≃ₗ[ℚ] SpherePowerH2 factorCount :=
  LinearEquiv.ofBijective (spherePowerRulingHomologyMap factorCount)
    ⟨spherePowerRulingHomologyMap_injective factorCount,
      spherePowerRulingHomologyMap_surjective factorCount positive⟩

/-- [proved-derived; formal-checked] Exact one-factor coordinates on genuine rational singular
degree-two homology. -/
def spherePowerRulingHomologyEquivOne :
    (Fin 1 → ℚ) ≃ₗ[ℚ] SpherePowerH2 1 :=
  LinearEquiv.ofBijective (spherePowerRulingHomologyMap 1)
    ⟨spherePowerRulingHomologyMap_injective 1,
      spherePowerRulingHomologyMap_surjective_one⟩

/-- [proved-derived; formal-checked] Exact two-factor coordinates on genuine rational singular
degree-two homology, with the source-level boundary witnesses retained by the transported ruling
decomposition. -/
def spherePowerRulingHomologyEquivTwo :
    (Fin 2 → ℚ) ≃ₗ[ℚ] SpherePowerH2 2 :=
  LinearEquiv.ofBijective (spherePowerRulingHomologyMap 2)
    ⟨spherePowerRulingHomologyMap_injective 2,
      spherePowerRulingHomologyMap_surjective_two⟩

section Audit

#print axioms spherePowerCellComplex_d
#print axioms spherePowerCellHomologyIsoModule
#print axioms spherePowerHomologyEquivCellModule
#print axioms spherePowerEvenCellIndexEquiv
#print axioms spherePowerEvenCellIndex_card
#print axioms spherePowerCellModule_finrank_even
#print axioms spherePowerOddCellIndex_isEmpty
#print axioms spherePowerCellModule_finrank_odd
#print axioms spherePowerCellModule_pascal
#print axioms spherePowerSuccessorSimplexRealization
#print axioms spherePowerLowDegreeCurrentDatumFromTwo
#print axioms coordinateRulingCycle_boundary_zero
#print axioms crossed_projection_coordinateRulingCycle
#print axioms coordinateProjection_spherePowerRulingHomologyMap
#print axioms spherePowerRulingHomologyMap_injective
#print axioms spherePowerRulingHomologyMap_surjective_one
#print axioms spherePowerRulingHomologyMap_surjective_two
#print axioms spherePowerPrefixCurrentMap
#print axioms lastCoordinateRulingCurrentMap
#print axioms exists_spherePowerSuccessorChainDecomposition
#print axioms exists_spherePowerSuccessorHomologyDecomposition
#print axioms coordinateRulingCyclesMap_then_spherePowerPrefix
#print axioms spherePowerPrefixHomologyMap_coordinateRuling
#print axioms sphereCycleMap_lastCoordinateRuling
#print axioms lastCoordinateRulingHomologyMap_fundamental
#print axioms spherePowerSuccessorHomologyMap_assembly
#print axioms spherePowerRulingHomologyMap_surjective_successor
#print axioms spherePowerRulingHomologyMap_surjective_from_two
#print axioms spherePowerRulingHomologyMap_surjective
#print axioms spherePowerRulingHomologyEquiv
#print axioms spherePowerRulingHomologyEquivOne
#print axioms spherePowerRulingHomologyEquivTwo

end Audit

end Soma.Holonics.Millennium.HodgeSpherePowerRulingHomology
