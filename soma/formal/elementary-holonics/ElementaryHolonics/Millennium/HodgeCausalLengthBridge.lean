import ElementaryHolonics.Millennium.HolonStagedCausalLength
import ElementaryHolonics.Millennium.HodgeHolonicCutFalsifier

/-!
# The Hodge cycle-class swing as a measured causal passage

[definition] This file applies the receiver-indexed causal-length tower to an existing
source-bearing Hodge object rather than inventing a Hodge-shaped tower.  A rational algebraic cycle
is the retained source occurrence, its rational Hodge class is the returned target, and the enacted
cycle-class swing has one local clock tick.  Codimension is retained separately as the boundary
degree coordinate.

[proved-derived; formal-checked] The tower receiver fibre over `some hodgeClass` is exactly
`CycleLiftFibre D hodgeClass`.  The same construction measures the sharper primitive-detection
holon and proves that occupation of every nonzero tower fibre is equivalent to the already stated
`PrimitiveLiftable` obligation.

[counterexample; formal-checked] The existing missing-axis model remains empty after the clock is
attached.  Equal or finite length data therefore cannot manufacture the absent algebraic source.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgeCausalLengthBridge

open Soma.Holonics
open Soma.Holonics.Millennium.HodgeConjecture
open Soma.Holonics.Millennium.HodgeConstructivePassage
open Soma.Holonics.Millennium.HodgeHolonicPrimitiveCut
open Soma.Holonics.Millennium.HolonStagedCausalLength
open Soma.Holonics.Millennium.ReceiverIndexedCausalLengthTower

/-! ## The cycle-class swing -/

/-- [definition] Codimension is a boundary degree coordinate on both stages.  It is not the
one-step passage clock. -/
def cycleClassBoundaryLength (D : Datum) :
    D.CycleSpace ⊕ D.rationalHodgeClasses → ℕ :=
  fun _ => D.codimension

/-- [definition] The exact cycle-class holon with stationary stage histories and a one-tick clock
on each enacted algebraic-cycle occurrence. -/
def cycleClassTower (D : Datum) :=
  oneStepTower (cycleClassHolon D) (cycleClassBoundaryLength D)

/-- [definition] One actual rational algebraic cycle enacted as a tower history. -/
def cycleClassHistory (D : Datum) (cycle : D.CycleSpace) :
    StagedHistory (cycleClassHolon D) :=
  StagedHistory.enact cycle

/-- [proved-derived; formal-checked] The enacted cycle begins at the retained algebraic-cycle
source port. -/
@[simp] theorem cycleClassHistory_source (D : Datum) (cycle : D.CycleSpace) :
    (cycleClassTower D).history.source (cycleClassHistory D cycle) = Sum.inl cycle := rfl

/-- [proved-derived; formal-checked] The enacted cycle ends at its actual rational Hodge class. -/
@[simp] theorem cycleClassHistory_target (D : Datum) (cycle : D.CycleSpace) :
    (cycleClassTower D).history.target (cycleClassHistory D cycle) =
      Sum.inr ⟨D.cycleClass.hom cycle, D.cycleClassesAreHodge ⟨cycle, rfl⟩⟩ := rfl

/-- [proved-derived; formal-checked] The enacted cycle-class swing has one causal clock tick. -/
@[simp] theorem cycleClassHistory_clockLength (D : Datum) (cycle : D.CycleSpace) :
    (cycleClassTower D).clockLength (cycleClassHistory D cycle) = 1 := by
  exact enacted_clockLength (cycleClassHolon D) (cycleClassBoundaryLength D) cycle

/-- [proved-derived; formal-checked] Boundary degree remains codimension on every staged state,
independently of the one-step passage clock. -/
@[simp] theorem cycleClassBoundaryLength_exact (D : Datum)
    (state : D.CycleSpace ⊕ D.rationalHodgeClasses) :
    (cycleClassTower D).boundaryLength state = D.codimension := rfl

/-- [proved-derived; formal-checked] The measured tower retains exactly the complete population of
algebraic-cycle lifts behind one rational Hodge receiver face. -/
def cycleClassTowerPreimageFibreEquiv (D : Datum)
    (hodgeClass : D.rationalHodgeClasses) :
    (cycleClassTower D).history.toHolon.PreimageFibre (some hodgeClass) ≃
      CycleLiftFibre D hodgeClass :=
  (enactedPreimageFibreEquiv (cycleClassHolon D)
    (cycleClassBoundaryLength D) hodgeClass).trans
      (cycleClassHolonPreimageFibreEquiv D hodgeClass)

/-! ## The primitive detector swing -/

/-- [definition] The codimension of the upper Hodge datum remains the boundary coordinate for the
primitive detector. -/
def primitiveDetectionBoundaryLength {lower upper : Datum}
    {step : PrimitiveHodgeStep lower upper}
    (_polarization : SignedDefinitePrimitivePolarization step) :
    upper.CycleSpace ⊕ step.Primitive → ℕ :=
  fun _ => upper.codimension

/-- [definition] The already source-bearing primitive detector equipped with an elementary clock.
This creates no detector occurrences; it measures exactly those already present. -/
def primitiveDetectionTower {lower upper : Datum}
    {step : PrimitiveHodgeStep lower upper}
    (polarization : SignedDefinitePrimitivePolarization step) :=
  oneStepTower (primitiveDetectionHolon polarization)
    (primitiveDetectionBoundaryLength polarization)

/-- [proved-derived; formal-checked] Every measured primitive receiver fibre is exactly its
original source-bearing detector fibre. -/
def primitiveDetectionTowerPreimageFibreEquiv {lower upper : Datum}
    {step : PrimitiveHodgeStep lower upper}
    (polarization : SignedDefinitePrimitivePolarization step)
    (primitive : step.Primitive) :
    (primitiveDetectionTower polarization).history.toHolon.PreimageFibre (some primitive) ≃
      (primitiveDetectionHolon polarization).PreimageFibre primitive :=
  enactedPreimageFibreEquiv (primitiveDetectionHolon polarization)
    (primitiveDetectionBoundaryLength polarization) primitive

/-- [proved-derived; formal-checked] The conjectural detector law is unchanged by measuring its
actual occurrences.  Clock attachment is conservative over source-fibre occupation. -/
theorem detectsEveryNonzero_iff_towerFibreOccupied {lower upper : Datum}
    {step : PrimitiveHodgeStep lower upper}
    (polarization : SignedDefinitePrimitivePolarization step) :
    DetectsEveryNonzero polarization ↔
      ∀ primitive : step.Primitive, primitive ≠ 0 →
        Nonempty
          ((primitiveDetectionTower polarization).history.toHolon.PreimageFibre
            (some primitive)) := by
  constructor
  · intro detects primitive hprimitive
    exact Nonempty.map
      (primitiveDetectionTowerPreimageFibreEquiv polarization primitive).symm
      (detects primitive hprimitive)
  · intro occupied primitive hprimitive
    exact Nonempty.map
      (primitiveDetectionTowerPreimageFibreEquiv polarization primitive)
      (occupied primitive hprimitive)

/-- [proved-derived; formal-checked] Under signed Hodge--Riemann definiteness, complete occupation
of the measured primitive swing is exactly the existing primitive algebraicity obligation. -/
theorem towerFibreOccupation_iff_primitiveLiftable {lower upper : Datum}
    {step : PrimitiveHodgeStep lower upper}
    (polarization : SignedDefinitePrimitivePolarization step) :
    (∀ primitive : step.Primitive, primitive ≠ 0 →
      Nonempty
        ((primitiveDetectionTower polarization).history.toHolon.PreimageFibre
          (some primitive))) ↔ step.PrimitiveLiftable :=
  (detectsEveryNonzero_iff_towerFibreOccupied polarization).symm.trans
    polarization.detectsEveryNonzero_iff_primitiveLiftable

/-! ## Firing falsifier -/

open Soma.Holonics.Millennium.HodgeHolonicCutFalsifier

/-- [counterexample; formal-checked] The clocked tower still has no enacted history returning the
missing Hodge class.  Signed polarization and a finite one-tick scale do not create an algebraic
cycle source. -/
theorem missingCycleClassTowerFibre_empty :
    ¬ Nonempty
      ((cycleClassTower upperDatum).history.toHolon.PreimageFibre
        (some missingHodgeClass)) := by
  exact enactedFibre_empty_of_sourceFibre_empty
    (cycleClassHolon upperDatum) (cycleClassBoundaryLength upperDatum) missingHodgeClass
      missingHolonFibre_empty

section Audit

#print axioms cycleClassHistory_source
#print axioms cycleClassHistory_target
#print axioms cycleClassHistory_clockLength
#print axioms cycleClassBoundaryLength_exact
#print axioms cycleClassTowerPreimageFibreEquiv
#print axioms primitiveDetectionTowerPreimageFibreEquiv
#print axioms detectsEveryNonzero_iff_towerFibreOccupied
#print axioms towerFibreOccupation_iff_primitiveLiftable
#print axioms missingCycleClassTowerFibre_empty

end Audit

end Soma.Holonics.Millennium.HodgeCausalLengthBridge
