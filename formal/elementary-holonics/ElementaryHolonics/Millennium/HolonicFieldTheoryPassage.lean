import ElementaryHolonics.Millennium.HolonicDifferenceCalculus
import ElementaryHolonics.Millennium.HolonicTypedOriginDimensions

/-!
# A finite holonic field-theory passage

**[proved-derived]** This file gives the smallest common carrier needed by the cosmological,
gauge, fluid, and material-field interpretations.  A field configuration produces an addressed
local jet at every event; a local Lagrangian reads that jet; the finite action is the sum over an
admitted region.  Disjoint regions glue exactly, action differences glue exactly, and every
additive receiver preserves the returned action difference.

The second section isolates the scalar focusing receiver of a timelike congruence.  It does not
identify dark matter with contraction or dark energy with expansion.  Instead it proves the exact
common chart: pressureless positive density contributes a focusing term, while a vacuum sector
with `pressure = -density` contributes the same defocusing term as a positive geometric
cosmological constant after the declared Einstein chart relation.

The final section records internal exchange between two field sectors.  Opposite exchange currents
cancel in the glued balance; a nonzero exterior remainder is therefore retained rather than called
"leakage" without a boundary.

The reaction section then separates charge cancellation from action transport.  A
particle--antiparticle pair can return zero total charge while retaining twice the one-particle
energy face.  A closed reaction ledger makes an unseen outgoing carrier the exact remainder of the
visible receiver.  Finally the Boltzmann collision departure is connected to the common finite
Leibniz owner rather than approximated.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HolonicFieldTheoryPassage

open Soma.Holonics.Millennium.HolonicDifferenceCalculus

/-! ## Local fields, action, and exact gluing -/

structure LocalFieldTheory
    (Event Configuration Jet Coefficient : Type*)
    [AddCommGroup Coefficient] where
  localJet : Configuration → Event → Jet
  lagrangian : Event → Jet → Coefficient

def LocalFieldTheory.actionOn
    {Event Configuration Jet Coefficient : Type*}
    [AddCommGroup Coefficient]
    (theory : LocalFieldTheory Event Configuration Jet Coefficient)
    (region : Finset Event) (field : Configuration) : Coefficient :=
  ∑ event ∈ region, theory.lagrangian event (theory.localJet field event)

theorem LocalFieldTheory.actionOn_union
    {Event Configuration Jet Coefficient : Type*}
    [DecidableEq Event] [AddCommGroup Coefficient]
    (theory : LocalFieldTheory Event Configuration Jet Coefficient)
    {left right : Finset Event} (disjoint : Disjoint left right)
    (field : Configuration) :
    theory.actionOn (left ∪ right) field =
      theory.actionOn left field + theory.actionOn right field := by
  unfold actionOn
  rw [Finset.sum_union disjoint]

def LocalFieldTheory.actionDifference
    {Event Configuration Jet Coefficient : Type*}
    [AddCommGroup Coefficient]
    (theory : LocalFieldTheory Event Configuration Jet Coefficient)
    (region : Finset Event) (source receiver : Configuration) : Coefficient :=
  theory.actionOn region receiver - theory.actionOn region source

theorem LocalFieldTheory.actionDifference_union
    {Event Configuration Jet Coefficient : Type*}
    [DecidableEq Event] [AddCommGroup Coefficient]
    (theory : LocalFieldTheory Event Configuration Jet Coefficient)
    {left right : Finset Event} (disjoint : Disjoint left right)
    (source receiver : Configuration) :
    theory.actionDifference (left ∪ right) source receiver =
      theory.actionDifference left source receiver +
        theory.actionDifference right source receiver := by
  simp only [actionDifference, theory.actionOn_union disjoint]
  abel

theorem LocalFieldTheory.receiver_actionDifference
    {Event Configuration Jet Coefficient Reading : Type*}
    [AddCommGroup Coefficient] [AddCommGroup Reading]
    (theory : LocalFieldTheory Event Configuration Jet Coefficient)
    (receiver : Coefficient →+ Reading) (region : Finset Event)
    (source target : Configuration) :
    receiver (theory.actionDifference region source target) =
      receiver (theory.actionOn region target) - receiver (theory.actionOn region source) := by
  simp [actionDifference]

/-! ## Expansion, shear, vorticity, and the focusing receiver -/

/-- The scalar slots in the timelike Raychaudhuri receiver.  A geometric realization must supply
these from a Lorentzian metric, connection, and congruence. -/
structure CongruenceLedger where
  expansion : ℚ
  shearSquare : ℚ
  vorticitySquare : ℚ
  ricciFocusing : ℚ
  accelerationDivergence : ℚ

/-- Four-dimensional timelike Raychaudhuri scalar, in the declared sign convention. -/
def CongruenceLedger.returnedExpansionRate (ledger : CongruenceLedger) : ℚ :=
  -(ledger.expansion ^ 2) / 3 - ledger.shearSquare + ledger.vorticitySquare -
    ledger.ricciFocusing + ledger.accelerationDivergence

structure PerfectFieldSector where
  energyDensity : ℚ
  pressure : ℚ

/-- The perfect-sector combination entering timelike Ricci focusing in four dimensions. -/
def PerfectFieldSector.activeDensity (sector : PerfectFieldSector) : ℚ :=
  sector.energyDensity + 3 * sector.pressure

/-- The sector's contribution to the expansion-rate ledger after the Einstein equation is used.
Negative output is focusing; positive output is defocusing in this convention. -/
def PerfectFieldSector.expansionContribution
    (einsteinCoupling : ℚ) (sector : PerfectFieldSector) : ℚ :=
  -(einsteinCoupling / 2) * sector.activeDensity

def dustSector (density : ℚ) : PerfectFieldSector :=
  ⟨density, 0⟩

def vacuumSector (density : ℚ) : PerfectFieldSector :=
  ⟨density, -density⟩

theorem dust_expansionContribution (einsteinCoupling density : ℚ) :
    (dustSector density).expansionContribution einsteinCoupling =
      -(einsteinCoupling / 2) * density := by
  simp [dustSector, PerfectFieldSector.expansionContribution,
    PerfectFieldSector.activeDensity]

theorem vacuum_expansionContribution (einsteinCoupling density : ℚ) :
    (vacuumSector density).expansionContribution einsteinCoupling =
      einsteinCoupling * density := by
  simp [vacuumSector, PerfectFieldSector.expansionContribution,
    PerfectFieldSector.activeDensity]
  ring

/-- Moving a vacuum field from the stress--energy chart to the geometric cosmological-constant
chart preserves its exact contribution to the expansion receiver. -/
theorem vacuumMatterChart_eq_geometricLambda
    (einsteinCoupling density cosmologicalConstant : ℚ)
    (chart : cosmologicalConstant = einsteinCoupling * density) :
    (vacuumSector density).expansionContribution einsteinCoupling =
      cosmologicalConstant := by
  rw [vacuum_expansionContribution, chart]

/-! ## Internal exchange is not an untyped exterior leak -/

/-- `densityDifference + expansionWork = admittedExchange` for one finite field-sector passage. -/
def SatisfiesSectorBalance
    (densityDifference expansionWork admittedExchange : ℚ) : Prop :=
  densityDifference + expansionWork = admittedExchange

theorem oppositeExchange_glues_to_total_conservation
    (matterDifference matterExpansion darkDifference darkExpansion exchange : ℚ)
    (matterBalance :
      SatisfiesSectorBalance matterDifference matterExpansion exchange)
    (darkBalance :
      SatisfiesSectorBalance darkDifference darkExpansion (-exchange)) :
    (matterDifference + darkDifference) +
        (matterExpansion + darkExpansion) = 0 := by
  unfold SatisfiesSectorBalance at matterBalance darkBalance
  linear_combination matterBalance + darkBalance

/-! ## Reaction receivers: null charge is not null transported action -/

/-- Two separately typed additive readings of one reaction occurrence.  The pair is only a finite
receiver chart; a physical realization must supply a four-momentum and charge representation. -/
structure ChargeEnergyReading where
  charge : ℚ
  energy : ℚ
  deriving DecidableEq

@[ext] theorem ChargeEnergyReading.ext
    {left right : ChargeEnergyReading}
    (charge_eq : left.charge = right.charge)
    (energy_eq : left.energy = right.energy) : left = right := by
  cases left
  cases right
  simp_all

def addChargeEnergyReading
    (left right : ChargeEnergyReading) : ChargeEnergyReading :=
  ⟨left.charge + right.charge, left.energy + right.energy⟩

def conjugateReading (charge energy : ℚ) : ChargeEnergyReading :=
  ⟨-charge, energy⟩

def matterReading (charge energy : ℚ) : ChargeEnergyReading :=
  ⟨charge, energy⟩

/-- Conjugate charge orientations cancel exactly, while their positive-or-negative energy
coordinates add.  No order assumption is needed for the separation itself. -/
theorem matter_conjugate_sum (charge energy : ℚ) :
    addChargeEnergyReading (matterReading charge energy) (conjugateReading charge energy) =
      ⟨0, 2 * energy⟩ := by
  apply ChargeEnergyReading.ext
  · simp [matterReading, conjugateReading, addChargeEnergyReading]
  · simp [matterReading, conjugateReading, addChargeEnergyReading, two_mul]

/-- The charge receiver of the conjugate pair is null. -/
theorem matter_conjugate_charge_is_zero (charge energy : ℚ) :
    (addChargeEnergyReading (matterReading charge energy)
      (conjugateReading charge energy)).charge = 0 := by
  simp [matterReading, conjugateReading, addChargeEnergyReading]

/-- Unless the admitted energy face itself is null, charge cancellation does not imply energy
cancellation. -/
theorem matter_conjugate_energy_is_nonzero
    (charge energy : ℚ) (energy_ne : energy ≠ 0) :
    (addChargeEnergyReading (matterReading charge energy)
      (conjugateReading charge energy)).energy ≠ 0 := by
  rw [matter_conjugate_sum]
  exact mul_ne_zero (by norm_num) energy_ne

/-- An exact finite reaction ledger in energy coordinates.  The separate outgoing faces retain
binding/rest conversion, kinetic motion, radiation, recoil, and a weakly observed carrier. -/
structure ReactionEnergyLedger where
  incomingRestEnergy : ℚ
  outgoingRestEnergy : ℚ
  outgoingKinetic : ℚ
  outgoingRadiation : ℚ
  outgoingRecoil : ℚ
  outgoingWeakCarrier : ℚ

def ReactionEnergyLedger.visibleOutgoing (ledger : ReactionEnergyLedger) : ℚ :=
  ledger.outgoingRestEnergy + ledger.outgoingKinetic + ledger.outgoingRadiation +
    ledger.outgoingRecoil

def ReactionEnergyLedger.isClosed (ledger : ReactionEnergyLedger) : Prop :=
  ledger.incomingRestEnergy = ledger.visibleOutgoing + ledger.outgoingWeakCarrier

/-- What a visible receiver calls missing energy is exactly the unobserved outgoing carrier when
the complete reaction ledger closes. -/
theorem ReactionEnergyLedger.visibleDefect_eq_weakCarrier
    (ledger : ReactionEnergyLedger) (closed : ledger.isClosed) :
    ledger.incomingRestEnergy - ledger.visibleOutgoing = ledger.outgoingWeakCarrier := by
  unfold ReactionEnergyLedger.isClosed at closed
  linarith

/-! ## Relic populations: collision, dilution, source, and retained remainder -/

/-- The exact pair-collision departure from an equilibrium population. -/
def pairCollisionDeparture (population equilibrium : ℚ) : ℚ :=
  population ^ 2 - equilibrium ^ 2

/-- The collision departure is the oriented population difference multiplied by the admitted
population sum.  This is the same finite Leibniz face used by nonlinear cosmological inference. -/
theorem pairCollisionDeparture_factor (population equilibrium : ℚ) :
    pairCollisionDeparture population equilibrium =
      (population - equilibrium) * (population + equilibrium) := by
  exact squareDifference_isDifferenceTimesSum equilibrium population

/-- One finite chronology cell of a relic-population balance.  Expansion/dilution, collisions, and
production remain separate current faces rather than being collapsed into a scalar abundance. -/
structure RelicPopulationCell where
  populationDifference : ℚ
  expansionDilution : ℚ
  collisionRemoval : ℚ
  admittedProduction : ℚ

def RelicPopulationCell.isBalanced (cell : RelicPopulationCell) : Prop :=
  cell.populationDifference + cell.expansionDilution + cell.collisionRemoval =
    cell.admittedProduction

/-- The retained population change is reconstructed exactly from production less the two declared
outgoing faces. -/
theorem RelicPopulationCell.reconstructDifference
    (cell : RelicPopulationCell) (balanced : cell.isBalanced) :
    cell.populationDifference =
      cell.admittedProduction - cell.expansionDilution - cell.collisionRemoval := by
  unfold RelicPopulationCell.isBalanced at balanced
  linarith

end Soma.Holonics.Millennium.HolonicFieldTheoryPassage

section Audit
open Soma.Holonics.Millennium.HolonicFieldTheoryPassage
#print axioms LocalFieldTheory.actionOn_union
#print axioms LocalFieldTheory.actionDifference_union
#print axioms LocalFieldTheory.receiver_actionDifference
#print axioms dust_expansionContribution
#print axioms vacuum_expansionContribution
#print axioms vacuumMatterChart_eq_geometricLambda
#print axioms oppositeExchange_glues_to_total_conservation
#print axioms matter_conjugate_sum
#print axioms matter_conjugate_energy_is_nonzero
#print axioms ReactionEnergyLedger.visibleDefect_eq_weakCarrier
#print axioms pairCollisionDeparture_factor
#print axioms RelicPopulationCell.reconstructDifference
end Audit
