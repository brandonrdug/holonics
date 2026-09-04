import ElementaryHolonics.Millennium.HolonicDifferenceCalculus
import ElementaryHolonics.Millennium.HolonicRankFourInteractionPlanes

/-!
# Exact Maxwell propagation on the six-plane carrier

**[proved-derived]** A chosen `3 + 1` receiver splits the six interaction planes of the rank-four
period carrier into three electric and three magnetic coordinates.  Discrete Faraday and
Ampere--Maxwell passages then compose exactly: the second returned time difference of either field
is the corresponding curl--curl return multiplied by

`cSquared = (permeability * permittivity)⁻¹`.

For positive constitutive coefficients, the propagation receiver
`c = sqrt ((permeability * permittivity)⁻¹)` is positive and has exactly that square.  No
rounding, plane-wave ansatz, perfectly circular coil, or continuum limit occurs in the proof.  The
continuum vector wave equation follows after a later primal/dual Hodge owner identifies the signed
curl--curl composition with the appropriate Laplacian on the source-free fibre.

The final theorems retain the full relativistic rest-energy factor:
`(m * c^2)^2 = m^2 * c^4`.  The constitutive Maxwell passage therefore supplies the exact `c^2`
receiver used by the mass-shell expression rather than discarding it as notation.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HolonicMaxwellPropagation

open Soma.Holonics.Millennium.HolonicRankFourInteractionPlanes
open Soma.Holonics.Millennium.HolonicDifferenceCalculus
open Soma.Holonics.Millennium.HolonicDiscreteInduction
open Soma.Holonics.Geometry.SixSphereMonodromy
open Soma.Holonics.Geometry.SixSpherePeriods
open Soma.Holonics.Geometry.SixSphereTorusFibre

/-! ## External successor as one addressed internal `δ̂` transport -/

/-- The lattice-grade chronology based at `origin`: one exterior successor occurrence transports
the rank-four carrier by one addressed `δ̂` period cycle.  Reversing the chosen orientation would
replace the step by its additive inverse; no absolute past/future label enters the construction. -/
def deltaChronology (origin : Lattice) : ℕ → Lattice :=
  affinePath origin (periodBasisCycle deltaDirection)

/-- One returned chronological difference is exactly one internal `δ̂` cycle, at every occurrence. -/
theorem firstDifference_deltaChronology (origin : Lattice) (time : ℕ) :
    firstDifference (deltaChronology origin) time = periodBasisCycle deltaDirection := by
  exact firstDifference_affinePath origin (periodBasisCycle deltaDirection) time

/-- The corresponding universal-cover displacement is exactly the fourth period column `(0,1)`.
This closes the lattice chronology seam; identifying a field evolution generator with this
translation still requires its own naturality square. -/
theorem periodDisplacement_firstDifference_deltaChronology
    (point : PeriodPoint) (origin : Lattice) (time : ℕ) :
    periodColumnVector point (firstDifference (deltaChronology origin) time) = ![0, 1] := by
  rw [firstDifference_deltaChronology]
  exact deltaPeriodVector point

/-! ## The six face coordinates as electric plus magnetic triples -/

abbrev SpatialSection := Fin 3 → ℝ
abbrev SixPlaneSection := InteractionPlane → ℝ

/-- The oriented `3 + 3` receiver.  The magnetic signs are the standard complementary-plane
orientation for the ordered spatial basis `(γ̂,û,ŵ)`: `F₁₂ = B₃`, `F₁₃ = -B₂`,
and `F₂₃ = B₁`. -/
def fieldStrengthThreePlusThreeEquiv :
    SixPlaneSection ≃ₗ[ℝ] (SpatialSection × SpatialSection) where
  toFun field :=
    (![field .gamma_delta, field .u_delta, field .w_delta],
      ![field .u_w, -field .gamma_w, field .gamma_u])
  invFun field := fun plane ↦
    match plane with
    | .gamma_u => field.2 2
    | .gamma_w => -field.2 1
    | .gamma_delta => field.1 0
    | .u_w => field.2 0
    | .u_delta => field.1 1
    | .w_delta => field.1 2
  left_inv field := by
    funext plane
    cases plane <;> simp
  right_inv field := by
    rcases field with ⟨electric, magnetic⟩
    apply Prod.ext
    · funext direction
      fin_cases direction <;> rfl
    · funext direction
      fin_cases direction <;> simp
  map_add' left right := by
    apply Prod.ext
    · funext direction
      fin_cases direction <;> rfl
    · funext direction
      fin_cases direction <;> simp [add_comm]
  map_smul' scalar field := by
    apply Prod.ext
    · funext direction
      fin_cases direction <;> rfl
    · funext direction
      fin_cases direction <;> simp

theorem fieldStrengthThreePlusThreeEquiv_isBijective :
    Function.Bijective fieldStrengthThreePlusThreeEquiv :=
  fieldStrengthThreePlusThreeEquiv.bijective

/-! ## The paired primal/dual Maxwell passage -/

universe v w

variable {Electric : Type v} {Magnetic : Type w}
variable [AddCommGroup Electric] [Module ℝ Electric]
variable [AddCommGroup Magnetic] [Module ℝ Magnetic]

/-- A finite vacuum Maxwell passage.  The two curls are kept typed because electric and magnetic
cochains occupy opposite sides of the primal/dual complex.  Positivity makes both constitutive
maps invertible at this receiver. -/
structure VacuumMaxwellPassage where
  permeability : ℝ
  permittivity : ℝ
  permeability_pos : 0 < permeability
  permittivity_pos : 0 < permittivity
  electricCurl : Electric →ₗ[ℝ] Magnetic
  magneticCurl : Magnetic →ₗ[ℝ] Electric
  electric : ℕ → Electric
  magnetic : ℕ → Magnetic
  faraday : ∀ time,
    firstDifference magnetic time = -electricCurl (electric time)
  ampereMaxwell : ∀ time,
    permittivity • firstDifference electric time =
      permeability⁻¹ • magneticCurl (magnetic time)

namespace VacuumMaxwellPassage

/-- The squared propagation conversion returned by the two constitutive faces. -/
def propagationSpeedSquared (passage : VacuumMaxwellPassage (Electric := Electric)
    (Magnetic := Magnetic)) : ℝ :=
  (passage.permeability * passage.permittivity)⁻¹

/-- The positive propagation-speed receiver. -/
def propagationSpeed (passage : VacuumMaxwellPassage (Electric := Electric)
    (Magnetic := Magnetic)) : ℝ :=
  Real.sqrt passage.propagationSpeedSquared

theorem propagationSpeedSquared_pos
    (passage : VacuumMaxwellPassage (Electric := Electric) (Magnetic := Magnetic)) :
    0 < passage.propagationSpeedSquared := by
  exact inv_pos.mpr (mul_pos passage.permeability_pos passage.permittivity_pos)

theorem propagationSpeed_pos
    (passage : VacuumMaxwellPassage (Electric := Electric) (Magnetic := Magnetic)) :
    0 < passage.propagationSpeed := by
  exact Real.sqrt_pos.2 passage.propagationSpeedSquared_pos

/-- `c^2 = (με)⁻¹` exactly. -/
theorem propagationSpeed_sq
    (passage : VacuumMaxwellPassage (Electric := Electric) (Magnetic := Magnetic)) :
    passage.propagationSpeed ^ 2 = passage.propagationSpeedSquared := by
  exact Real.sq_sqrt (le_of_lt passage.propagationSpeedSquared_pos)

theorem propagationSpeedSquared_mul_constitutive
    (passage : VacuumMaxwellPassage (Electric := Electric) (Magnetic := Magnetic)) :
    passage.propagationSpeedSquared *
        (passage.permeability * passage.permittivity) = 1 := by
  exact inv_mul_cancel₀
    (mul_ne_zero (ne_of_gt passage.permeability_pos)
      (ne_of_gt passage.permittivity_pos))

/-- Ampere--Maxwell solved for one electric temporal return. -/
theorem electric_firstDifference
    (passage : VacuumMaxwellPassage (Electric := Electric) (Magnetic := Magnetic))
    (time : ℕ) :
    firstDifference passage.electric time =
      passage.propagationSpeedSquared •
        passage.magneticCurl (passage.magnetic time) := by
  calc
    firstDifference passage.electric time =
        passage.permittivity⁻¹ •
          (passage.permittivity • firstDifference passage.electric time) := by
      simp [smul_smul, ne_of_gt passage.permittivity_pos]
    _ = passage.permittivity⁻¹ •
        (passage.permeability⁻¹ •
          passage.magneticCurl (passage.magnetic time)) := by
      rw [passage.ampereMaxwell time]
    _ = passage.propagationSpeedSquared •
        passage.magneticCurl (passage.magnetic time) := by
      rw [smul_smul]
      congr 1
      simp [propagationSpeedSquared]

/-- Faraday followed by Ampere--Maxwell gives the electric curl--curl wave return. -/
theorem electric_secondDifference
    (passage : VacuumMaxwellPassage (Electric := Electric) (Magnetic := Magnetic))
    (time : ℕ) :
    secondDifference passage.electric time =
      (-passage.propagationSpeedSquared) •
        passage.magneticCurl (passage.electricCurl (passage.electric time)) := by
  have hscaled :
      passage.permittivity • secondDifference passage.electric time =
        (-passage.permeability⁻¹) •
          passage.magneticCurl (passage.electricCurl (passage.electric time)) := by
    calc
      passage.permittivity • secondDifference passage.electric time =
          passage.permittivity • firstDifference passage.electric (time + 1) -
            passage.permittivity • firstDifference passage.electric time := by
        rw [secondDifference, smul_sub]
      _ = passage.permeability⁻¹ • passage.magneticCurl (passage.magnetic (time + 1)) -
          passage.permeability⁻¹ • passage.magneticCurl (passage.magnetic time) := by
        rw [passage.ampereMaxwell (time + 1), passage.ampereMaxwell time]
      _ = passage.permeability⁻¹ •
          (passage.magneticCurl (passage.magnetic (time + 1)) -
            passage.magneticCurl (passage.magnetic time)) := by
        rw [smul_sub]
      _ = passage.permeability⁻¹ •
          passage.magneticCurl
            (firstDifference passage.magnetic time) := by
        rw [← passage.magneticCurl.map_sub]
        rfl
      _ = passage.permeability⁻¹ •
          passage.magneticCurl (-passage.electricCurl (passage.electric time)) := by
        rw [passage.faraday time]
      _ = (-passage.permeability⁻¹) •
          passage.magneticCurl (passage.electricCurl (passage.electric time)) := by
        simp
  calc
    secondDifference passage.electric time =
        passage.permittivity⁻¹ •
          (passage.permittivity • secondDifference passage.electric time) := by
      simp [smul_smul, ne_of_gt passage.permittivity_pos]
    _ = passage.permittivity⁻¹ •
        ((-passage.permeability⁻¹) •
          passage.magneticCurl (passage.electricCurl (passage.electric time))) := by
      rw [hscaled]
    _ = (-passage.propagationSpeedSquared) •
        passage.magneticCurl (passage.electricCurl (passage.electric time)) := by
      rw [smul_smul]
      congr 1
      simp [propagationSpeedSquared]

/-- Ampere--Maxwell followed by Faraday gives the magnetic curl--curl wave return. -/
theorem magnetic_secondDifference
    (passage : VacuumMaxwellPassage (Electric := Electric) (Magnetic := Magnetic))
    (time : ℕ) :
    secondDifference passage.magnetic time =
      (-passage.propagationSpeedSquared) •
        passage.electricCurl (passage.magneticCurl (passage.magnetic time)) := by
  calc
    secondDifference passage.magnetic time =
        firstDifference passage.magnetic (time + 1) -
          firstDifference passage.magnetic time := rfl
    _ = -passage.electricCurl (passage.electric (time + 1)) -
        (-passage.electricCurl (passage.electric time)) := by
      rw [passage.faraday (time + 1), passage.faraday time]
    _ = -passage.electricCurl
        (firstDifference passage.electric time) := by
      calc
        -passage.electricCurl (passage.electric (time + 1)) -
            (-passage.electricCurl (passage.electric time)) =
            -(passage.electricCurl (passage.electric (time + 1)) -
              passage.electricCurl (passage.electric time)) := by abel
        _ = -passage.electricCurl
            (passage.electric (time + 1) - passage.electric time) := by
          rw [passage.electricCurl.map_sub]
        _ = -passage.electricCurl
            (firstDifference passage.electric time) := rfl
    _ = -passage.electricCurl
        (passage.propagationSpeedSquared •
          passage.magneticCurl (passage.magnetic time)) := by
      rw [passage.electric_firstDifference time]
    _ = (-passage.propagationSpeedSquared) •
        passage.electricCurl (passage.magneticCurl (passage.magnetic time)) := by
      simp

end VacuumMaxwellPassage

/-! ## Lawful receiver folds preserve the propagation equation -/

universe x y

variable {Electric' : Type x} {Magnetic' : Type y}
variable [AddCommGroup Electric'] [Module ℝ Electric']
variable [AddCommGroup Magnetic'] [Module ℝ Magnetic']

/-- A dimensional fold is lawful for this Maxwell passage when it transports both typed field
carriers and intertwines both curl directions.  The kernels of the two receiver maps are the
micro-path populations collapsed by the fold. -/
structure MaxwellReceiverFold
    (passage : VacuumMaxwellPassage (Electric := Electric) (Magnetic := Magnetic)) where
  electricReceiver : Electric →ₗ[ℝ] Electric'
  magneticReceiver : Magnetic →ₗ[ℝ] Magnetic'
  electricCurl : Electric' →ₗ[ℝ] Magnetic'
  magneticCurl : Magnetic' →ₗ[ℝ] Electric'
  electricCurl_natural :
    magneticReceiver.comp passage.electricCurl =
      electricCurl.comp electricReceiver
  magneticCurl_natural :
    electricReceiver.comp passage.magneticCurl =
      magneticCurl.comp magneticReceiver

namespace MaxwellReceiverFold

theorem electricCurl_commutes
    {passage : VacuumMaxwellPassage (Electric := Electric) (Magnetic := Magnetic)}
    (fold : MaxwellReceiverFold passage (Electric' := Electric') (Magnetic' := Magnetic'))
    (field : Electric) :
    fold.magneticReceiver (passage.electricCurl field) =
      fold.electricCurl (fold.electricReceiver field) := by
  exact LinearMap.congr_fun fold.electricCurl_natural field

theorem magneticCurl_commutes
    {passage : VacuumMaxwellPassage (Electric := Electric) (Magnetic := Magnetic)}
    (fold : MaxwellReceiverFold passage (Electric' := Electric') (Magnetic' := Magnetic'))
    (field : Magnetic) :
    fold.electricReceiver (passage.magneticCurl field) =
      fold.magneticCurl (fold.magneticReceiver field) := by
  exact LinearMap.congr_fun fold.magneticCurl_natural field

/-- Every linear receiver commutes with the second returned difference. -/
theorem electricReceiver_secondDifference
    {passage : VacuumMaxwellPassage (Electric := Electric) (Magnetic := Magnetic)}
    (fold : MaxwellReceiverFold passage (Electric' := Electric') (Magnetic' := Magnetic'))
    (time : ℕ) :
    fold.electricReceiver (secondDifference passage.electric time) =
      secondDifference (fun index ↦ fold.electricReceiver (passage.electric index)) time := by
  simp [secondDifference, firstDifference]

/-- A lawful fold retains the electric wave equation exactly, including `c²`. -/
theorem electricWave_preserved
    {passage : VacuumMaxwellPassage (Electric := Electric) (Magnetic := Magnetic)}
    (fold : MaxwellReceiverFold passage (Electric' := Electric') (Magnetic' := Magnetic'))
    (time : ℕ) :
    secondDifference (fun index ↦ fold.electricReceiver (passage.electric index)) time =
      (-passage.propagationSpeedSquared) •
        fold.magneticCurl
          (fold.electricCurl (fold.electricReceiver (passage.electric time))) := by
  rw [← fold.electricReceiver_secondDifference time,
    passage.electric_secondDifference time, map_smul,
    fold.magneticCurl_commutes, fold.electricCurl_commutes]

/-- Every magnetic receiver commutes with the second returned difference. -/
theorem magneticReceiver_secondDifference
    {passage : VacuumMaxwellPassage (Electric := Electric) (Magnetic := Magnetic)}
    (fold : MaxwellReceiverFold passage (Electric' := Electric') (Magnetic' := Magnetic'))
    (time : ℕ) :
    fold.magneticReceiver (secondDifference passage.magnetic time) =
      secondDifference (fun index ↦ fold.magneticReceiver (passage.magnetic index)) time := by
  simp [secondDifference, firstDifference]

/-- A lawful fold retains the magnetic wave equation exactly, including `c²`. -/
theorem magneticWave_preserved
    {passage : VacuumMaxwellPassage (Electric := Electric) (Magnetic := Magnetic)}
    (fold : MaxwellReceiverFold passage (Electric' := Electric') (Magnetic' := Magnetic'))
    (time : ℕ) :
    secondDifference (fun index ↦ fold.magneticReceiver (passage.magnetic index)) time =
      (-passage.propagationSpeedSquared) •
        fold.electricCurl
          (fold.magneticCurl (fold.magneticReceiver (passage.magnetic time))) := by
  rw [← fold.magneticReceiver_secondDifference time,
    passage.magnetic_secondDifference time, map_smul,
    fold.electricCurl_commutes, fold.magneticCurl_commutes]

end MaxwellReceiverFold

/-! ## The full `c²` rest-energy face -/

/-- Rest energy in a declared propagation chart. -/
def restEnergy (mass speed : ℝ) : ℝ := mass * speed ^ 2

/-- Squaring rest energy retains `c⁴`; the inner `c²` is not erased. -/
theorem restEnergy_sq (mass speed : ℝ) :
    restEnergy mass speed ^ 2 = mass ^ 2 * speed ^ 4 := by
  simp [restEnergy]
  ring

theorem VacuumMaxwellPassage.restEnergy_sq_from_constitutive
    (passage : VacuumMaxwellPassage (Electric := Electric) (Magnetic := Magnetic))
    (mass : ℝ) :
    restEnergy mass passage.propagationSpeed ^ 2 =
      mass ^ 2 * passage.propagationSpeedSquared ^ 2 := by
  rw [restEnergy_sq]
  congr 1
  calc
    passage.propagationSpeed ^ 4 =
        (passage.propagationSpeed ^ 2) ^ 2 := by ring
    _ = passage.propagationSpeedSquared ^ 2 := by
      rw [passage.propagationSpeed_sq]

end Soma.Holonics.Millennium.HolonicMaxwellPropagation

section Audit
open Soma.Holonics.Millennium.HolonicMaxwellPropagation
#print axioms firstDifference_deltaChronology
#print axioms periodDisplacement_firstDifference_deltaChronology
#print axioms fieldStrengthThreePlusThreeEquiv_isBijective
#print axioms VacuumMaxwellPassage.propagationSpeedSquared_pos
#print axioms VacuumMaxwellPassage.propagationSpeed_pos
#print axioms VacuumMaxwellPassage.propagationSpeed_sq
#print axioms VacuumMaxwellPassage.propagationSpeedSquared_mul_constitutive
#print axioms VacuumMaxwellPassage.electric_firstDifference
#print axioms VacuumMaxwellPassage.electric_secondDifference
#print axioms VacuumMaxwellPassage.magnetic_secondDifference
#print axioms MaxwellReceiverFold.electricCurl_commutes
#print axioms MaxwellReceiverFold.magneticCurl_commutes
#print axioms MaxwellReceiverFold.electricReceiver_secondDifference
#print axioms MaxwellReceiverFold.electricWave_preserved
#print axioms MaxwellReceiverFold.magneticReceiver_secondDifference
#print axioms MaxwellReceiverFold.magneticWave_preserved
#print axioms restEnergy_sq
#print axioms VacuumMaxwellPassage.restEnergy_sq_from_constitutive
end Audit
