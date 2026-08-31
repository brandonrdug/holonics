import ElementaryHolonics.Millennium.HolonicFourTorusParametronRealization
import ElementaryHolonics.Millennium.HolonicEntropyActionInduction

/-!
# The torus winding holon is exactly its realized Complex Parametron current image

The finite four-torus already realizes every integral period vector as an exact branch-current
section of the Complex Parametron incidence body, and the four cut receivers reconstruct that
period vector.  This file packages those two maps as an equivalence with the *realized image*.
It does not identify an arbitrary Parametron branch section with a torus winding: the complementary
branch-current fibre remains outside the image.

The same passage realizes the entropy/action exterior two-current.  After the four cut receivers
recover two realized winding currents, their transverse current is exactly the real-coordinate
cast of the integral cellular cycle wedge.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HolonicTorusEntropyParametronEquivalence

open Soma.Holonics.Geometry.SixSphereMonodromy
open Soma.Holonics.Millennium.HolonicFourForceSectorCarrier
open Soma.Holonics.Millennium.HolonicFourTorusCarrier
open Soma.Holonics.Millennium.HolonicFourTorusParametronRealization
open Soma.Holonics.Millennium.HolonicEntropyActionInduction
open Soma.Holonics.Millennium.HolonicRankFourInteractionPlanes

/-- The complete branch-current section produced by one integral four-torus winding. -/
def realizedWindingCurrent (grain : ℕ) (cycle : Lattice) :
    ParametronBranch grain → ℝ :=
  chainDrive (axisCycleRealization (grain := grain) cycle)

/-- Four cut-current receivers reconstruct the integral winding coordinates after the exact
integer-to-real chart. -/
theorem fourAxisCurrentReceiver_realizedWindingCurrent
    (grain : ℕ) (cycle : Lattice) :
    fourAxisCurrentReceiver (realizedWindingCurrent grain cycle) =
      fun direction ↦ (cycle direction : ℝ) := by
  exact fourAxisCurrentReceiver_realization cycle

/-- The realized Complex Parametron branch-current chart loses no torus winding occurrence. -/
theorem realizedWindingCurrent_injective (grain : ℕ) :
    Function.Injective (realizedWindingCurrent grain) := by
  intro left right hequal
  have hreceiver := congrArg fourAxisCurrentReceiver hequal
  rw [fourAxisCurrentReceiver_realizedWindingCurrent,
    fourAxisCurrentReceiver_realizedWindingCurrent] at hreceiver
  funext direction
  have hcoordinate := congrFun hreceiver direction
  exact_mod_cast hcoordinate

/-- The exact torus/Parametron equivalence at the winding-current stratum.  The codomain is the
actual realized image, so no arbitrary branch current is silently called toroidal. -/
def windingLatticeEquivRealizedParametronCurrent (grain : ℕ) :
    Lattice ≃ {current : ParametronBranch grain → ℝ //
      current ∈ Set.range (realizedWindingCurrent grain)} :=
  Equiv.ofInjective (realizedWindingCurrent grain)
    (realizedWindingCurrent_injective grain)

/-- The transverse entropy/action current seen after physical realization is exactly the cast
integral two-current on the corresponding torus interaction plane. -/
theorem entropyAxisCrossCurrent_realizedWindingCurrent
    (grain : ℕ) (left right : Lattice)
    (plane :
      Soma.Holonics.Millennium.HolonicRankFourInteractionPlanes.InteractionPlane) :
    entropyAxisCrossCurrent
        (fourAxisCurrentReceiver (realizedWindingCurrent grain left))
        (fourAxisCurrentReceiver (realizedWindingCurrent grain right))
        plane.directions.1 plane.directions.2 =
      (cycleWedge left right plane : ℝ) := by
  rw [fourAxisCurrentReceiver_realizedWindingCurrent,
    fourAxisCurrentReceiver_realizedWindingCurrent]
  simp only [entropyAxisCrossCurrent, cycleWedge]
  norm_cast

/-- All realized transverse currents vanish exactly when the two nonzero-reference winding
sections lie on one rational current line.  The scalar is rational because the source winding
coordinates are integral; the complete realized branch sections remain distinct occurrences. -/
theorem all_realizedEntropyAxisCrossCurrents_zero_iff_aligned
    {left right : Lattice} (hleft : left ≠ 0) :
    (∀ first second : Direction,
        entropyAxisCrossCurrent
          (fun axis ↦ (left axis : ℚ)) (fun axis ↦ (right axis : ℚ))
          first second = 0) ↔
      ∃ scale : ℚ,
        (fun axis ↦ (right axis : ℚ)) =
          fun axis ↦ scale * (left axis : ℚ) := by
  apply allEntropyAxisCrossCurrents_zero_iff_aligned
  intro hzero
  apply hleft
  funext axis
  have hcoordinate : (left axis : ℚ) = 0 := by
    simpa using congrFun hzero axis
  have : left axis = 0 := by exact_mod_cast hcoordinate
  simpa using this

section Audit

#print axioms fourAxisCurrentReceiver_realizedWindingCurrent
#print axioms realizedWindingCurrent_injective
#print axioms windingLatticeEquivRealizedParametronCurrent
#print axioms entropyAxisCrossCurrent_realizedWindingCurrent
#print axioms all_realizedEntropyAxisCrossCurrents_zero_iff_aligned

end Audit

end Soma.Holonics.Millennium.HolonicTorusEntropyParametronEquivalence
