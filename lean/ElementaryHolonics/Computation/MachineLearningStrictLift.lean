import ElementaryHolonics.Computation.MachineLearningChart
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Tactic

/-!
# Kernel invariance and strict holonic lift

A larger native carrier is not by itself a stronger machine.  The exact distinction is dynamic:
a classical linear receiver chart descends through a native transport precisely when the chart's
reconstruction kernel is preserved.  If one hidden direction is transported into a visible
direction, no classical successor on that quotient can make the square commute.
-/

namespace Soma.Holonics.Computation.MachineLearningStrictLift

universe uK uV uQ

variable {𝕜 : Type uK} {V : Type uV} {Q : Type uQ}
variable [Field 𝕜]
variable [AddCommGroup V] [Module 𝕜 V]
variable [AddCommGroup Q] [Module 𝕜 Q]

/-- The native transport preserves every difference hidden by the receiver chart. -/
def KernelInvariant (quotient : V →ₗ[𝕜] Q) (transport : V →ₗ[𝕜] V) : Prop :=
  LinearMap.ker quotient ≤ (LinearMap.ker quotient).comap transport

/-- Any descended classical transport forces invariance of the complete receiver kernel. -/
theorem kernelInvariant_of_descendedTransport
    (quotient : V →ₗ[𝕜] Q) (native : V →ₗ[𝕜] V) (classical : Q →ₗ[𝕜] Q)
  (commutes : ∀ value, quotient (native value) = classical (quotient value)) :
    KernelInvariant quotient native := by
  intro hidden hhidden
  change quotient (native hidden) = 0
  rw [commutes, LinearMap.mem_ker.mp hhidden, map_zero]

/--
If the kernel is invariant, the native linear transport has a canonical transport on the quotient
by that complete kernel.
-/
def descendedKernelQuotientTransport
    (quotient : V →ₗ[𝕜] Q) (native : V →ₗ[𝕜] V)
    (invariant : KernelInvariant quotient native) :
    (V ⧸ LinearMap.ker quotient) →ₗ[𝕜] (V ⧸ LinearMap.ker quotient) :=
  (LinearMap.ker quotient).mapQ (LinearMap.ker quotient) native invariant

/-- The canonical quotient transport commutes with every native occurrence. -/
theorem descendedKernelQuotientTransport_exact
    (quotient : V →ₗ[𝕜] Q) (native : V →ₗ[𝕜] V)
    (invariant : KernelInvariant quotient native) (value : V) :
    (LinearMap.ker quotient).mkQ (native value) =
      descendedKernelQuotientTransport quotient native invariant
        ((LinearMap.ker quotient).mkQ value) := by
  rfl

/--
One hidden difference which becomes receiver-visible obstructs every classical successor transport
on that chart.
-/
theorem visibleTransportedKernel_obstructsEveryDescent
    (quotient : V →ₗ[𝕜] Q) (native : V →ₗ[𝕜] V) (hidden : V)
    (hidden_now : hidden ∈ LinearMap.ker quotient)
    (visible_later : quotient (native hidden) ≠ 0) :
    ¬ ∃ classical : Q →ₗ[𝕜] Q,
      ∀ value, quotient (native value) = classical (quotient value) := by
  rintro ⟨classical, commutes⟩
  have invariant := kernelInvariant_of_descendedTransport quotient native classical commutes
  have transportedHidden : native hidden ∈ LinearMap.ker quotient := invariant hidden_now
  exact visible_later (LinearMap.mem_ker.mp transportedHidden)

/--
The strict-lift witness: two native occurrences share one present classical face, but an admitted
native successor separates their future classical faces.
-/
structure StrictLiftWitness
    (quotient : V →ₗ[𝕜] Q) (native : V →ₗ[𝕜] V) where
  left : V
  right : V
  samePresentFace : quotient left = quotient right
  differentFutureFace : quotient (native left) ≠ quotient (native right)

/-- A strict-lift witness rules out every descended linear classical transport. -/
theorem StrictLiftWitness.noLinearDescent
    {quotient : V →ₗ[𝕜] Q} {native : V →ₗ[𝕜] V}
    (witness : StrictLiftWitness quotient native) :
    ¬ ∃ classical : Q →ₗ[𝕜] Q,
      ∀ value, quotient (native value) = classical (quotient value) := by
  rintro ⟨classical, commutes⟩
  apply witness.differentFutureFace
  rw [commutes, commutes, witness.samePresentFace]

/-! ## A two-dimensional control -/

namespace Control

/-- A classical receiver sees only the first rational coordinate. -/
def firstCoordinate : (ℚ × ℚ) →ₗ[ℚ] ℚ where
  toFun := Prod.fst
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The native successor exchanges visible and hidden coordinates. -/
def exchange : (ℚ × ℚ) →ₗ[ℚ] (ℚ × ℚ) where
  toFun := Prod.swap
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The second-coordinate impulse is presently hidden. -/
theorem secondImpulse_hidden :
    ((0, 1) : ℚ × ℚ) ∈ LinearMap.ker firstCoordinate := by
  rw [LinearMap.mem_ker]
  rfl

/-- One exchange makes that same impulse receiver-visible. -/
theorem secondImpulse_visibleAfterExchange :
    firstCoordinate (exchange ((0, 1) : ℚ × ℚ)) ≠ 0 := by
  norm_num [firstCoordinate, exchange]

/-- This fixed one-coordinate machine cannot represent the exchanged native transport. -/
theorem exchangeStrictlyReopensFirstCoordinate :
    ¬ ∃ classical : ℚ →ₗ[ℚ] ℚ,
      ∀ value, firstCoordinate (exchange value) = classical (firstCoordinate value) :=
  visibleTransportedKernel_obstructsEveryDescent
    firstCoordinate exchange (0, 1) secondImpulse_hidden secondImpulse_visibleAfterExchange

end Control

end Soma.Holonics.Computation.MachineLearningStrictLift

section Audit
open Soma.Holonics.Computation.MachineLearningStrictLift
#print axioms kernelInvariant_of_descendedTransport
#print axioms descendedKernelQuotientTransport_exact
#print axioms visibleTransportedKernel_obstructsEveryDescent
#print axioms StrictLiftWitness.noLinearDescent
#print axioms Control.exchangeStrictlyReopensFirstCoordinate
end Audit
