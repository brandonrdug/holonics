import ElementaryHolonics.Geometry.Telescoping
import ElementaryHolonics.Millennium.Horizon
import ElementaryHolonics.Millennium.Polarisation
import ElementaryHolonics.Millennium.Swing
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Difference calculus: orientation before sign, local action before global return

This file makes the common mechanism exact.

An edge first carries an oriented difference `target - source`.  It has no intrinsic positive or
negative label.  Reversal negates it; only an ordered receiver can call the two orientations
positive and negative.  The affine swing is precisely this reversal about its anchor, and Euler's
complex half-turn `exp(pi i) = -1` enacts the same action.

Repeated discrete differentiation takes differences of differences.  Finite integration is exact
telescoping: the sum of all local differences is the one exterior difference.  The window theorem
is the coarse-graining law—every internal face cancels, while the two boundary faces survive.
Modulo is then a declared quotient of the same oriented difference; its zero fibre retains every
integral multiple of the modulus.

These are algebraic transport theorems.  They do not assert that every physical force, charge, or
orientation is scalar-valued, nor that boundary cancellation by itself proves a dynamic
conservation law.
-/

namespace Soma.Holonics.Millennium.HolonicDifferenceCalculus

open scoped BigOperators

/-! ## 1. Orientation is carried before an ordered receiver assigns a sign -/

/-- One addressed geometric comparison, before choosing any ordered coordinate chart. -/
structure OrientedEdge (G : Type*) where
  source : G
  target : G

namespace OrientedEdge

variable {G : Type*} [AddCommGroup G]

/-- The action carried by an oriented edge. -/
def difference (edge : OrientedEdge G) : G := edge.target - edge.source

/-- Reversing an edge exchanges its two addressed boundary faces. -/
def reverse (edge : OrientedEdge G) : OrientedEdge G := ⟨edge.target, edge.source⟩

/-- Orientation reversal negates the difference; no order or magnitude is involved. -/
theorem difference_reverse (edge : OrientedEdge G) :
    edge.reverse.difference = -edge.difference := by
  simp [difference, reverse]

/-- Reversing twice returns the complete addressed edge. -/
theorem reverse_reverse {H : Type*} (edge : OrientedEdge H) : edge.reverse.reverse = edge := by
  cases edge
  rfl

/-- A receiver transports the geometric difference into its own additive chart. -/
def receiverDifference {A : Type*} [AddCommGroup A]
    (receiver : G →+ A) (edge : OrientedEdge G) : A := receiver edge.difference

/-- Receiver transport commutes with reversal. -/
theorem receiverDifference_reverse {A : Type*} [AddCommGroup A]
    (receiver : G →+ A) (edge : OrientedEdge G) :
    receiverDifference receiver edge.reverse = -receiverDifference receiver edge := by
  simp [receiverDifference, difference_reverse]

/-- Only after transport into an ordered chart do the two orientations receive opposite signs.
The invariant is the polarization: whichever orientation is positive, its reverse is negative. -/
theorem nonzeroReceiverDifference_isPolarized
    (receiver : G →+ ℝ) (edge : OrientedEdge G)
    (hne : receiverDifference receiver edge ≠ 0) :
    (receiverDifference receiver edge < 0 ∧
        0 < receiverDifference receiver edge.reverse) ∨
      (0 < receiverDifference receiver edge ∧
        receiverDifference receiver edge.reverse < 0) := by
  rw [receiverDifference_reverse]
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · exact Or.inl ⟨hneg, neg_pos.mpr hneg⟩
  · exact Or.inr ⟨hpos, neg_neg_of_pos hpos⟩

end OrientedEdge

/-! ## 2. The swing and Euler's half-turn enact the same difference reversal -/

/-- The edge from an anchor to the body before the swing. -/
def anchoredEdge {G : Type*} [AddCommGroup G] (anchor body : G) : OrientedEdge G :=
  ⟨anchor, body⟩

/-- The edge from the same anchor to the returned body after the swing. -/
def swungEdge {G : Type*} [AddCommGroup G] (anchor body : G) : OrientedEdge G :=
  ⟨anchor, Swing.swing anchor body⟩

/-- The swing reverses the oriented displacement while keeping the anchor fixed. -/
theorem swing_reversesDifference {G : Type*} [AddCommGroup G] (anchor body : G) :
    (swungEdge anchor body).difference = -(anchoredEdge anchor body).difference := by
  exact Swing.theSwingNegatesTheDisplacementFromTheAnchor anchor body

/-- Euler's complex half-turn acts by negation. -/
theorem eulerHalfTurn_actsByNegation (z : ℂ) :
    Complex.exp (Real.pi * Complex.I) * z = -z := by
  rw [Complex.exp_pi_mul_I]
  ring

/-- In the complex additive chart, the affine swing is multiplication of the displacement by the
Euler half-turn.  The sign is the receiver face of the turn, not a label attached to the body. -/
theorem swingDifference_isEulerHalfTurn (anchor body : ℂ) :
    (swungEdge anchor body).difference =
      Complex.exp (Real.pi * Complex.I) * (anchoredEdge anchor body).difference := by
  rw [swing_reversesDifference, eulerHalfTurn_actsByNegation]

/-! ## 3. The finite Leibniz swing retains the interaction face -/

section FiniteLeibniz

variable {R : Type*} [CommRing R]

/-- Change the left coordinate first while the right coordinate is held at its source occurrence,
then change the right coordinate while the left coordinate is held at its target occurrence.  This
is one exact two-swing path across the product face. -/
theorem productDifference_leftThenRight (left₀ left₁ right₀ right₁ : R) :
    left₁ * right₁ - left₀ * right₀ =
      (left₁ - left₀) * right₀ + left₁ * (right₁ - right₀) := by
  ring

/-- Change the right coordinate first and the left coordinate second.  The intermediate pivot is
different, but the complete returned product difference is the same. -/
theorem productDifference_rightThenLeft (left₀ left₁ right₀ right₁ : R) :
    left₁ * right₁ - left₀ * right₀ =
      left₀ * (right₁ - right₀) + (left₁ - left₀) * right₁ := by
  ring

/-- The two ordered swing paths allocate the mixed interaction face differently while returning
the same exterior difference. -/
theorem productDifference_pathInterchange (left₀ left₁ right₀ right₁ : R) :
    (left₁ - left₀) * right₀ + left₁ * (right₁ - right₀) =
      left₀ * (right₁ - right₀) + (left₁ - left₀) * right₁ := by
  ring

/-- If both coordinate differences are evaluated at the source pivot, the exact remainder is the
mixed face.  Dropping it is precisely the first-order linearization quotient. -/
theorem productDifference_sourceLinearizationWithRemainder
    (left₀ left₁ right₀ right₁ : R) :
    left₁ * right₁ - left₀ * right₀ =
      (left₁ - left₀) * right₀ + left₀ * (right₁ - right₀) +
        (left₁ - left₀) * (right₁ - right₀) := by
  ring

/-- The pair-annihilation departure used by the Boltzmann collision receiver is itself one
oriented difference multiplied by its returned population sum. -/
theorem squareDifference_isDifferenceTimesSum (source target : R) :
    target ^ 2 - source ^ 2 = (target - source) * (target + source) := by
  ring

end FiniteLeibniz

/-! ## 4. Differences of differences -/

variable {G : Type*} [AddCommGroup G]

/-- The first discrete difference of a chronological path. -/
def firstDifference (path : ℕ → G) (time : ℕ) : G :=
  path (time + 1) - path time

/-- The second difference is the change of the first difference. -/
def secondDifference (path : ℕ → G) (time : ℕ) : G :=
  firstDifference path (time + 1) - firstDifference path time

/-- Arbitrarily high discrete differences, retaining their chronological order. -/
def iteratedDifference : ℕ → (ℕ → G) → (ℕ → G)
  | 0, path => path
  | order + 1, path => firstDifference (iteratedDifference order path)

@[simp] theorem iteratedDifference_zero (path : ℕ → G) :
    iteratedDifference 0 path = path := rfl

@[simp] theorem iteratedDifference_succ (order : ℕ) (path : ℕ → G) :
    iteratedDifference (order + 1) path = firstDifference (iteratedDifference order path) := rfl

/-- Every additive receiver commutes with the first difference. -/
theorem receiver_commutes_firstDifference {A : Type*} [AddCommGroup A]
    (receiver : G →+ A) (path : ℕ → G) (time : ℕ) :
    receiver (firstDifference path time) =
      firstDifference (fun n ↦ receiver (path n)) time := by
  simp [firstDifference]

/-- Every additive receiver commutes with every order of discrete differentiation. -/
theorem receiver_commutes_iteratedDifference {A : Type*} [AddCommGroup A]
    (receiver : G →+ A) (order : ℕ) (path : ℕ → G) :
    (fun time ↦ receiver (iteratedDifference order path time)) =
      iteratedDifference order (fun time ↦ receiver (path time)) := by
  induction order with
  | zero => rfl
  | succ order ih =>
      funext time
      rw [show order + 1 = Nat.succ order by omega]
      simp only [iteratedDifference]
      rw [receiver_commutes_firstDifference]
      exact congrFun (congrArg firstDifference ih) time

/-- A path with constant local action. -/
def affinePath (origin step : G) (time : ℕ) : G := origin + time • step

/-- The first difference of an affine path is exactly its step. -/
theorem firstDifference_affinePath (origin step : G) (time : ℕ) :
    firstDifference (affinePath origin step) time = step := by
  simp [firstDifference, affinePath, add_nsmul]

/-- Its difference of differences is zero: acceleration/curvature requires departure from affine
transport rather than a sign convention. -/
theorem secondDifference_affinePath (origin step : G) (time : ℕ) :
    secondDifference (affinePath origin step) time = 0 := by
  simp [secondDifference, firstDifference_affinePath]

/-! ## 5. Galois/monodromy transport is measured by its returned difference -/

/-- The additive defect returned by an automorphism acting on one state.  Field automorphisms,
monodromy actions, gyrations, and chart-return maps enter this carrier through their underlying
additive equivalence. -/
def transportDifference (transport : G ≃+ G) (state : G) : G :=
  transport state - state

/-- The transport defect vanishes exactly on the fixed population. -/
theorem transportDifference_eq_zero_iff_fixed (transport : G ≃+ G) (state : G) :
    transportDifference transport state = 0 ↔ transport state = state := by
  exact sub_eq_zero

/-- Re-expressing the state in another additive chart conjugates the transport. -/
def conjugateTransport {H : Type*} [AddCommGroup H]
    (chart : G ≃+ H) (transport : G ≃+ G) : H ≃+ H :=
  chart.symm.trans (transport.trans chart)

/-- The returned difference is natural under chart transition: the rebased receiver sees exactly
the transported source difference, rather than a newly assigned sign or defect. -/
theorem chart_preserves_transportDifference {H : Type*} [AddCommGroup H]
    (chart : G ≃+ H) (transport : G ≃+ G) (state : G) :
    chart (transportDifference transport state) =
      transportDifference (conjugateTransport chart transport) (chart state) := by
  simp [transportDifference, conjugateTransport]

/-- Iterating one transport gives its chronological orbit. -/
def transportOrbit (transport : G ≃+ G) (state : G) : ℕ → G
  | 0 => state
  | time + 1 => transport (transportOrbit transport state time)

/-- Each local difference along the orbit is the automorphism defect at that occurrence. -/
theorem firstDifference_transportOrbit
    (transport : G ≃+ G) (state : G) (time : ℕ) :
    firstDifference (transportOrbit transport state) time =
      transportDifference transport (transportOrbit transport state time) := by
  simp [firstDifference, transportOrbit, transportDifference]

/-! ## 6. Exact integration and coarse-graining -/

/-- Discrete integration of every local action returns the one exterior difference. -/
theorem localDifferences_integrateToBoundary (path : ℕ → G) (steps : ℕ) :
    (∑ time ∈ Finset.range steps, firstDifference path time) =
      path steps - path 0 := by
  exact Soma.Holonics.finite_telescoping path steps

/-- Windowed integration is the exact coarse-graining law. Every internal face cancels and the two
addressed endpoints survive. -/
theorem windowDifferences_integrateToBoundary
    (path : ℕ → G) (start length : ℕ) :
    (∑ offset ∈ Finset.range length, firstDifference path (start + offset)) =
      path (start + length) - path start := by
  have h := Soma.Holonics.finite_telescoping (fun offset ↦ path (start + offset)) length
  simpa [firstDifference, Nat.add_assoc] using h

/-- Sampling one point per block is a receiver chart on the same path. -/
def coarsePath (path : ℕ → G) (stride : ℕ) (block : ℕ) : G :=
  path (block * stride)

/-- One coarse difference is exactly the integrated population of its microscopic differences. -/
theorem coarseDifference_isIntegratedWindow
    (path : ℕ → G) (stride block : ℕ) :
    firstDifference (coarsePath path stride) block =
      ∑ offset ∈ Finset.range stride,
        firstDifference path (block * stride + offset) := by
  rw [windowDifferences_integrateToBoundary]
  simp [firstDifference, coarsePath, Nat.add_mul]

/-! ## 7. Modulo is a quotient of the oriented difference -/

/-- The integral difference as seen by the modulus-`n` receiver. -/
def modularDifference (n : ℕ) (source target : ℤ) : ZMod n :=
  ((target - source : ℤ) : ZMod n)

/-- Casting commutes with forming the oriented difference. -/
theorem modularDifference_eq_castDifference (n : ℕ) (source target : ℤ) :
    modularDifference n source target =
      (target : ZMod n) - (source : ZMod n) := by
  simp [modularDifference]

/-- Reversing the integral edge negates its modular orientation. -/
theorem modularDifference_reverse (n : ℕ) (source target : ℤ) :
    modularDifference n target source = -modularDifference n source target := by
  simp [modularDifference]

/-- The complete zero fibre of the modular difference is divisibility by the modulus. -/
theorem modularDifference_eq_zero_iff_dvd (n : ℕ) (source target : ℤ) :
    modularDifference n source target = 0 ↔ (n : ℤ) ∣ target - source := by
  exact ZMod.intCast_zmod_eq_zero_iff_dvd (target - source) n

/-- Equivalently, a zero modular difference is exactly congruence of the two endpoints. -/
theorem modularDifference_eq_zero_iff_modEq (n : ℕ) (source target : ℤ) :
    modularDifference n source target = 0 ↔ source ≡ target [ZMOD n] := by
  rw [modularDifference_eq_zero_iff_dvd, Int.modEq_iff_dvd]

/-- A finite modular receiver cannot reconstruct the integral difference: zero and one complete
modulus winding have the same face and distinct endpoints. -/
theorem modularReceiver_reopensIntegralDifference :
    modularDifference 4 0 0 = modularDifference 4 0 4 ∧ (0 : ℤ) ≠ 4 := by
  constructor
  · decide
  · norm_num

/-! ## 8. Euler/Stokes faces of the same difference calculus -/

/-- The minimal Stokes theorem is the adjointness of the local difference and boundary maps. -/
theorem localDifference_globalBoundary_areAdjoint
    (field chain : ℚ × ℚ × ℚ) :
    Polarisation.pair1 (Polarisation.dcoch field) chain =
      Polarisation.pair0 field (Polarisation.bdry chain) :=
  Polarisation.theAdjointnessIsStokes field chain

/-- Adding one local edge/face pair changes the presentation but preserves the Euler return. -/
theorem eulerReturn_survivesLocalEdgeFacePair (vertices edges faces : ℤ) :
    vertices - (edges + 1) + (faces + 1) = vertices - edges + faces :=
  Horizon.theCharacteristicIsInvariantUnderAddingAChord vertices edges faces

end Soma.Holonics.Millennium.HolonicDifferenceCalculus

#print axioms Soma.Holonics.Millennium.HolonicDifferenceCalculus.OrientedEdge.difference_reverse
#print axioms Soma.Holonics.Millennium.HolonicDifferenceCalculus.OrientedEdge.nonzeroReceiverDifference_isPolarized
#print axioms Soma.Holonics.Millennium.HolonicDifferenceCalculus.swingDifference_isEulerHalfTurn
#print axioms Soma.Holonics.Millennium.HolonicDifferenceCalculus.productDifference_leftThenRight
#print axioms Soma.Holonics.Millennium.HolonicDifferenceCalculus.productDifference_pathInterchange
#print axioms Soma.Holonics.Millennium.HolonicDifferenceCalculus.productDifference_sourceLinearizationWithRemainder
#print axioms Soma.Holonics.Millennium.HolonicDifferenceCalculus.squareDifference_isDifferenceTimesSum
#print axioms Soma.Holonics.Millennium.HolonicDifferenceCalculus.receiver_commutes_iteratedDifference
#print axioms Soma.Holonics.Millennium.HolonicDifferenceCalculus.secondDifference_affinePath
#print axioms Soma.Holonics.Millennium.HolonicDifferenceCalculus.transportDifference_eq_zero_iff_fixed
#print axioms Soma.Holonics.Millennium.HolonicDifferenceCalculus.chart_preserves_transportDifference
#print axioms Soma.Holonics.Millennium.HolonicDifferenceCalculus.firstDifference_transportOrbit
#print axioms Soma.Holonics.Millennium.HolonicDifferenceCalculus.coarseDifference_isIntegratedWindow
#print axioms Soma.Holonics.Millennium.HolonicDifferenceCalculus.modularDifference_eq_zero_iff_modEq
#print axioms Soma.Holonics.Millennium.HolonicDifferenceCalculus.modularReceiver_reopensIntegralDifference
#print axioms Soma.Holonics.Millennium.HolonicDifferenceCalculus.localDifference_globalBoundary_areAdjoint
