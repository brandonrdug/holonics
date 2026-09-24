import ElementaryHolonics.Millennium.HolonicDiscreteInduction
import ElementaryHolonics.Millennium.HolonicFieldTheoryPassage
import ElementaryHolonics.Millennium.HolonicFourForceSectorCarrier
import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# Entropy, action, and induction as one typed successor-current passage

**[proved-derived]** This file installs the exact common carrier exposed by the entropy/action
sources without making probability a microscopic governor.  A local successor law carries one
addressed state to the next and records its returned difference.  Mathematical induction extends
that law through every finite successor word.  Faraday induction is then an actual source-specific
instance: magnetic-flux difference is the transported coordinate and negative face circulation is
its source.

The entropy law is a storage/current/production balance

`S (k+1) - S k + outwardFlux k = production k`.

It telescopes exactly.  Closed-system monotonicity is proved only after outward flux vanishes and
the declared constitutive production is nonnegative.  This separates the kinematic Stokes law from
the material second-law hypothesis.

The relativistic thermal receiver contributes a second exact object.  The local derivative of the
inverse-temperature covector splits into a symmetric stretch and an antisymmetric turn.  The turn
changes sign under reversal and vanishes on a repeated direction.  A physical realization still
supplies the spacetime derivative, stress--energy, spin current, and boundary conditions.

Finally a fixed-temperature constitutive map sends the entropy quantity line into the energy line,
so physical free energy is typed as `E - Theta(S)`.  A nonnegative dissipation law proves descent
for a closed grain.  Variational free energy from a probabilistic generative receiver is deliberately
not identified with this physical quantity.  Equal scalar entropy coordinates also fail to determine
successor conduct whenever a richer successor receiver separates their histories.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HolonicEntropyActionInduction

open scoped BigOperators
open Soma.Holonics
open Soma.Holonics.Millennium.HolonicDiscreteInduction
open Soma.Holonics.Millennium.HolonicFourTorusCarrier
open Soma.Holonics.Millennium.HolonicRankFourInteractionPlanes
open Soma.Holonics.Millennium.HolonicInteractionExterior
open Soma.Holonics.Millennium.HolonicFourForceSectorCarrier

/-! ## One local successor law, promoted through every finite word -/

/-- The exact orbit generated from one initial occurrence. -/
def successorOrbit {State : Type*} (successor : State → State) (initial : State) : ℕ → State
  | 0 => initial
  | n + 1 => successor (successorOrbit successor initial n)

@[simp] theorem successorOrbit_zero {State : Type*}
    (successor : State → State) (initial : State) :
    successorOrbit successor initial 0 = initial :=
  rfl

@[simp] theorem successorOrbit_succ {State : Type*}
    (successor : State → State) (initial : State) (n : ℕ) :
    successorOrbit successor initial (n + 1) =
      successor (successorOrbit successor initial n) :=
  rfl

/-- One source-indexed additive coordinate transported through a deterministic successor. -/
structure SuccessorCurrent (State Current : Type*) [AddCommGroup Current] where
  successor : State → State
  coordinate : State → Current
  source : State → Current
  localLaw : ∀ state,
    coordinate (successor state) - coordinate state = source state

/-- Structural induction is the exact local-to-global promotion of the successor-current law. -/
theorem SuccessorCurrent.telescopes
    {State Current : Type*} [AddCommGroup Current]
    (law : SuccessorCurrent State Current) (initial : State) (steps : ℕ) :
    law.coordinate (successorOrbit law.successor initial steps) -
        law.coordinate initial =
      ∑ k ∈ Finset.range steps,
        law.source (successorOrbit law.successor initial k) := by
  induction steps with
  | zero => simp
  | succ steps ih =>
      rw [Finset.sum_range_succ]
      simp only [successorOrbit_succ]
      calc
        law.coordinate (law.successor (successorOrbit law.successor initial steps)) -
            law.coordinate initial =
          (law.coordinate (law.successor (successorOrbit law.successor initial steps)) -
              law.coordinate (successorOrbit law.successor initial steps)) +
            (law.coordinate (successorOrbit law.successor initial steps) -
              law.coordinate initial) := by abel
        _ = law.source (successorOrbit law.successor initial steps) +
            (law.coordinate (successorOrbit law.successor initial steps) -
              law.coordinate initial) := by rw [law.localLaw]
        _ = (law.coordinate (successorOrbit law.successor initial steps) -
              law.coordinate initial) +
            law.source (successorOrbit law.successor initial steps) := by abel
        _ = (∑ k ∈ Finset.range steps,
              law.source (successorOrbit law.successor initial k)) +
            law.source (successorOrbit law.successor initial steps) := by rw [ih]

/-- A zero local source makes the transported coordinate invariant along every finite successor
word.  The base occurrence and the preservation square are both explicit. -/
theorem SuccessorCurrent.invariant_of_zero_source
    {State Current : Type*} [AddCommGroup Current]
    (law : SuccessorCurrent State Current)
    (source_zero : ∀ state, law.source state = 0)
    (initial : State) (steps : ℕ) :
    law.coordinate (successorOrbit law.successor initial steps) =
      law.coordinate initial := by
  have telescoped := law.telescopes initial steps
  simp [source_zero] at telescoped
  exact sub_eq_zero.mp telescoped

/-! ## Faraday induction inhabits the successor-current carrier -/

/-- One fixed face of an exact Faraday history, read as a successor-current law.  Flux is the
coordinate and negative circulation is its returned source. -/
def faradaySuccessorCurrent
    {grain : ℕ}
    (flux : ℕ → FaceSection grain) (emf : ℕ → EdgeSection grain)
    (hfaraday : SatisfiesFaradayHistory flux emf) (face : Face grain) :
    SuccessorCurrent ℕ ℝ where
  successor := Nat.succ
  coordinate time := flux time face
  source time := -faceCirculation (emf time) face
  localLaw time := by
    have returned := hfaraday time face
    linarith

theorem successorOrbit_natSucc (initial steps : ℕ) :
    successorOrbit Nat.succ initial steps = initial + steps := by
  induction steps with
  | zero => simp
  | succ steps ih => simp [ih, Nat.add_assoc]

/-- The generic successor theorem reconstructs the existing finite Faraday telescope. -/
theorem faradaySuccessorCurrent_telescopes
    {grain : ℕ}
    (flux : ℕ → FaceSection grain) (emf : ℕ → EdgeSection grain)
    (hfaraday : SatisfiesFaradayHistory flux emf) (steps : ℕ) (face : Face grain) :
    flux steps face - flux 0 face =
      ∑ time ∈ Finset.range steps, -faceCirculation (emf time) face := by
  simpa [faradaySuccessorCurrent, successorOrbit_natSucc] using
    (faradaySuccessorCurrent flux emf hfaraday face).telescopes 0 steps

/-! ## Exact entropy storage, flux, and production -/

/-- A time-grained entropy-line balance.  `outwardFlux` is positive in the outward hand;
`production` is an interior source.  Nonnegativity is a separate constitutive field below. -/
structure CurrentBalance (Quantity : Type*) [AddCommGroup Quantity] where
  storage : ℕ → Quantity
  outwardFlux : ℕ → Quantity
  production : ℕ → Quantity
  localBalance : ∀ k,
    storage (k + 1) - storage k + outwardFlux k = production k

/-- The world-tube difference equals total interior production minus the side-boundary current,
with no limit, rounding, or probability distribution. -/
theorem CurrentBalance.telescopes
    {Quantity : Type*} [AddCommGroup Quantity]
    (balance : CurrentBalance Quantity) (steps : ℕ) :
    balance.storage steps - balance.storage 0 +
        ∑ k ∈ Finset.range steps, balance.outwardFlux k =
      ∑ k ∈ Finset.range steps, balance.production k := by
  rw [← Soma.Holonics.finite_telescoping balance.storage steps]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  exact balance.localBalance k

/-- A quantity-line balance may be closed only after projection to a declared receiver: side
current is allowed to survive in the source provided it lies in the receiver kernel.  The returned
difference is then exactly the receiver image of the interior production. -/
theorem CurrentBalance.receiver_difference_eq_production
    {Quantity Reading : Type*}
    [AddCommGroup Quantity]
    [AddCommGroup Reading]
    (balance : CurrentBalance Quantity) (receiver : Quantity →+ Reading)
    (boundary_in_kernel : ∀ k, balance.outwardFlux k ∈ receiver.ker)
    (steps : ℕ) :
    receiver (balance.storage steps - balance.storage 0) =
      ∑ k ∈ Finset.range steps, receiver (balance.production k) := by
  have returned := congrArg receiver (balance.telescopes steps)
  simpa [map_add, map_sub, map_sum,
    show (∑ k ∈ Finset.range steps, receiver (balance.outwardFlux k)) = 0 by
      exact Finset.sum_eq_zero fun k _hk ↦ boundary_in_kernel k] using returned

/-- Entropy increase is relative to a receiver cone, not an absolute scalar clock.  It is enough
for the boundary current to be null in that receiver and for the received production to lie in its
chosen positive cone. -/
theorem CurrentBalance.receiver_monotone_of_boundary_kernel
    {Quantity Reading : Type*}
    [AddCommGroup Quantity]
    [AddCommGroup Reading] [LinearOrder Reading] [IsOrderedAddMonoid Reading]
    (balance : CurrentBalance Quantity) (receiver : Quantity →+ Reading)
    (boundary_in_kernel : ∀ k, balance.outwardFlux k ∈ receiver.ker)
    (production_nonnegative : ∀ k, 0 ≤ receiver (balance.production k)) :
    Monotone (fun k ↦ receiver (balance.storage k)) := by
  apply monotone_nat_of_le_succ
  intro k
  apply sub_nonneg.mp
  have returned := congrArg receiver (balance.localBalance k)
  have hboundary : receiver (balance.outwardFlux k) = 0 := boundary_in_kernel k
  have hdifference :
      receiver (balance.storage (k + 1)) - receiver (balance.storage k) =
        receiver (balance.production k) := by
    simpa [map_add, map_sub, hboundary] using returned
  rw [hdifference]
  exact production_nonnegative k

/-- Receiver-null total entropy change is equivalent to receiver-nullity of every nonnegative
local production grain.  Source currents hidden in the receiver kernel are retained rather than
silently deleted. -/
theorem CurrentBalance.receiver_difference_eq_zero_iff
    {Quantity Reading : Type*}
    [AddCommGroup Quantity]
    [AddCommGroup Reading] [LinearOrder Reading] [IsOrderedAddMonoid Reading]
    (balance : CurrentBalance Quantity) (receiver : Quantity →+ Reading)
    (boundary_in_kernel : ∀ k, balance.outwardFlux k ∈ receiver.ker)
    (production_nonnegative : ∀ k, 0 ≤ receiver (balance.production k))
    (steps : ℕ) :
    receiver (balance.storage steps - balance.storage 0) = 0 ↔
      ∀ k ∈ Finset.range steps, receiver (balance.production k) = 0 := by
  rw [balance.receiver_difference_eq_production receiver boundary_in_kernel steps]
  exact Finset.sum_eq_zero_iff_of_nonneg fun k _hk ↦ production_nonnegative k

/-- The second-law datum: production is nonnegative in the declared entropy receiver. -/
structure EntropyCurrentBalance (EntropyLine : Type*)
    [AddCommGroup EntropyLine] [LinearOrder EntropyLine] [IsOrderedAddMonoid EntropyLine]
    extends CurrentBalance EntropyLine where
  production_nonnegative : ∀ k, 0 ≤ production k

/-- With no side-boundary entropy current, nonnegative constitutive production makes stored
entropy monotone. -/
theorem EntropyCurrentBalance.closed_monotone
    {EntropyLine : Type*}
    [AddCommGroup EntropyLine] [LinearOrder EntropyLine] [IsOrderedAddMonoid EntropyLine]
    (balance : EntropyCurrentBalance EntropyLine)
    (closed : ∀ k, balance.outwardFlux k = 0) :
    Monotone balance.storage := by
  apply monotone_nat_of_le_succ
  intro k
  apply sub_nonneg.mp
  rw [show balance.storage (k + 1) - balance.storage k = balance.production k by
    have hlocal := balance.localBalance k
    simpa [closed k] using hlocal]
  exact balance.production_nonnegative k

/-- Over a closed finite world-tube the terminal stored entropy exceeds the initial reading by the
exact summed production. -/
theorem EntropyCurrentBalance.closed_difference_eq_production
    {EntropyLine : Type*}
    [AddCommGroup EntropyLine] [LinearOrder EntropyLine] [IsOrderedAddMonoid EntropyLine]
    (balance : EntropyCurrentBalance EntropyLine)
    (closed : ∀ k, balance.outwardFlux k = 0) (steps : ℕ) :
    balance.storage steps - balance.storage 0 =
      ∑ k ∈ Finset.range steps, balance.production k := by
  simpa [closed] using balance.toCurrentBalance.telescopes steps

/-- On a closed finite world-tube, a null returned entropy difference is not an unexplained
scalar cancellation: it is equivalent to the vanishing of every admitted nonnegative local
production grain.  This is the exact finite local-to-global `nullity of the null' law. -/
theorem EntropyCurrentBalance.closed_difference_eq_zero_iff
    {EntropyLine : Type*}
    [AddCommGroup EntropyLine] [LinearOrder EntropyLine] [IsOrderedAddMonoid EntropyLine]
    (balance : EntropyCurrentBalance EntropyLine)
    (closed : ∀ k, balance.outwardFlux k = 0) (steps : ℕ) :
    balance.storage steps - balance.storage 0 = 0 ↔
      ∀ k ∈ Finset.range steps, balance.production k = 0 := by
  rw [balance.closed_difference_eq_production closed steps]
  exact Finset.sum_eq_zero_iff_of_nonneg fun k _hk ↦ balance.production_nonnegative k

/-! ## The local thermal turn and stretch -/

/-- One local coordinate derivative of an inverse-temperature covector on four addressed axes. -/
abbrev ThermalGradient := Fin 4 → Fin 4 → ℚ

/-- Symmetric receiver stretch: `(Dᵢⱼ + Dⱼᵢ)/2`. -/
def thermalStretch (derivative : ThermalGradient) : ThermalGradient :=
  fun i j ↦ (derivative i j + derivative j i) / 2

/-- Antisymmetric receiver turn: `(Dᵢⱼ - Dⱼᵢ)/2`. -/
def thermalTurn (derivative : ThermalGradient) : ThermalGradient :=
  fun i j ↦ (derivative i j - derivative j i) / 2

theorem thermalGradient_eq_stretch_add_turn (derivative : ThermalGradient) :
    derivative = thermalStretch derivative + thermalTurn derivative := by
  funext i j
  simp [thermalStretch, thermalTurn]
  ring

theorem thermalStretch_swap (derivative : ThermalGradient) (i j : Fin 4) :
    thermalStretch derivative j i = thermalStretch derivative i j := by
  simp [thermalStretch, add_comm]

theorem thermalTurn_swap (derivative : ThermalGradient) (i j : Fin 4) :
    thermalTurn derivative j i = -thermalTurn derivative i j := by
  simp [thermalTurn]
  ring

theorem thermalTurn_self (derivative : ThermalGradient) (i : Fin 4) :
    thermalTurn derivative i i = 0 := by
  simp [thermalTurn]

/-! ## Monotone interaction produces a nonnegative oriented difference -/

/-- The algebraic core of the relativistic H-theorem: a monotone constitutive response pairs an
oriented occurrence difference with a difference of the same hand. -/
theorem monotoneDifference_product_nonnegative
    {Scalar : Type*} [Ring Scalar] [LinearOrder Scalar] [IsStrictOrderedRing Scalar]
    (response : Scalar → Scalar) (monotone_response : Monotone response)
    (source target : Scalar) :
    0 ≤ (target - source) * (response target - response source) := by
  rcases le_total source target with hforward | hreverse
  · exact mul_nonneg (sub_nonneg.mpr hforward)
      (sub_nonneg.mpr (monotone_response hforward))
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hreverse)
      (sub_nonpos.mpr (monotone_response hreverse))

/-- Sum the positive interaction grain over an exact finite occurrence population. -/
def interactionProduction
    {Occurrence Scalar : Type*}
    [Ring Scalar] [LinearOrder Scalar] [IsStrictOrderedRing Scalar]
    (population : Finset Occurrence) (conductance : Occurrence → Scalar)
    (source target : Occurrence → Scalar) (response : Scalar → Scalar) : Scalar :=
  ∑ occurrence ∈ population,
    conductance occurrence *
      ((target occurrence - source occurrence) *
        (response (target occurrence) - response (source occurrence)))

theorem interactionProduction_nonnegative
    {Occurrence Scalar : Type*}
    [Ring Scalar] [LinearOrder Scalar] [IsStrictOrderedRing Scalar]
    (population : Finset Occurrence) (conductance : Occurrence → Scalar)
    (source target : Occurrence → Scalar) (response : Scalar → Scalar)
    (conductance_nonnegative : ∀ occurrence ∈ population, 0 ≤ conductance occurrence)
    (monotone_response : Monotone response) :
    0 ≤ interactionProduction population conductance source target response := by
  apply Finset.sum_nonneg
  intro occurrence hoccurrence
  exact mul_nonneg (conductance_nonnegative occurrence hoccurrence)
    (monotoneDifference_product_nonnegative response monotone_response
      (source occurrence) (target occurrence))

/-! ## Strict difference and transverse entropy current

The nonnegative interaction theorem is deliberately only weak: a monotone response may have a
nontrivial kernel.  A strictly monotone constitution removes that receiver radical.  Its local
production vanishes exactly when the transported coordinate has no returned difference, and a
nonzero difference produces a strictly positive interaction grain.

Two independent current directions carry more information than either scalar coordinate.  Their
alternating product is the exact two-current seen by an oriented receiver plane.  This is the
finite exterior-current face of the four cyclic directions in the polygonal four-torus carrier:
exchanging either the receiver axes or the two presented holons reverses the sign, while aligned
currents have zero transverse reading.  Zero transverse reading retains a reconstruction fibre;
it does not identify the two currents. -/

/-- Under a strict constitution, the local interaction grain has no hidden scalar kernel. -/
theorem strictMonotoneDifference_product_eq_zero_iff
    {Scalar : Type*} [Ring Scalar] [LinearOrder Scalar] [IsStrictOrderedRing Scalar]
    (response : Scalar → Scalar) (strict_response : StrictMono response)
    (source target : Scalar) :
    (target - source) * (response target - response source) = 0 ↔ target = source := by
  constructor
  · intro hzero
    rcases mul_eq_zero.mp hzero with hcoordinate | hresponse
    · exact sub_eq_zero.mp hcoordinate
    · exact strict_response.injective (sub_eq_zero.mp hresponse)
  · rintro rfl
    simp

/-- `There is a difference' is exactly strict positive production after the constitutive kernel
has been removed. -/
theorem strictMonotoneDifference_product_pos_iff
    {Scalar : Type*} [Ring Scalar] [LinearOrder Scalar] [IsStrictOrderedRing Scalar]
    (response : Scalar → Scalar) (strict_response : StrictMono response)
    (source target : Scalar) :
    0 < (target - source) * (response target - response source) ↔ target ≠ source := by
  constructor
  · intro hpositive hequal
    subst target
    simpa using hpositive
  · intro hdifference
    have hnonnegative :
        0 ≤ (target - source) * (response target - response source) :=
      monotoneDifference_product_nonnegative response strict_response.monotone source target
    have hnonzero :
        (target - source) * (response target - response source) ≠ 0 := by
      intro hzero
      exact hdifference
        ((strictMonotoneDifference_product_eq_zero_iff
          response strict_response source target).mp hzero)
    exact lt_of_le_of_ne hnonnegative hnonzero.symm

/-- With positive conductance and a strict constitutive response, a null total interaction
production has no hidden cancellation: every transported occurrence has returned to the same
coordinate.  Conversely, any receiver-visible difference makes one positive grain and therefore
prevents the total current from vanishing. -/
theorem interactionProduction_eq_zero_iff_of_strict
    {Occurrence Scalar : Type*}
    [Ring Scalar] [LinearOrder Scalar] [IsStrictOrderedRing Scalar]
    (population : Finset Occurrence) (conductance : Occurrence → Scalar)
    (source target : Occurrence → Scalar) (response : Scalar → Scalar)
    (conductance_positive : ∀ occurrence ∈ population, 0 < conductance occurrence)
    (strict_response : StrictMono response) :
    interactionProduction population conductance source target response = 0 ↔
      ∀ occurrence ∈ population, target occurrence = source occurrence := by
  rw [interactionProduction,
    Finset.sum_eq_zero_iff_of_nonneg (fun occurrence hoccurrence ↦
      mul_nonneg (le_of_lt (conductance_positive occurrence hoccurrence))
        (monotoneDifference_product_nonnegative response strict_response.monotone
          (source occurrence) (target occurrence)))]
  refine forall_congr' fun occurrence ↦ forall_congr' fun hoccurrence ↦ ?_
  constructor
  · intro hzero
    rcases mul_eq_zero.mp hzero with hconductance | hlocal
    · exact False.elim ((ne_of_gt (conductance_positive occurrence hoccurrence)) hconductance)
    · exact (strictMonotoneDifference_product_eq_zero_iff response strict_response
        (source occurrence) (target occurrence)).mp hlocal
  · intro hequal
    exact mul_eq_zero.mpr <| Or.inr <|
      (strictMonotoneDifference_product_eq_zero_iff response strict_response
        (source occurrence) (target occurrence)).mpr hequal

/-- One entropy/action current with four addressed torus winding coordinates. -/
abbrev FourTorusEntropyCurrent (Scalar : Type*) := Direction → Scalar

/-- The oriented transverse current on the receiver plane spanned by `first` and `second`.
This is a determinant/exterior product, not a product of two silently identified time units. -/
def entropyAxisCrossCurrent
    {Scalar : Type*} [CommRing Scalar]
    (left right : FourTorusEntropyCurrent Scalar) (first second : Direction) : Scalar :=
  left first * right second - left second * right first

/-- On integral winding populations the entropy/action two-current is exactly the already-owned
six-plane cycle wedge, rather than a second interaction ontology. -/
theorem entropyAxisCrossCurrent_eq_cycleWedge
    (left right : Soma.Holonics.Geometry.SixSphereMonodromy.Lattice)
    (plane : InteractionPlane) :
    entropyAxisCrossCurrent left right plane.directions.1 plane.directions.2 =
      cycleWedge left right plane :=
  rfl

/-- Changing the common four-axis chart before forming the entropy/action two-current is exactly
the exterior-square transport of its six interaction-plane coordinates.  Thus the two time/current
axes remain distinct tensor factors, while their oriented transverse receiver is basis covariant. -/
theorem entropyAxisCrossCurrent_natural
    (transport : Soma.Holonics.Geometry.SixSphereMonodromy.LatticeEnd)
    (left right : Soma.Holonics.Geometry.SixSphereMonodromy.Lattice) :
    (fun index : Fin 6 ↦
      entropyAxisCrossCurrent (transport.mulVec left) (transport.mulVec right)
        (interactionPlaneEquivFinSix.symm index).directions.1
        (interactionPlaneEquivFinSix.symm index).directions.2) =
      (exteriorSquareAction transport).mulVec
        (fun index : Fin 6 ↦
          entropyAxisCrossCurrent left right
            (interactionPlaneEquivFinSix.symm index).directions.1
            (interactionPlaneEquivFinSix.symm index).directions.2) := by
  exact cycleWedge_natural transport left right

/-- Reversing the receiver plane reverses the returned orientation. -/
theorem entropyAxisCrossCurrent_swap_axes
    {Scalar : Type*} [CommRing Scalar]
    (left right : FourTorusEntropyCurrent Scalar) (first second : Direction) :
    entropyAxisCrossCurrent left right second first =
      -entropyAxisCrossCurrent left right first second := by
  simp [entropyAxisCrossCurrent]

/-- Reversing the order of the interacting holons reverses the returned orientation. -/
theorem entropyAxisCrossCurrent_swap_holons
    {Scalar : Type*} [CommRing Scalar]
    (left right : FourTorusEntropyCurrent Scalar) (first second : Direction) :
    entropyAxisCrossCurrent right left first second =
      -entropyAxisCrossCurrent left right first second := by
  simp [entropyAxisCrossCurrent]
  ring

/-- Outside the zero-cross fibre, exchanging the interacting currents is genuinely
noncommutative at the oriented receiver. -/
theorem entropyAxisCrossCurrent_swap_holons_ne
    {Scalar : Type*} [CommRing Scalar] [LinearOrder Scalar] [IsStrictOrderedRing Scalar]
    {left right : FourTorusEntropyCurrent Scalar} {first second : Direction}
    (hcross : entropyAxisCrossCurrent left right first second ≠ 0) :
    entropyAxisCrossCurrent right left first second ≠
      entropyAxisCrossCurrent left right first second := by
  rw [entropyAxisCrossCurrent_swap_holons]
  intro hequal
  apply hcross
  linarith

/-- A current has no transverse difference from itself. -/
theorem entropyAxisCrossCurrent_self
    {Scalar : Type*} [CommRing Scalar]
    (current : FourTorusEntropyCurrent Scalar) (first second : Direction) :
    entropyAxisCrossCurrent current current first second = 0 := by
  simp [entropyAxisCrossCurrent]
  ring

/-- Relatively aligned currents have zero transverse receiver current. -/
theorem entropyAxisCrossCurrent_aligned
    {Scalar : Type*} [CommRing Scalar]
    (scale : Scalar) (current : FourTorusEntropyCurrent Scalar)
    (first second : Direction) :
    entropyAxisCrossCurrent current (fun axis ↦ scale * current axis) first second = 0 := by
  simp [entropyAxisCrossCurrent]
  ring

/-- A nonzero transverse current certifies a receiver-visible oriented difference. -/
theorem entropyAxisCrossCurrent_ne_zero_implies_ne
    {Scalar : Type*} [CommRing Scalar]
    {left right : FourTorusEntropyCurrent Scalar} {first second : Direction}
    (hcross : entropyAxisCrossCurrent left right first second ≠ 0) :
    left ≠ right := by
  intro hequal
  subst right
  exact hcross (entropyAxisCrossCurrent_self left first second)

/-- A nonzero transverse entropy current rules out relative alignment on the observed receiver
plane.  This is stronger than merely separating the two complete current sections. -/
theorem entropyAxisCrossCurrent_ne_zero_implies_plane_not_aligned
    {Scalar : Type*} [CommRing Scalar]
    {left right : FourTorusEntropyCurrent Scalar} {first second : Direction}
    (hcross : entropyAxisCrossCurrent left right first second ≠ 0) :
    ¬ ∃ scale : Scalar,
      right first = scale * left first ∧ right second = scale * left second := by
  rintro ⟨scale, hfirst, hsecond⟩
  apply hcross
  simp [entropyAxisCrossCurrent, hfirst, hsecond]
  ring

/-- Over a field, the complete six-plane zero reading reconstructs one common current line,
provided the reference current itself is nonzero.  A single zero plane retains a large fibre, but
simultaneous nullity on every torus plane is exactly relative alignment. -/
theorem allEntropyAxisCrossCurrents_zero_iff_aligned
    {Scalar : Type*} [Field Scalar]
    {left right : FourTorusEntropyCurrent Scalar} (hleft : left ≠ 0) :
    (∀ first second : Direction,
        entropyAxisCrossCurrent left right first second = 0) ↔
      ∃ scale : Scalar, right = fun axis ↦ scale * left axis := by
  constructor
  · intro hcross
    have hpivot : ∃ pivot : Direction, left pivot ≠ 0 := by
      by_contra hnone
      apply hleft
      funext axis
      by_contra haxis
      exact hnone ⟨axis, haxis⟩
    obtain ⟨pivot, hpivot⟩ := hpivot
    refine ⟨right pivot / left pivot, ?_⟩
    funext axis
    have hplane := hcross pivot axis
    simp only [entropyAxisCrossCurrent] at hplane
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff hpivot).2
    calc
      right axis * left pivot = left pivot * right axis := mul_comm _ _
      _ = left axis * right pivot := sub_eq_zero.mp hplane
      _ = right pivot * left axis := mul_comm _ _
  · rintro ⟨scale, rfl⟩
    intro first second
    exact entropyAxisCrossCurrent_aligned scale left first second

/-- Exact one-event Leibniz return for an evolving transverse entropy/action current.  The two
time axes remain distinct: one term transports the left-current difference against the old right
current, while the other transports the new left current against the right-current difference. -/
theorem entropyAxisCrossCurrent_returnedDifference
    {Scalar : Type*} [CommRing Scalar]
    (leftBefore leftAfter rightBefore rightAfter : FourTorusEntropyCurrent Scalar)
    (first second : Direction) :
    entropyAxisCrossCurrent leftAfter rightAfter first second -
        entropyAxisCrossCurrent leftBefore rightBefore first second =
      entropyAxisCrossCurrent (leftAfter - leftBefore) rightBefore first second +
        entropyAxisCrossCurrent leftAfter (rightAfter - rightBefore) first second := by
  simp [entropyAxisCrossCurrent]
  ring

/-- The complete family of currents collapsed by one oriented two-axis receiver. -/
def EntropyAxisCrossFiber
    {Scalar : Type*} [CommRing Scalar]
    (reference : FourTorusEntropyCurrent Scalar) (first second : Direction) :=
  {current : FourTorusEntropyCurrent Scalar //
    entropyAxisCrossCurrent reference current first second = 0}

/-- Zero transverse current is not source equality: distinct aligned currents occupy the same
receiver fibre. -/
theorem entropyAxisCrossFiber_nontrivial :
    let unit : FourTorusEntropyCurrent ℚ := fun axis ↦ if axis = 0 then 1 else 0
    let double : FourTorusEntropyCurrent ℚ := fun axis ↦ if axis = 0 then 2 else 0
    unit ≠ double ∧ entropyAxisCrossCurrent unit double 0 1 = 0 := by
  dsimp
  constructor
  · intro hequal
    have hcoordinate := congrFun hequal (0 : Direction)
    norm_num at hcoordinate
  · norm_num [entropyAxisCrossCurrent]

/-! ## Conservative turn and dissipative crossing -/

/-- One source-specific skew--dissipative constitutive law.  The alternating bilinear form is the
conservative turn read against a gradient; `dissipation` is the positive crossing of its level
sets; `source` retains every boundary/correction contribution. -/
structure SkewDissipativeTurnLaw (Gradient : Type*)
    [AddCommGroup Gradient] [Module ℚ Gradient] where
  turn : LinearMap.BilinForm ℚ Gradient
  turn_alternating : turn.IsAlt
  dissipation : Gradient → ℚ
  dissipation_nonnegative : ∀ gradient, 0 ≤ dissipation gradient
  source : Gradient → ℚ
  returnedRate : Gradient → ℚ
  constitutiveLaw : ∀ gradient,
    returnedRate gradient =
      turn gradient gradient - dissipation gradient + source gradient

/-- Alternation annihilates the conservative self-pairing exactly, leaving negative dissipation
plus the explicit source/boundary term. -/
theorem SkewDissipativeTurnLaw.returnedRate_eq
    {Gradient : Type*} [AddCommGroup Gradient] [Module ℚ Gradient]
    (law : SkewDissipativeTurnLaw Gradient) (gradient : Gradient) :
    law.returnedRate gradient =
      -law.dissipation gradient + law.source gradient := by
  rw [law.constitutiveLaw, law.turn_alternating.self_eq_zero]
  simp

/-- With no correction or boundary source, the skew part circulates while the positive part makes
the returned potential rate nonpositive. -/
theorem SkewDissipativeTurnLaw.returnedRate_nonpositive_of_source_zero
    {Gradient : Type*} [AddCommGroup Gradient] [Module ℚ Gradient]
    (law : SkewDissipativeTurnLaw Gradient) (gradient : Gradient)
    (source_zero : law.source gradient = 0) :
    law.returnedRate gradient ≤ 0 := by
  rw [law.returnedRate_eq, source_zero, add_zero]
  exact neg_nonpos.mpr (law.dissipation_nonnegative gradient)

/-! ## Typed physical free energy -/

/-- At fixed temperature over one admitted grain, the thermal constitution is an additive map
from the entropy quantity line to the energy quantity line. -/
structure ThermalConstitution (EntropyLine EnergyLine : Type*)
    [AddCommGroup EntropyLine] [AddCommGroup EnergyLine] where
  entropyToEnergy : EntropyLine →+ EnergyLine

/-- Physical free energy in the declared chart: `E - Theta(S)`. -/
def freeEnergy
    {EntropyLine EnergyLine : Type*}
    [AddCommGroup EntropyLine] [AddCommGroup EnergyLine]
    (constitution : ThermalConstitution EntropyLine EnergyLine)
    (energy : EnergyLine) (entropy : EntropyLine) : EnergyLine :=
  energy - constitution.entropyToEnergy entropy

/-- The complete returned free-energy difference keeps energy and entropy differences separate. -/
theorem freeEnergy_difference
    {EntropyLine EnergyLine : Type*}
    [AddCommGroup EntropyLine] [AddCommGroup EnergyLine]
    (constitution : ThermalConstitution EntropyLine EnergyLine)
    (energySource energyTarget : EnergyLine)
    (entropySource entropyTarget : EntropyLine) :
    freeEnergy constitution energyTarget entropyTarget -
        freeEnergy constitution energySource entropySource =
      (energyTarget - energySource) -
        constitution.entropyToEnergy (entropyTarget - entropySource) := by
  simp [freeEnergy]
  abel

/-- Rational-coordinate specialization of a fixed temperature. -/
def rationalTemperatureConstitution (temperature : ℚ) :
    ThermalConstitution ℚ ℚ where
  entropyToEnergy :=
    { toFun := fun entropy ↦ temperature * entropy
      map_zero' := by simp
      map_add' := by intro left right; ring }

theorem rational_freeEnergy (temperature energy entropy : ℚ) :
    freeEnergy (rationalTemperatureConstitution temperature) energy entropy =
      energy - temperature * entropy :=
  rfl

/-- One physical free-energy balance.  Boundary power and dissipation are distinct energy-line
faces; the law is not inferred from the phrase "least action". -/
structure FreeEnergyBalanceGrain (EntropyLine EnergyLine : Type*)
    [AddCommGroup EntropyLine]
    [AddCommGroup EnergyLine] [LinearOrder EnergyLine] [IsOrderedAddMonoid EnergyLine] where
  constitution : ThermalConstitution EntropyLine EnergyLine
  energyBefore : EnergyLine
  energyAfter : EnergyLine
  entropyBefore : EntropyLine
  entropyAfter : EntropyLine
  boundaryPower : EnergyLine
  dissipation : EnergyLine
  dissipation_nonnegative : 0 ≤ dissipation
  balance :
    freeEnergy constitution energyAfter entropyAfter + dissipation =
      freeEnergy constitution energyBefore entropyBefore + boundaryPower

/-- A closed grain with nonnegative dissipation cannot increase physical free energy. -/
theorem FreeEnergyBalanceGrain.closed_descends
    {EntropyLine EnergyLine : Type*}
    [AddCommGroup EntropyLine]
    [AddCommGroup EnergyLine] [LinearOrder EnergyLine] [IsOrderedAddMonoid EnergyLine]
    (grain : FreeEnergyBalanceGrain EntropyLine EnergyLine)
    (closed : grain.boundaryPower = 0) :
    freeEnergy grain.constitution grain.energyAfter grain.entropyAfter ≤
      freeEnergy grain.constitution grain.energyBefore grain.entropyBefore := by
  have returned := grain.balance
  rw [closed, add_zero] at returned
  calc
    freeEnergy grain.constitution grain.energyAfter grain.entropyAfter =
        freeEnergy grain.constitution grain.energyAfter grain.entropyAfter + 0 := by simp
    _ ≤ freeEnergy grain.constitution grain.energyAfter grain.entropyAfter +
        grain.dissipation := by
      simpa [add_comm] using
        (add_le_add_left grain.dissipation_nonnegative
          (freeEnergy grain.constitution grain.energyAfter grain.entropyAfter))
    _ = freeEnergy grain.constitution grain.energyBefore grain.entropyBefore := returned

/-! ## Entropy-coordinate receiver insufficiency -/

/-- Equal entropy coordinates do not found equal deterministic continuation.  When a successor
receiver separates two histories in one entropy fibre, no successor law can factor through that
entropy receiver. -/
theorem no_successor_factor_of_equal_entropy
    {History EntropyReading SuccessorReading : Type*}
    (entropy : History → EntropyReading)
    (successor : History → SuccessorReading)
    {left right : History}
    (sameEntropy : entropy left = entropy right)
    (differentSuccessor : successor left ≠ successor right) :
    ¬ ∃ descend : EntropyReading → SuccessorReading,
      successor = descend ∘ entropy := by
  rintro ⟨descend, factors⟩
  apply differentSuccessor
  calc
    successor left = descend (entropy left) := congrFun factors left
    _ = descend (entropy right) := congrArg descend sameEntropy
    _ = successor right := (congrFun factors right).symm

end Soma.Holonics.Millennium.HolonicEntropyActionInduction

section Audit
open Soma.Holonics.Millennium.HolonicEntropyActionInduction
#print axioms SuccessorCurrent.telescopes
#print axioms SuccessorCurrent.invariant_of_zero_source
#print axioms faradaySuccessorCurrent_telescopes
#print axioms CurrentBalance.telescopes
#print axioms CurrentBalance.receiver_difference_eq_production
#print axioms CurrentBalance.receiver_monotone_of_boundary_kernel
#print axioms CurrentBalance.receiver_difference_eq_zero_iff
#print axioms EntropyCurrentBalance.closed_monotone
#print axioms EntropyCurrentBalance.closed_difference_eq_production
#print axioms EntropyCurrentBalance.closed_difference_eq_zero_iff
#print axioms thermalGradient_eq_stretch_add_turn
#print axioms thermalTurn_swap
#print axioms monotoneDifference_product_nonnegative
#print axioms interactionProduction_nonnegative
#print axioms interactionProduction_eq_zero_iff_of_strict
#print axioms strictMonotoneDifference_product_eq_zero_iff
#print axioms strictMonotoneDifference_product_pos_iff
#print axioms entropyAxisCrossCurrent_swap_axes
#print axioms entropyAxisCrossCurrent_eq_cycleWedge
#print axioms entropyAxisCrossCurrent_natural
#print axioms entropyAxisCrossCurrent_swap_holons
#print axioms entropyAxisCrossCurrent_swap_holons_ne
#print axioms entropyAxisCrossCurrent_aligned
#print axioms entropyAxisCrossCurrent_ne_zero_implies_ne
#print axioms entropyAxisCrossCurrent_ne_zero_implies_plane_not_aligned
#print axioms allEntropyAxisCrossCurrents_zero_iff_aligned
#print axioms entropyAxisCrossCurrent_returnedDifference
#print axioms entropyAxisCrossFiber_nontrivial
#print axioms SkewDissipativeTurnLaw.returnedRate_eq
#print axioms SkewDissipativeTurnLaw.returnedRate_nonpositive_of_source_zero
#print axioms freeEnergy_difference
#print axioms FreeEnergyBalanceGrain.closed_descends
#print axioms no_successor_factor_of_equal_entropy
end Audit
