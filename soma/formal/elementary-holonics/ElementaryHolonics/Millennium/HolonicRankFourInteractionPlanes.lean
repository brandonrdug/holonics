import ElementaryHolonics.Millennium.HolonicDiscreteInduction

/-!
# Rank four returns six interaction planes

**[proved-derived]** The four integral period directions are exactly a `3 + 1` additive carrier
after a receiver chooses one direction as temporal.  Their unordered coordinate pairs form six
oriented interaction planes: three spatial planes and three space--time planes.  This is the finite
exterior-square carrier common to electromagnetic two-forms and to infinitesimal Lorentz
rotations/boosts.  It is the base-plane carrier on which the electromagnetic, weak, strong, and
frame/gravity connections can receive their distinct internal fibres and constitutive laws.

The file also exposes the two distinct occurrences of six in the `(3,4,∞)` torus family.  Rank four
has six coordinate two-planes.  Separately, the source monodromy's invariant alternating form has
the exact readings `Q₀(γ,δ)=1`, `Q₀(u,w)=6`, while its dual bivector has the exchanged
readings `η(γ̂,δ̂)=6`, `η(û,ŵ)=1`.  The integer six is therefore an invariant
incidence multiplicity, not a decimal approximation or a consequence of writing a circle.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HolonicRankFourInteractionPlanes

open Soma.Holonics.Geometry.SixSphereMonodromy
open Soma.Holonics.Geometry.SixSpherePeriods
open Soma.Holonics.Geometry.SixSphereTorusFibre
open Soma.Holonics.Millennium.HolonicDiscreteInduction

/-! ## Exact `3 + 1` reconstruction of the rank-four lattice -/

abbrev SpatialLattice := Fin 3 → ℤ

/-- Selecting the fourth coordinate as the receiver's temporal coordinate is an exact additive
equivalence, not a cardinality comparison: `ℤ³ × ℤ ≃+ ℤ⁴`. -/
def latticeThreePlusOneEquiv : (SpatialLattice × ℤ) ≃+ Lattice where
  toFun state := ![state.1 0, state.1 1, state.1 2, state.2]
  invFun cycle := (![cycle 0, cycle 1, cycle 2], cycle 3)
  left_inv state := by
    rcases state with ⟨spatial, temporal⟩
    apply Prod.ext
    · funext i
      fin_cases i <;> rfl
    · rfl
  right_inv cycle := by
    funext i
    fin_cases i <;> rfl
  map_add' left right := by
    funext i
    fin_cases i <;> rfl

theorem latticeThreePlusOneEquiv_isBijective :
    Function.Bijective latticeThreePlusOneEquiv :=
  latticeThreePlusOneEquiv.bijective

/-! ## The six exterior planes -/

/-- The six increasing pairs of the four ordered period directions. -/
inductive InteractionPlane where
  | gamma_u
  | gamma_w
  | gamma_delta
  | u_w
  | u_delta
  | w_delta
  deriving DecidableEq, Repr

instance : Fintype InteractionPlane :=
  Fintype.ofList [.gamma_u, .gamma_w, .gamma_delta, .u_w, .u_delta, .w_delta] <| by
    intro plane
    cases plane <;> simp

/-- The addressed directions belong to the finite four-torus carrier; this name keeps them
distinct from unrelated notions of direction imported elsewhere in the Millennium atlas. -/
abbrev PeriodDirection :=
  Soma.Holonics.Millennium.HolonicFourTorusCarrier.Direction

def InteractionPlane.directions :
    InteractionPlane → PeriodDirection × PeriodDirection
  | .gamma_u => (gammaDirection, uDirection)
  | .gamma_w => (gammaDirection, wDirection)
  | .gamma_delta => (gammaDirection, deltaDirection)
  | .u_w => (uDirection, wDirection)
  | .u_delta => (uDirection, deltaDirection)
  | .w_delta => (wDirection, deltaDirection)

theorem interactionPlane_count : Fintype.card InteractionPlane = 6 := by decide

theorem InteractionPlane.directions_ne (plane : InteractionPlane) :
    plane.directions.1 ≠ plane.directions.2 := by
  cases plane <;> decide

theorem InteractionPlane.directions_injective :
    Function.Injective InteractionPlane.directions := by decide

/-- A `3 + 1` receiver splits the six planes into three purely spatial rotations and three
space--time transports.  A Lorentz metric upgrades the latter to boosts; the partition itself is
metric-free. -/
inductive ThreePlusOnePlaneKind where
  | spatial
  | spaceTime
  deriving DecidableEq, Repr

instance : Fintype ThreePlusOnePlaneKind :=
  Fintype.ofList [.spatial, .spaceTime] <| by
    intro kind
    cases kind <;> simp

def InteractionPlane.threePlusOneKind : InteractionPlane → ThreePlusOnePlaneKind
  | .gamma_u | .gamma_w | .u_w => .spatial
  | .gamma_delta | .u_delta | .w_delta => .spaceTime

def spatialInteractionPlanes : Finset InteractionPlane :=
  {.gamma_u, .gamma_w, .u_w}

def spaceTimeInteractionPlanes : Finset InteractionPlane :=
  {.gamma_delta, .u_delta, .w_delta}

theorem spatialInteractionPlane_count : spatialInteractionPlanes.card = 3 := by decide

theorem spaceTimeInteractionPlane_count : spaceTimeInteractionPlanes.card = 3 := by decide

theorem interactionPlane_partition (plane : InteractionPlane) :
    (plane ∈ spatialInteractionPlanes ∨ plane ∈ spaceTimeInteractionPlanes) ∧
      ¬ (plane ∈ spatialInteractionPlanes ∧ plane ∈ spaceTimeInteractionPlanes) := by
  cases plane <;> decide

/-! ## The exact six-plane readings of the source forms -/

def basisDirection (direction : PeriodDirection) : Lattice := Pi.single direction 1

def planeReading (form : LatticeEnd) (plane : InteractionPlane) : ℤ :=
  dotProduct (basisDirection plane.directions.1)
    (form.mulVec (basisDirection plane.directions.2))

/-- The primitive invariant alternating form on the primal lattice reads only the two complementary
planes, with multiplicities one and six. -/
theorem Q0_sixPlaneReadings :
    planeReading Q0 .gamma_u = 0 ∧
    planeReading Q0 .gamma_w = 0 ∧
    planeReading Q0 .gamma_delta = 1 ∧
    planeReading Q0 .u_w = 6 ∧
    planeReading Q0 .u_delta = 0 ∧
    planeReading Q0 .w_delta = 0 := by
  decide

/-- The invariant dual bivector exchanges the two nonzero multiplicities. -/
theorem eta_sixPlaneReadings :
    planeReading periodBivector .gamma_u = 0 ∧
    planeReading periodBivector .gamma_w = 0 ∧
    planeReading periodBivector .gamma_delta = 6 ∧
    planeReading periodBivector .u_w = 1 ∧
    planeReading periodBivector .u_delta = 0 ∧
    planeReading periodBivector .w_delta = 0 := by
  decide

/-! ## What `(6μ,β)` is -/

/-- The left period block couples its two source columns through the exact determinant
`6μ² - τβ`.  Thus `(6μ,β)` is one complex-two displacement column; it is not a map from
`6μ` to `β`. -/
theorem periodCore_det (point : PeriodPoint) :
    (Z point).det = 6 * point.μ ^ 2 - point.τ * point.β := by
  simp [Z, Matrix.det_fin_two]
  ring

/-- Every signed winding population has this exact displacement on the universal cover. -/
theorem periodColumnVector_coordinates (point : PeriodPoint) (cycle : Lattice) :
    periodColumnVector point cycle =
      ![6 * point.μ * (cycle gammaDirection : ℂ) +
          point.τ * (cycle uDirection : ℂ) + (cycle wDirection : ℂ),
        point.β * (cycle gammaDirection : ℂ) +
          point.μ * (cycle uDirection : ℂ) + (cycle deltaDirection : ℂ)] := by
  ext coordinate
  fin_cases coordinate <;>
    simp [periodColumnVector, periodMatrix, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, gammaDirection, uDirection, wDirection, deltaDirection] <;>
    ring

/-- Under the source's nondegeneracy hypotheses, the integral period map is injective exactly.
Hence its image lattice is a faithful copy of `ℤ⁴`, not an approximate model of it. -/
theorem periodColumnVector_injective
    (point : PeriodPoint) (hτ : 0 < point.τ.im) (hD : D point < 0) :
    Function.Injective (periodColumnVector point) :=
  (periodColumnVector_isClosedEmbedding point hτ hD).injective

end Soma.Holonics.Millennium.HolonicRankFourInteractionPlanes

section Audit
open Soma.Holonics.Millennium.HolonicRankFourInteractionPlanes
#print axioms latticeThreePlusOneEquiv_isBijective
#print axioms interactionPlane_count
#print axioms InteractionPlane.directions_ne
#print axioms InteractionPlane.directions_injective
#print axioms spatialInteractionPlane_count
#print axioms spaceTimeInteractionPlane_count
#print axioms interactionPlane_partition
#print axioms Q0_sixPlaneReadings
#print axioms eta_sixPlaneReadings
#print axioms periodCore_det
#print axioms periodColumnVector_coordinates
#print axioms periodColumnVector_injective
end Audit
