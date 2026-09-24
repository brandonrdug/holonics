import ElementaryHolonics.Millennium.HolonicTorusFlow
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Topology.Path

/-!
# Oriented torus paths and coprime slope embeddings

An integral pair first constructs a continuous oriented loop on the genuine geometric two-torus.
Its canonical real lift starts at zero and returns with exactly that integral displacement; this is
the winding receiver.  The same pair defines a circle map into the torus.  Bézout's identity proves
that a coprime pair makes this map injective, and compact-to-Hausdorff topology upgrades it to an
embedding.  Thus the `(p,q)` torus knot is constructed as an embedded geometric circle in `T^2`,
not as a crossing table.

The traversible-band connection is made at the exact statement its evidence supports: an odd
`m`-half-twist boundary has the coprime slope `(2,m)`.  No isotopy or Euclidean torus-surface theorem
is inferred from the engine's classification enum.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HolonicTorusKnots

open Soma.Holonics
open Topology unitInterval

/-- The genuine geometric two-torus. -/
abbrev GeometricTwoTorus := UnitAddTorus (Fin 2)

/-- The coordinatewise quotient projection from the canonical real covering chart. -/
def realToTwoTorus (x : Fin 2 → ℝ) : GeometricTwoTorus :=
  fun i => (x i : UnitAddCircle)

/-- The canonical straight lift of an integral slope. -/
def torusSlopeLift (winding : Fin 2 → ℤ) (t : ℝ) : Fin 2 → ℝ :=
  fun i => (winding i : ℝ) * t

/-- The intrinsic circle map of the same integral slope. -/
def torusSlopeMap (winding : Fin 2 → ℤ) : C(UnitAddCircle, GeometricTwoTorus) where
  toFun phase i := winding i • phase
  continuous_toFun := by
    rw [continuous_pi_iff]
    intro i
    exact continuous_zsmul (winding i)

@[simp]
theorem torusSlopeMap_apply (winding : Fin 2 → ℤ) (phase : UnitAddCircle) (i : Fin 2) :
    torusSlopeMap winding phase i = winding i • phase := rfl

/-- Projecting the straight lift returns the intrinsic torus circle at every real time. -/
theorem realToTwoTorus_torusSlopeLift (winding : Fin 2 → ℤ) (t : ℝ) :
    realToTwoTorus (torusSlopeLift winding t) =
      torusSlopeMap winding (t : UnitAddCircle) := by
  ext i
  change (((winding i : ℝ) * t : ℝ) : UnitAddCircle) =
    winding i • (t : UnitAddCircle)
  rw [← QuotientAddGroup.mk_zsmul]
  simp only [zsmul_eq_mul]

@[simp]
theorem torusSlopeLift_zero (winding : Fin 2 → ℤ) :
    torusSlopeLift winding 0 = 0 := by
  ext i
  simp [torusSlopeLift]

/-- The lift's endpoint displacement is the integral winding pair in the real chart. -/
theorem torusSlopeLift_endpoint_displacement (winding : Fin 2 → ℤ) (i : Fin 2) :
    torusSlopeLift winding 1 i - torusSlopeLift winding 0 i = winding i := by
  simp [torusSlopeLift]

/-- The integral slope gives a genuinely closed oriented path on the geometric two-torus. -/
def torusSlopePath (winding : Fin 2 → ℤ) :
    Path (0 : GeometricTwoTorus) 0 where
  toContinuousMap :=
    { toFun := fun t => torusSlopeMap winding ((t : ℝ) : UnitAddCircle)
      continuous_toFun :=
        (torusSlopeMap winding).continuous.comp
          (QuotientAddGroup.continuous_mk.comp continuous_subtype_val) }
  source' := by
    ext i
    simp [torusSlopeMap]
  target' := by
    ext i
    simp [torusSlopeMap, ← QuotientAddGroup.mk_zsmul]

/-- The path is carried as an addressed geometric occurrence before its winding is re-read. -/
def torusSlopePathPassage :
    AddressedPassage (Fin 2 → ℤ) (Path (0 : GeometricTwoTorus) 0) :=
  AddressedPassage.graph torusSlopePath

theorem torusSlopePathPassage_retains_winding (winding : Fin 2 → ℤ) :
    Nonempty ((torusSlopePathPassage).Fibre winding (torusSlopePath winding)) :=
  ⟨AddressedPassage.graphFibre _ winding⟩

/-! ## Coprime slopes embed one geometric circle -/

/-- Bézout combines the two coordinate equalities into equality of the source phases. -/
theorem torusSlopeMap_injective_of_coprime (p q : ℕ) (hpq : Nat.Coprime p q) :
    Function.Injective (torusSlopeMap ![(p : ℤ), (q : ℤ)]) := by
  intro x y hxy
  have hp : (p : ℤ) • x = (p : ℤ) • y := by
    simpa [torusSlopeMap] using congrFun hxy 0
  have hq : (q : ℤ) • x = (q : ℤ) • y := by
    simpa [torusSlopeMap] using congrFun hxy 1
  let d : UnitAddCircle := x - y
  have hpd : (p : ℤ) • d = 0 := by
    dsimp [d]
    rw [zsmul_sub, hp, sub_self]
  have hqd : (q : ℤ) • d = 0 := by
    dsimp [d]
    rw [zsmul_sub, hq, sub_self]
  have hbezout :
      (1 : ℤ) = Nat.gcdA p q * (p : ℤ) + Nat.gcdB p q * (q : ℤ) := by
    calc
      (1 : ℤ) = (Nat.gcd p q : ℤ) := by rw [hpq.gcd_eq_one]; norm_num
      _ = (p : ℤ) * Nat.gcdA p q + (q : ℤ) * Nat.gcdB p q :=
        Nat.gcd_eq_gcd_ab p q
      _ = Nat.gcdA p q * (p : ℤ) + Nat.gcdB p q * (q : ℤ) := by ring
  have hd : d = 0 := by
    calc
      d = (1 : ℤ) • d := (one_zsmul _).symm
      _ = (Nat.gcdA p q * (p : ℤ) + Nat.gcdB p q * (q : ℤ)) • d := by
        rw [hbezout]
      _ = Nat.gcdA p q • ((p : ℤ) • d) +
          Nat.gcdB p q • ((q : ℤ) • d) := by
        rw [add_zsmul, mul_zsmul, mul_zsmul]
      _ = 0 := by rw [hpd, hqd]; simp
  exact sub_eq_zero.mp hd

/-- A coprime slope is a closed embedding of a circle in the genuine geometric torus. -/
theorem torusSlopeMap_isEmbedding_of_coprime (p q : ℕ) (hpq : Nat.Coprime p q) :
    IsEmbedding (torusSlopeMap ![(p : ℤ), (q : ℤ)]) :=
  ((torusSlopeMap ![(p : ℤ), (q : ℤ)]).continuous.isClosedEmbedding
    (torusSlopeMap_injective_of_coprime p q hpq)).isEmbedding

/-- The geometric `(p,q)` torus knot is the embedded image of its coprime slope circle. -/
def torusKnotSet (p q : ℕ) : Set GeometricTwoTorus :=
  Set.range (torusSlopeMap ![(p : ℤ), (q : ℤ)])

theorem torusKnotSet_isCompact (p q : ℕ) : IsCompact (torusKnotSet p q) := by
  exact isCompact_range (torusSlopeMap ![(p : ℤ), (q : ℤ)]).continuous

/-! ## The traversible half-twist reading returns the slope `(2,m)` -/

/-- Odd half-twist count is exactly the coprimality needed by the `(2,m)` boundary slope. -/
theorem oddHalfTwist_boundarySlope_coprime (m : ℕ) (hm : Odd m) : Nat.Coprime 2 m :=
  Nat.coprime_two_left.mpr hm

/-- Therefore every odd traversible-band count constructs an embedded `(2,m)` boundary circle. -/
theorem oddHalfTwist_boundary_isTorusKnotEmbedding (m : ℕ) (hm : Odd m) :
    IsEmbedding (torusSlopeMap ![(2 : ℤ), (m : ℤ)]) :=
  torusSlopeMap_isEmbedding_of_coprime 2 m (oddHalfTwist_boundarySlope_coprime m hm)

/-- The constructed boundary's canonical lift returns exactly the asserted `(2,m)` slope. -/
theorem oddHalfTwist_boundary_lift_returns_slope (m : ℕ) (i : Fin 2) :
    torusSlopeLift ![(2 : ℤ), (m : ℤ)] 1 i -
      torusSlopeLift ![(2 : ℤ), (m : ℤ)] 0 i = ![(2 : ℤ), (m : ℤ)] i :=
  torusSlopeLift_endpoint_displacement _ i

/-! ## A finite torus probe does not determine integral winding -/

def slopeModuloFour (winding : Fin 2 → ℤ) : Fin 2 → ZMod 4 :=
  fun i => winding i

/-- Integral slopes `0` and `4` agree at the finite phase probe but are not the same winding. -/
theorem finiteModuloFourProbe_does_not_identify_integralSlope :
    slopeModuloFour ![(0 : ℤ), (0 : ℤ)] = slopeModuloFour ![(4 : ℤ), (0 : ℤ)] ∧
      ![(0 : ℤ), (0 : ℤ)] ≠ ![(4 : ℤ), (0 : ℤ)] := by
  constructor
  · funext i
    fin_cases i <;> decide
  · decide

end Soma.Holonics.Millennium.HolonicTorusKnots

section Audit
open Soma.Holonics.Millennium.HolonicTorusKnots
#print axioms realToTwoTorus_torusSlopeLift
#print axioms torusSlopeLift_endpoint_displacement
#print axioms torusSlopePathPassage_retains_winding
#print axioms torusSlopeMap_injective_of_coprime
#print axioms torusSlopeMap_isEmbedding_of_coprime
#print axioms torusKnotSet_isCompact
#print axioms oddHalfTwist_boundary_isTorusKnotEmbedding
#print axioms oddHalfTwist_boundary_lift_returns_slope
#print axioms finiteModuloFourProbe_does_not_identify_integralSlope
end Audit
