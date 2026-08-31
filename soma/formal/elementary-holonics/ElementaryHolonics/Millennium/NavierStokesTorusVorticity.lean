import ElementaryHolonics.Millennium.NavierStokesOpenLifespan
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Compactness.LocallyCompact

/-!
# Periodic vorticity as a continuous field on the three-torus

The Euclidean presentation of a periodic Navier--Stokes field contains infinitely many copies of
the same spatial event.  This module descends those copies through the actual quotient projection
`ℝ³ → (ℝ / ℤ)³`.  The descended vorticity world-tube is jointly continuous on every open interior
time slab, and currying it gives a continuous path in the Banach space of continuous torus fields.

The final norm theorem is an exact receiver statement: a real number bounds the continuous-map
norm if and only if it bounds the Euclidean vorticity norm at every spatial point.  Thus no chosen
fundamental-domain representative enters the `L∞ₓ` reading.
-/

noncomputable section

open ContDiff Function Set Topology

namespace Soma.Holonics.Millennium.NavierStokesTorusVorticity

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesVorticity
open Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy
open Soma.Holonics.Millennium.NavierStokesFiniteTimeVorticity
open Soma.Holonics.Millennium.NavierStokesOpenLifespan

/-- The compact spatial carrier of a three-dimensional unit-periodic field. -/
abbrev SpatialTorus := UnitAddTorus (Fin 3)

/-- Coordinatewise quotient projection from the ordinary function presentation of `ℝ³`. -/
def piToSpatialTorus (x : Fin 3 → ℝ) : SpatialTorus := fun i => (x i : UnitAddCircle)

/-- The finite product of the three circle quotient maps is itself an open quotient map. -/
theorem piToSpatialTorus_isOpenQuotientMap :
    IsOpenQuotientMap piToSpatialTorus := by
  have hcoordinate : ∀ _i : Fin 3,
      IsOpenQuotientMap ((↑) : ℝ → UnitAddCircle) :=
    fun _i => QuotientAddGroup.isOpenQuotientMap_mk
  change IsOpenQuotientMap (Pi.map (fun _i : Fin 3 => ((↑) : ℝ → UnitAddCircle)))
  exact IsOpenQuotientMap.piMap hcoordinate

/-- The quotient projection in the repository's Euclidean-space presentation. -/
def euclideanToSpatialTorus (x : Space) : SpatialTorus :=
  piToSpatialTorus ((EuclideanSpace.equiv (Fin 3) ℝ) x)

/-- The Euclidean-to-torus projection is an open quotient map. -/
theorem euclideanToSpatialTorus_isOpenQuotientMap :
    IsOpenQuotientMap euclideanToSpatialTorus := by
  have hcoordinates := piToSpatialTorus_isOpenQuotientMap
  have heuclidean :=
    (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isOpenQuotientMap
  change IsOpenQuotientMap
    (piToSpatialTorus ∘ (EuclideanSpace.equiv (Fin 3) ℝ))
  exact hcoordinates.comp heuclidean

/-- Every torus point has a Euclidean representative. -/
theorem euclideanToSpatialTorus_surjective :
    Function.Surjective euclideanToSpatialTorus :=
  euclideanToSpatialTorus_isOpenQuotientMap.surjective

/-- A fixed representative used only to define quotient lifts.  All observable theorems below
remove this choice by periodicity. -/
def euclideanRepresentative (q : SpatialTorus) : Space :=
  Classical.choose (euclideanToSpatialTorus_surjective q)

@[simp]
theorem euclideanToSpatialTorus_representative (q : SpatialTorus) :
    euclideanToSpatialTorus (euclideanRepresentative q) = q :=
  Classical.choose_spec (euclideanToSpatialTorus_surjective q)

/-! ## Exact descent of one-periodic fields -/

/-- A field with each coordinate period equal to one is constant on every fibre of the torus
projection. -/
theorem isOnePeriodic_eq_of_euclideanToSpatialTorus_eq
    {F : Type*} (field : Space → F) (hperiodic : IsOnePeriodic field)
    {x y : Space} (hxy : euclideanToSpatialTorus x = euclideanToSpatialTorus y) :
    field x = field y := by
  classical
  have hcoordinate : ∀ i : Fin 3,
      (y i : UnitAddCircle) = (x i : UnitAddCircle) := by
    intro i
    have hi := congrFun hxy.symm i
    simpa [euclideanToSpatialTorus, piToSpatialTorus] using hi
  have hinteger : ∀ i : Fin 3, ∃ z : ℤ, x i = y i + z • (1 : ℝ) := by
    intro i
    have hmod : y i ≡ x i [PMOD (1 : ℝ)] :=
      AddCommGroup.modEq_iff_eq_mod_zmultiples.mpr (hcoordinate i)
    exact AddCommGroup.modEq_iff_eq_add_zsmul.mp hmod
  choose z hz using hinteger
  have hspace : x =
      ((y + z 0 • EuclideanSpace.single 0 (1 : ℝ)) +
        z 1 • EuclideanSpace.single 1 (1 : ℝ)) +
          z 2 • EuclideanSpace.single 2 (1 : ℝ) := by
    ext j
    fin_cases j <;> simp [EuclideanSpace.single_apply, hz]
  have hshift (i : Fin 3) :
      Function.Periodic field (z i • EuclideanSpace.single i (1 : ℝ)) :=
    ((show Function.Periodic field (EuclideanSpace.single i (1 : ℝ)) from
      fun x => hperiodic x i).zsmul (z i))
  rw [hspace]
  calc
    field (((y + z 0 • EuclideanSpace.single 0 (1 : ℝ)) +
        z 1 • EuclideanSpace.single 1 (1 : ℝ)) +
          z 2 • EuclideanSpace.single 2 (1 : ℝ)) =
      field ((y + z 0 • EuclideanSpace.single 0 (1 : ℝ)) +
        z 1 • EuclideanSpace.single 1 (1 : ℝ)) := hshift 2 _
    _ = field (y + z 0 • EuclideanSpace.single 0 (1 : ℝ)) := hshift 1 _
    _ = field y := hshift 0 _

/-- The quotient lift of a one-periodic field. -/
def periodicTorusLiftFunction
    {F : Type*} (field : Space → F) (_hperiodic : IsOnePeriodic field) :
    SpatialTorus → F :=
  fun q => field (euclideanRepresentative q)

@[simp]
theorem periodicTorusLiftFunction_projection
    {F : Type*} (field : Space → F) (hperiodic : IsOnePeriodic field) (x : Space) :
    periodicTorusLiftFunction field hperiodic (euclideanToSpatialTorus x) = field x := by
  apply isOnePeriodic_eq_of_euclideanToSpatialTorus_eq field hperiodic
  exact euclideanToSpatialTorus_representative _

/-- Continuous one-periodic Euclidean fields descend to continuous torus fields. -/
def periodicTorusLift
    {F : Type*} [TopologicalSpace F]
    (field : Space → F) (hcontinuous : Continuous field)
    (hperiodic : IsOnePeriodic field) : C(SpatialTorus, F) where
  toFun := periodicTorusLiftFunction field hperiodic
  continuous_toFun := by
    rw [← euclideanToSpatialTorus_isOpenQuotientMap.continuous_comp_iff]
    have heq : periodicTorusLiftFunction field hperiodic ∘ euclideanToSpatialTorus = field := by
      funext x
      exact periodicTorusLiftFunction_projection field hperiodic x
    rw [heq]
    exact hcontinuous

@[simp]
theorem periodicTorusLift_projection
    {F : Type*} [TopologicalSpace F]
    (field : Space → F) (hcontinuous : Continuous field)
    (hperiodic : IsOnePeriodic field) (x : Space) :
    periodicTorusLift field hcontinuous hperiodic (euclideanToSpatialTorus x) = field x :=
  periodicTorusLiftFunction_projection field hperiodic x

/-! ## The open-lifespan vorticity world-tube -/

/-- Vorticity is jointly smooth on the complete open interior of an open-lifespan solution.  The
proof uses only a compact closed slab chosen strictly beyond the queried event. -/
theorem openPeriodicSolutionOn_vorticityField_contDiffOn_interior
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure) :
    ContDiffOn ℝ ∞ (Function.uncurry (vorticityField velocity))
      (Set.univ ×ˢ Ioo 0 T) := by
  intro z hz
  let S : ℝ := (z.2 + T) / 2
  have hS0 : 0 < S := by dsimp [S]; linarith [hz.2.1, hz.2.2]
  have hzS : z.2 < S := by dsimp [S]; linarith [hz.2.2]
  have hST : S < T := by dsimp [S]; linarith [hz.2.2]
  let closed := solution.toClosedInterior hS0 hST
  have hsmooth :=
    smoothSolutionOn_vorticityField_contDiffOn_interior closed.toSmoothSolutionOn
  have hnhds :
      Soma.Holonics.Millennium.NavierStokesFiniteTimeVorticity.openSpaceTimeSlab S ∈ nhds z := by
    simpa [Soma.Holonics.Millennium.NavierStokesFiniteTimeVorticity.openSpaceTimeSlab] using
      (prod_mem_nhds Filter.univ_mem (Ioo_mem_nhds hz.2.1 hzS))
  exact (hsmooth.contDiffAt hnhds).contDiffWithinAt

/-- Interior vorticity slices of an open periodic solution retain all three unit periods. -/
theorem openPeriodicSolutionOn_vorticityField_isOnePeriodic
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    IsOnePeriodic (fun x => vorticityField velocity x t) :=
  vorticityField_isOnePeriodic velocity t
    (solution.velocityPeriodic t ⟨ht.1.le, ht.2⟩)

/-- The jointly continuous vorticity field after quotienting the spatial copies. -/
def torusVorticityWorldTube
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure) :
    C((Ioo 0 T) × SpatialTorus, Space) where
  toFun := fun z => vorticityField velocity (euclideanRepresentative z.2) z.1.1
  continuous_toFun := by
    have hsource : Continuous
        (fun z : (Ioo 0 T) × Space => vorticityField velocity z.2 z.1.1) := by
      rw [continuous_iff_continuousAt]
      intro z
      have hvorticityAt : ContinuousAt (Function.uncurry (vorticityField velocity))
          (z.2, z.1.1) := by
        exact ((openPeriodicSolutionOn_vorticityField_contDiffOn_interior solution).contDiffAt
          (prod_mem_nhds Filter.univ_mem (Ioo_mem_nhds z.1.2.1 z.1.2.2))).continuousAt
      have hpair : ContinuousAt
          (fun w : (Ioo 0 T) × Space => (w.2, w.1.1)) z :=
        continuousAt_snd.prodMk (continuousAt_subtype_val.comp continuousAt_fst)
      have hcomp := ContinuousAt.comp_of_eq
        (f := fun w : (Ioo 0 T) × Space => (w.2, w.1.1))
        (g := Function.uncurry (vorticityField velocity))
        hvorticityAt hpair rfl
      simpa [Function.comp_def, Function.uncurry] using hcomp
    letI : LocallyCompactSpace (Ioo 0 T) := isOpen_Ioo.locallyCompactSpace
    apply euclideanToSpatialTorus_isOpenQuotientMap.isQuotientMap.continuous_lift_prod_right
    apply hsource.congr
    intro z
    apply isOnePeriodic_eq_of_euclideanToSpatialTorus_eq
        (fun x => vorticityField velocity x z.1.1)
        (openPeriodicSolutionOn_vorticityField_isOnePeriodic solution z.1.2)
    exact (euclideanToSpatialTorus_representative _).symm

/-- The vorticity current is a continuous path through continuous spatial torus fields. -/
def torusVorticityEvolution
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure) :
    C(Ioo 0 T, C(SpatialTorus, Space)) :=
  ContinuousMap.curry (torusVorticityWorldTube solution)

/-- The bundled evolution really is continuous in the compact-open (equivalently here, uniform)
topology on continuous torus fields. -/
theorem continuous_torusVorticityEvolution
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure) :
    Continuous (torusVorticityEvolution solution) :=
  (torusVorticityEvolution solution).continuous

/-- Consequently the exact spatial sup-norm receiver varies continuously throughout the open
interior lifespan. -/
theorem continuous_norm_torusVorticityEvolution
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure) :
    Continuous (fun t : Ioo 0 T => ‖torusVorticityEvolution solution t‖) :=
  continuous_norm.comp (continuous_torusVorticityEvolution solution)

@[simp]
theorem torusVorticityEvolution_projection
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (x : Space) :
    torusVorticityEvolution solution t (euclideanToSpatialTorus x) =
      vorticityField velocity x t.1 := by
  apply isOnePeriodic_eq_of_euclideanToSpatialTorus_eq
    (fun y => vorticityField velocity y t.1)
    (openPeriodicSolutionOn_vorticityField_isOnePeriodic solution t.2)
  exact euclideanToSpatialTorus_representative _

/-- Exact `L∞ₓ` receiver characterization.  The torus continuous-map norm is bounded by `C` if
and only if every Euclidean presentation of the vorticity slice is bounded by `C`. -/
theorem norm_torusVorticityEvolution_le_iff
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (C : ℝ) :
    ‖torusVorticityEvolution solution t‖ ≤ C ↔
      ∀ x : Space, ‖vorticityField velocity x t.1‖ ≤ C := by
  rw [ContinuousMap.norm_le_of_nonempty]
  constructor
  · intro h x
    simpa using h (euclideanToSpatialTorus x)
  · intro h q
    obtain ⟨x, rfl⟩ := euclideanToSpatialTorus_surjective q
    simpa using h x

#print axioms piToSpatialTorus_isOpenQuotientMap
#print axioms isOnePeriodic_eq_of_euclideanToSpatialTorus_eq
#print axioms periodicTorusLift
#print axioms openPeriodicSolutionOn_vorticityField_contDiffOn_interior
#print axioms torusVorticityEvolution
#print axioms continuous_norm_torusVorticityEvolution
#print axioms norm_torusVorticityEvolution_le_iff

end Soma.Holonics.Millennium.NavierStokesTorusVorticity
