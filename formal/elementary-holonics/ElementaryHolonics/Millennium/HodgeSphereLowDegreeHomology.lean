import ElementaryHolonics.Millennium.HodgeTwoSphereFundamentalCycle
import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
import Mathlib.Analysis.Normed.Module.Connected

noncomputable section

namespace Soma.Holonics.Millennium.HodgeSphereLowDegreeHomology

open CategoryTheory CategoryTheory.Limits
open AlgebraicTopology
open scoped Simplicial
open Soma.Holonics.Millennium.HodgeProjectiveLineSingularReduction
open Soma.Holonics.Millennium.HodgeTwoSphereFundamentalCycle

local instance : PathConnectedSpace HodgeTwoSphereFundamentalCycle.TwoSphere := by
  apply isPathConnected_iff_pathConnectedSpace.mp
  apply isPathConnected_sphere
  · rw [← Module.finrank_eq_rank ℝ (EuclideanSpace ℝ (Fin 3))]
    norm_num [finrank_euclideanSpace_fin]
  · norm_num

local instance : PathConnectedSpace sphereTopCat := by
  exact (inferInstance : PathConnectedSpace HodgeTwoSphereFundamentalCycle.TwoSphere)

abbrev SphereZeroHomology : ModuleCat ℚ :=
  RationalSingularHomology 0 sphereTopCat

/-- The augmentation identifies rational singular degree-zero homology of the sphere with one
coordinate line.  The path-connected instance is supplied by the normed-space sphere theorem. -/
def sphereH0EquivQ : SphereZeroHomology ≃ₗ[ℚ] ℚ :=
  (asIso (TopCat.singularHomology₀ε sphereTopCat rationalCoefficient)).toLinearEquiv

def sphereBasePoint : HodgeTwoSphereFundamentalCycle.TwoSphere :=
  radialFace 0 (Classical.arbitrary (stdSimplex ℝ (Fin 3)))

def spherePointSimplex : SphereSingularSimplex 0 :=
  (TopCat.toSSetObjEquiv sphereTopCat
    (Opposite.op (SimplexCategory.mk 0))).symm
      (ContinuousMap.const (stdSimplex ℝ (Fin 1)) sphereBasePoint)

def spherePointChainMorphism : rationalCoefficient ⟶ SphereSingularChainComplex.X 0 :=
  by
    change rationalCoefficient ⟶
      ((TopCat.toSSet.obj sphereTopCat).chainComplex rationalCoefficient).X 0
    exact (TopCat.toSSet.obj sphereTopCat).ιChainComplex spherePointSimplex

def spherePointCycle : SphereSingularChainComplex.cycles 0 :=
  SphereSingularChainComplex.liftCycles spherePointChainMorphism
    0 (by simp)
      (by
        rw [SphereSingularChainComplex.shape _ _ (by simp)]
        simp)
      (1 : ℚ)

def spherePointClass : SphereZeroHomology :=
  SphereSingularChainComplex.homologyπ 0 spherePointCycle

theorem sphereH0EquivQ_point : sphereH0EquivQ spherePointClass = 1 := by
  have h := SSet.liftCycles_ιChainComplex_homologyπ_homology₀ε
    (TopCat.toSSet.obj sphereTopCat) rationalCoefficient spherePointSimplex
  have h' := congrArg (fun f => f (1 : ℚ)) h
  change ((TopCat.toSSet.obj sphereTopCat).homology₀ε rationalCoefficient)
    (((TopCat.toSSet.obj sphereTopCat).chainComplex rationalCoefficient).homologyπ 0
      (((TopCat.toSSet.obj sphereTopCat).chainComplex rationalCoefficient).liftCycles
        ((TopCat.toSSet.obj sphereTopCat).ιChainComplex spherePointSimplex)
        0 (by simp) (by simp) (1 : ℚ))) = 1
  exact h'

theorem sphereH0_scalar_reconstruction (z : SphereZeroHomology) :
    z = sphereH0EquivQ z • spherePointClass := by
  apply (sphereH0EquivQ.injective)
  rw [map_smul, sphereH0EquivQ_point]
  simp

theorem sphereH0_scalar_reconstruction_exists (z : SphereZeroHomology) :
    ∃ c : ℚ, z = c • spherePointClass :=
  ⟨sphereH0EquivQ z, sphereH0_scalar_reconstruction z⟩

/- The path-connectedness input can also be retained at chain level: any two selected vertices
are joined by one actual singular edge, whose alternating boundary is their difference.  This is
stated in Mathlib's canonical singular-simplex chart; `TopCat.toSSetObjEquiv` transports it to the
continuous-map chart used by the surrounding sphere files. -/
theorem sphere_zero_chain_difference_is_boundary
    (xPoint yPoint : ↑sphereTopCat) :
    ∃ edge : SSet.Edge (TopCat.toSSetObj₀Equiv.symm xPoint)
        (TopCat.toSSetObj₀Equiv.symm yPoint),
      ModuleCat.Hom.hom
          ((TopCat.toSSet.obj sphereTopCat).ιChainComplex
            (R := rationalCoefficient) (TopCat.toSSetObj₀Equiv.symm yPoint)) (1 : ℚ) -
          ModuleCat.Hom.hom
            ((TopCat.toSSet.obj sphereTopCat).ιChainComplex
              (R := rationalCoefficient) (TopCat.toSSetObj₀Equiv.symm xPoint)) (1 : ℚ) =
        ((TopCat.toSSet.obj sphereTopCat).chainComplex rationalCoefficient).d 1 0
          (ModuleCat.Hom.hom
            ((TopCat.toSSet.obj sphereTopCat).ιChainComplex
              (R := rationalCoefficient) edge.edge) (1 : ℚ)) := by
  obtain ⟨path⟩ := PathConnectedSpace.joined xPoint yPoint
  let e : SSet.Edge (TopCat.toSSetObj₀Equiv.symm xPoint)
      (TopCat.toSSetObj₀Equiv.symm yPoint) :=
    (TopCat.toSSetObjEdgeEquiv (X := sphereTopCat)).symm
      ((TopCat.pathEquiv (X := sphereTopCat)).symm path)
  refine ⟨e, ?_⟩
  have h := congrArg (fun f => f (1 : ℚ))
    ((TopCat.toSSet.obj sphereTopCat).ιChainComplex_d
      (R := rationalCoefficient) e.edge)
  simp only [ModuleCat.hom_comp, ModuleCat.hom_sum, LinearMap.coe_sum,
    Finset.sum_apply, ModuleCat.hom_zsmul] at h
  simp [Fin.sum_univ_two] at h
  simpa only [CategoryTheory.comp_apply, sub_eq_add_neg] using h.symm

/-! Audit the returned constructors. -/
#print axioms sphereH0EquivQ
#print axioms sphereH0_scalar_reconstruction
#print axioms sphere_zero_chain_difference_is_boundary

end Soma.Holonics.Millennium.HodgeSphereLowDegreeHomology
