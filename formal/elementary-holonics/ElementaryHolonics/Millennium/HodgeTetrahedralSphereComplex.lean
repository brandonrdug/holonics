import ElementaryHolonics.Millennium.HodgeTwoSphereFundamentalCycle

/-!
# The finite tetrahedral sphere complex and its singular realization

This file constructs the finite source of the explicit sphere cycle.  The four oriented faces and
six oriented edges form a rational boundary map.  Its top kernel is computed, not assumed: every
cycle is a unique multiple of the alternating tetrahedral boundary, so top homology is `ℚ` and
the fundamental class is nonzero.

The finite faces and edges are then realized by the continuous radial singular simplices from
`HodgeTwoSphereFundamentalCycle`.  The realization square commutes with the boundary exactly.  The
induced categorical map into genuine rational singular homology isolates the next theorem: prove
that this geometric realization does not kill the already nonzero finite fundamental class.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgeTetrahedralSphereComplex

open CategoryTheory
open Soma.Holonics.Millennium.HodgeTwoSphereFundamentalCycle

inductive TetraEdge
  | e01 | e02 | e03 | e12 | e13 | e23
  deriving DecidableEq

instance : Fintype TetraEdge :=
  Fintype.ofList [.e01, .e02, .e03, .e12, .e13, .e23] (by
    intro edge
    cases edge <;> simp)

abbrev FaceChain := Fin 4 → ℚ
abbrev EdgeChain := TetraEdge → ℚ

def boundaryColumn : TetraEdge → FaceChain
  | .e01 => ![0, 0, 1, 1]
  | .e02 => ![0, 1, 0, -1]
  | .e03 => ![0, -1, -1, 0]
  | .e12 => ![1, 0, 0, 1]
  | .e13 => ![-1, 0, 1, 0]
  | .e23 => ![1, 1, 0, 0]

def faceBoundary : FaceChain →ₗ[ℚ] EdgeChain where
  toFun chain edge := ∑ face, chain face * boundaryColumn edge face
  map_add' x y := by
    funext edge
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' q x := by
    funext edge
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc, Finset.mul_sum]

@[simp]
theorem faceBoundary_apply (chain : FaceChain) (edge : TetraEdge) :
    faceBoundary chain edge = ∑ face, chain face * boundaryColumn edge face := rfl

def fundamentalFaceChain : FaceChain :=
  fun face => (-1 : ℚ) ^ (face : ℕ)

theorem fundamentalFaceChain_boundary_zero :
    faceBoundary fundamentalFaceChain = 0 := by
  funext edge
  cases edge <;>
    simp [faceBoundary, boundaryColumn, fundamentalFaceChain, Fin.sum_univ_four] <;>
    norm_num

abbrev TetrahedralH2 := LinearMap.ker faceBoundary

def fundamentalClass : TetrahedralH2 :=
  ⟨fundamentalFaceChain, fundamentalFaceChain_boundary_zero⟩

theorem cycle_coordinates (cycle : FaceChain) (hcycle : faceBoundary cycle = 0) :
    cycle = cycle 0 • fundamentalFaceChain := by
  have hedge23 := congrFun hcycle TetraEdge.e23
  have hedge13 := congrFun hcycle TetraEdge.e13
  have hedge12 := congrFun hcycle TetraEdge.e12
  simp [faceBoundary, boundaryColumn, Fin.sum_univ_four] at hedge23 hedge13 hedge12
  funext face
  fin_cases face
  · simp [fundamentalFaceChain]
  · simp [fundamentalFaceChain]
    linarith
  · simp [fundamentalFaceChain]
    linarith
  · simp [fundamentalFaceChain]
    linarith

def tetrahedralH2EquivQ : TetrahedralH2 ≃ₗ[ℚ] ℚ where
  toFun cycle := cycle.1 0
  invFun coefficient := coefficient • fundamentalClass
  left_inv cycle := by
    apply Subtype.ext
    exact (cycle_coordinates cycle.1 cycle.2).symm
  right_inv coefficient := by
    simp [fundamentalClass, fundamentalFaceChain]
  map_add' x y := rfl
  map_smul' q x := rfl

theorem fundamentalClass_ne_zero : fundamentalClass ≠ 0 := by
  intro hzero
  have := congrArg (fun cycle : TetrahedralH2 => cycle.1 0) hzero
  norm_num [fundamentalClass, fundamentalFaceChain] at this

def edgeSimplex : TetraEdge → SphereSingularSimplex 1
  | .e23 => simplexFace 0 (radialSingularSimplex 0)
  | .e13 => simplexFace 1 (radialSingularSimplex 0)
  | .e12 => simplexFace 2 (radialSingularSimplex 0)
  | .e03 => simplexFace 1 (radialSingularSimplex 1)
  | .e02 => simplexFace 2 (radialSingularSimplex 1)
  | .e01 => simplexFace 2 (radialSingularSimplex 2)

def faceRealization : FaceChain →ₗ[ℚ] SphereChain 2 where
  toFun chain := ∑ face, chain face • simplexGenerator (radialSingularSimplex face)
  map_add' x y := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' q x := by
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro face _
    simp only [Pi.smul_apply, RingHom.id_apply, smul_smul, smul_eq_mul]

def edgeRealization : EdgeChain →ₗ[ℚ] SphereChain 1 where
  toFun chain :=
    chain .e01 • simplexGenerator (edgeSimplex .e01) +
    chain .e02 • simplexGenerator (edgeSimplex .e02) +
    chain .e03 • simplexGenerator (edgeSimplex .e03) +
    chain .e12 • simplexGenerator (edgeSimplex .e12) +
    chain .e13 • simplexGenerator (edgeSimplex .e13) +
    chain .e23 • simplexGenerator (edgeSimplex .e23)
  map_add' x y := by
    simp only [Pi.add_apply, add_smul]
    abel
  map_smul' q x := by
    simp only [Pi.smul_apply, RingHom.id_apply, smul_add, smul_smul, smul_eq_mul]

theorem faceRealization_fundamental :
    faceRealization fundamentalFaceChain = sphereFundamentalCandidate := rfl

theorem faceRealization_boundary (chain : FaceChain) :
    SphereSingularChainComplex.d 2 1 (faceRealization chain) =
      edgeRealization (faceBoundary chain) := by
  change SphereSingularChainComplex.d 2 1
      (∑ face : Fin 4, chain face • simplexGenerator (radialSingularSimplex face)) =
    edgeRealization (faceBoundary chain)
  rw [map_sum]
  simp_rw [map_smul, boundary_radialSingularSimplex]
  rw [Fin.sum_univ_four]
  change _ =
    faceBoundary chain .e01 • simplexGenerator (edgeSimplex .e01) +
    faceBoundary chain .e02 • simplexGenerator (edgeSimplex .e02) +
    faceBoundary chain .e03 • simplexGenerator (edgeSimplex .e03) +
    faceBoundary chain .e12 • simplexGenerator (edgeSimplex .e12) +
    faceBoundary chain .e13 • simplexGenerator (edgeSimplex .e13) +
    faceBoundary chain .e23 • simplexGenerator (edgeSimplex .e23)
  simp [faceBoundary_apply, Fin.sum_univ_four, boundaryColumn, edgeSimplex]
  simp only [← radialSingularSimplex_edge_23, ← radialSingularSimplex_edge_13,
    ← radialSingularSimplex_edge_12, ← radialSingularSimplex_edge_03,
    ← radialSingularSimplex_edge_02, ← radialSingularSimplex_edge_01]
  module

def tetrahedralH2Module : ModuleCat ℚ := ModuleCat.of ℚ TetrahedralH2

def tetrahedralCycleMorphism :
    tetrahedralH2Module ⟶ SphereSingularChainComplex.X 2 :=
  ModuleCat.ofHom (faceRealization.comp (Submodule.subtype (LinearMap.ker faceBoundary)))

theorem tetrahedralCycleMorphism_comp_boundary_zero :
    tetrahedralCycleMorphism ≫ SphereSingularChainComplex.d 2 1 = 0 := by
  ext cycle
  change SphereSingularChainComplex.d 2 1 (faceRealization cycle.1) = 0
  rw [faceRealization_boundary, cycle.2, map_zero]

def tetrahedralCycleLift :
    tetrahedralH2Module ⟶ SphereSingularChainComplex.cycles 2 :=
  SphereSingularChainComplex.liftCycles tetrahedralCycleMorphism 1 (by simp)
    tetrahedralCycleMorphism_comp_boundary_zero

theorem tetrahedralCycleLift_i :
    tetrahedralCycleLift ≫ SphereSingularChainComplex.iCycles 2 =
      tetrahedralCycleMorphism := by
  apply HomologicalComplex.liftCycles_i

def tetrahedralHomologyRealization :
    tetrahedralH2Module ⟶ SphereSingularChainComplex.homology 2 :=
  tetrahedralCycleLift ≫ SphereSingularChainComplex.homologyπ 2

def realizedFundamentalClass : SphereSingularChainComplex.homology 2 :=
  tetrahedralHomologyRealization fundamentalClass

theorem tetrahedralCycleMorphism_fundamental :
    tetrahedralCycleMorphism fundamentalClass = sphereFundamentalCandidate := by
  exact faceRealization_fundamental

section Audit

#print axioms tetrahedralH2EquivQ
#print axioms fundamentalClass_ne_zero
#print axioms faceRealization_boundary
#print axioms tetrahedralCycleMorphism_comp_boundary_zero
#print axioms tetrahedralCycleMorphism_fundamental

end Audit

end Soma.Holonics.Millennium.HodgeTetrahedralSphereComplex
