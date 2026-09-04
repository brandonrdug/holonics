import ElementaryHolonics.Millennium.HodgeTetrahedralReduction

/-!
# Face-natural local carriers assemble into the tetrahedral reduction

This file states and proves the local-to-global law needed by the current Hodge residual.  A local
carrier assigns a finite tetrahedral chain to every addressed singular simplex in every degree.
The assignment is admissible only when the boundary of every carried simplex equals the complete
alternating population of its carried faces.  Because rational singular chains are the coproduct
of their addressed simplex generators, that one local law linearizes to a genuine global chain
map.

If the local carrier returns each of the four radial face simplices to its matching finite face
atom, the assembled chain map retracts the complete geometric realization in degree two.  The
existing reduction theorem then returns the normalized Hodge detector.  Thus the remaining source
construction is no longer an opaque linear map: it is a face-natural carrier on local occurrences
plus four exact normalization equations.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgeTetrahedralCarrierAssembly

open CategoryTheory CategoryTheory.Limits
open Soma.Holonics.Millennium.HodgeProjectiveLineSingularReduction
open Soma.Holonics.Millennium.HodgeTwoSphereFundamentalCycle
open Soma.Holonics.Millennium.HodgeTetrahedralSphereComplex
open Soma.Holonics.Millennium.HodgeTetrahedralChainComplex
open Soma.Holonics.Millennium.HodgeTetrahedralRealizationChainMap
open Soma.Holonics.Millennium.HodgeTetrahedralReduction

/-- One addressed finite face occurrence. -/
def faceUnit (face : Fin 4) : FaceChain :=
  fun observed => if observed = face then 1 else 0

@[simp]
theorem faceUnit_apply_self (face : Fin 4) : faceUnit face face = 1 := by
  simp [faceUnit]

/-- Multiplication by one carried generator, as a morphism out of the coefficient line. -/
def carriedCoefficient {degree : ℕ}
    (value : tetrahedralChainComplex.X degree) :
    rationalCoefficient ⟶ tetrahedralChainComplex.X degree :=
  ModuleCat.ofHom
    { toFun := fun coefficient => coefficient • value
      map_add' := fun left right => add_smul left right value
      map_smul' := by
        intro scalar coefficient
        rw [RingHom.id_apply]
        exact (smul_smul scalar coefficient value).symm }

@[simp]
theorem carriedCoefficient_apply {degree : ℕ}
    (value : tetrahedralChainComplex.X degree) (coefficient : ℚ) :
    carriedCoefficient value coefficient = coefficient • value := rfl

theorem sigmaInjection_eq_smul_simplexGenerator (degree : ℕ)
    (simplex : SphereSingularSimplex degree) (coefficient : ℚ) :
    (Sigma.ι (fun _ : SphereSingularSimplex degree => rationalCoefficient) simplex) coefficient =
      coefficient • simplexGenerator simplex := by
  let one : (rationalCoefficient : Type) := (1 : ℚ)
  let coefficientPoint : (rationalCoefficient : Type) := coefficient
  have hone : coefficient • one = coefficientPoint := by
    change coefficient * 1 = coefficient
    exact mul_one coefficient
  have hlinear := map_smul
    (Sigma.ι (fun _ : SphereSingularSimplex degree => rationalCoefficient) simplex).hom
    coefficient one
  change (Sigma.ι (fun _ : SphereSingularSimplex degree => rationalCoefficient) simplex)
      coefficientPoint = coefficient •
        (Sigma.ι (fun _ : SphereSingularSimplex degree => rationalCoefficient) simplex) one
  rw [← hone]
  exact hlinear

/-- The coproduct-linear extension of an addressed simplex carrier. -/
abbrev linearizeCarrier (degree : ℕ)
    (carry : SphereSingularSimplex degree → tetrahedralChainComplex.X degree) :
    SphereSingularChainComplex.X degree ⟶ tetrahedralChainComplex.X degree :=
  Sigma.desc fun simplex => carriedCoefficient (carry simplex)

@[simp]
theorem linearizeCarrier_simplexGenerator (degree : ℕ)
    (carry : SphereSingularSimplex degree → tetrahedralChainComplex.X degree)
    (simplex : SphereSingularSimplex degree) :
    linearizeCarrier degree carry (simplexGenerator simplex) = carry simplex := by
  change ((Sigma.ι (fun _ : SphereSingularSimplex degree => rationalCoefficient) simplex ≫
      Sigma.desc (fun simplex => carriedCoefficient (carry simplex))) (1 : ℚ)) = carry simplex
  rw [Sigma.ι_desc]
  change (1 : ℚ) • carry simplex = carry simplex
  exact one_smul ℚ (carry simplex)

/-- The exact local seam law.  It compares the finite boundary of one carried occurrence with the
complete alternating population of the carried source faces. -/
structure FaceNaturalCarrier where
  carry : (degree : ℕ) → SphereSingularSimplex degree →
    tetrahedralChainComplex.X degree
  boundary : ∀ (degree : ℕ) (simplex : SphereSingularSimplex (degree + 1)),
    tetrahedralChainComplex.d (degree + 1) degree (carry (degree + 1) simplex) =
      ∑ face : Fin (degree + 2), (-1 : ℚ) ^ (face : ℕ) •
        carry degree (simplexFace face simplex)

namespace FaceNaturalCarrier

/-- The local face law extends to the whole rational singular-chain population. -/
theorem linearize_comm (carrier : FaceNaturalCarrier) (degree : ℕ) :
    linearizeCarrier (degree + 1) (carrier.carry (degree + 1)) ≫
        tetrahedralChainComplex.d (degree + 1) degree =
      SphereSingularChainComplex.d (degree + 1) degree ≫
        linearizeCarrier degree (carrier.carry degree) := by
  apply Sigma.hom_ext
  intro simplex
  change Sigma.ι (fun _ : SphereSingularSimplex (degree + 1) => rationalCoefficient) simplex ≫
        (Sigma.desc (fun source => carriedCoefficient (carrier.carry (degree + 1) source)) ≫
          tetrahedralChainComplex.d (degree + 1) degree) =
      Sigma.ι (fun _ : SphereSingularSimplex (degree + 1) => rationalCoefficient) simplex ≫
        (SphereSingularChainComplex.d (degree + 1) degree ≫
          Sigma.desc (fun source => carriedCoefficient (carrier.carry degree source)))
  rw [← Category.assoc, Sigma.ι_desc]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro coefficient
  simp only [ConcreteCategory.comp_apply]
  change tetrahedralChainComplex.d (degree + 1) degree
      (carriedCoefficient (carrier.carry (degree + 1) simplex) coefficient) =
    linearizeCarrier degree (carrier.carry degree)
      (SphereSingularChainComplex.d (degree + 1) degree
        ((Sigma.ι (fun _ : SphereSingularSimplex (degree + 1) => rationalCoefficient)
          simplex) coefficient))
  let q : ℚ := coefficient
  have hcarry :
      carriedCoefficient (carrier.carry (degree + 1) simplex) coefficient =
        q • carrier.carry (degree + 1) simplex := rfl
  have hsigma :
      (Sigma.ι (fun _ : SphereSingularSimplex (degree + 1) => rationalCoefficient)
        simplex) coefficient = q • simplexGenerator simplex := by
    exact sigmaInjection_eq_smul_simplexGenerator (degree + 1) simplex q
  rw [hcarry, hsigma]
  rw [map_smul, map_smul, boundary_simplexGenerator]
  rw [map_smul]
  rw [map_sum]
  simp only [map_smul]
  rw [carrier.boundary]
  congr 1
  apply Finset.sum_congr rfl
  intro face _
  rw [linearizeCarrier_simplexGenerator]

/-- Every face-natural local carrier assembles to one genuine global reduction chain map. -/
def chainMap (carrier : FaceNaturalCarrier) :
    SphereSingularChainComplex ⟶ tetrahedralChainComplex where
  f degree := linearizeCarrier degree (carrier.carry degree)
  comm' := by
    intro sourceDegree targetDegree related
    change targetDegree + 1 = sourceDegree at related
    subst sourceDegree
    exact carrier.linearize_comm targetDegree

/-- Returning the four radial singular faces to their addressed finite atoms is exactly the local
normalization required at the Hodge source. -/
def NormalizedOnRadialFaces (carrier : FaceNaturalCarrier) : Prop :=
  ∀ face : Fin 4, carrier.carry 2 (radialSingularSimplex face) = faceUnit face

/-- The four local normalization equations extend to the full degree-two retraction square. -/
theorem realization_retract (carrier : FaceNaturalCarrier)
    (normalized : carrier.NormalizedOnRadialFaces) :
    HodgeSphereFundamentalDetector.faceRealizationMorphism ≫ carrier.chainMap.f 2 =
      𝟙 HodgeSphereFundamentalDetector.TetrahedralFaceModule := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro chain
  funext face
  change linearizeCarrier 2 (carrier.carry 2)
      (∑ radialFace : Fin 4,
        chain radialFace • simplexGenerator (radialSingularSimplex radialFace)) face = chain face
  rw [map_sum]
  simp only [map_smul]
  have hterm (radialFace : Fin 4) :
      linearizeCarrier 2 (carrier.carry 2)
          (simplexGenerator (radialSingularSimplex radialFace)) =
        carrier.carry 2 (radialSingularSimplex radialFace) :=
    linearizeCarrier_simplexGenerator 2 (carrier.carry 2) _
  simp_rw [hterm]
  change ∀ radialFace : Fin 4,
    carrier.carry 2 (radialSingularSimplex radialFace) = faceUnit radialFace at normalized
  simp_rw [normalized]
  rw [Fin.sum_univ_four]
  change
    chain 0 * (if face = 0 then 1 else 0) +
      chain 1 * (if face = 1 then 1 else 0) +
      chain 2 * (if face = 2 then 1 else 0) +
      chain 3 * (if face = 3 then 1 else 0) = chain face
  fin_cases face <;> simp [Fin.ext_iff]

/-- A face-natural carrier with the four exact radial returns constructs the normalized detector. -/
def degreeTwoReceiver (carrier : FaceNaturalCarrier)
    (normalized : carrier.NormalizedOnRadialFaces) :
    HodgeSphereFundamentalDetector.TetrahedralDegreeTwoReceiver :=
  degreeTwoReceiverOfReduction carrier.chainMap (carrier.realization_retract normalized)

end FaceNaturalCarrier

section Audit

#print axioms faceUnit_apply_self
#print axioms sigmaInjection_eq_smul_simplexGenerator
#print axioms linearizeCarrier_simplexGenerator
#print axioms FaceNaturalCarrier.linearize_comm
#print axioms FaceNaturalCarrier.chainMap
#print axioms FaceNaturalCarrier.realization_retract
#print axioms FaceNaturalCarrier.degreeTwoReceiver

end Audit

end Soma.Holonics.Millennium.HodgeTetrahedralCarrierAssembly
