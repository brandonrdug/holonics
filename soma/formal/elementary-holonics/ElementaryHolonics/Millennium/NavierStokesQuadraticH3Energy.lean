import ElementaryHolonics.Millennium.NavierStokesH3Production
import Mathlib.Analysis.Analytic.IteratedFDeriv

/-!
# A coordinate--Frobenius quadratic H³ energy precursor

**[proved-derived]** The order-three operator-norm receiver is not a quadratic Hilbert-space
quantity.  This file therefore keeps the complete finite coordinate population instead: for each
order `0 ≤ n ≤ 3`, every ordered word `Fin n → Fin 3` is applied to the joint space--time
`n`-th Fréchet derivative through purely spatial directions, and the squared Euclidean norm of the
result is integrated over the periodic cube.  The ordered population has `1 + 3 + 9 + 27 = 40`
derivative words and retains all three velocity components.

**[conditional]** For an actual `OpenPeriodicSolutionOn`, every interior time occurrence supplies
joint smoothness on an open cylinder.  That regularity proves integrability of every square,
genuine differentiation of the complete finite sum under the spatial integral, periodicity of
each coordinate jet, and cancellation of its top incompressible transport work.

The final theorem also takes one diagonal order-three scalar face through the exact unforced
production identity in `NavierStokesH3Production`.  No estimate of the commutator population by
the complete quadratic energy is claimed here, and no pressure or viscous integration-by-parts
identity for every mixed word is asserted.
-/

noncomputable section

open ContDiff InnerProductSpace MeasureTheory Set
open scoped BigOperators Laplacian

namespace Soma.Holonics.Millennium.NavierStokesQuadraticH3Energy

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesFiniteTime
open Soma.Holonics.Millennium.NavierStokesFiniteTimeVorticity
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPeriodicEnergy
open Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy
open Soma.Holonics.Millennium.NavierStokesPeriodicFlux
open Soma.Holonics.Millennium.NavierStokesH3Production
open Soma.Holonics.Millennium.NavierStokesTorusFourier

/-! ## The complete finite coordinate population -/

/-- A spatial coordinate direction embedded into the joint space--time carrier. -/
def jointSpatialBasisDirection (i : Fin 3) : Space × ℝ :=
  (spatialBasisVector i, 0)

/-- The purely spatial directions addressed by an ordered coordinate word. -/
def coordinateWordDirections {n : ℕ} (word : Fin n → Fin 3) : Fin n → Space × ℝ :=
  fun k ↦ jointSpatialBasisDirection (word k)

/-- One full-vector coordinate jet, realized directly in the joint space--time derivative. -/
def coordinateJet
    (velocity : VelocityField) (n : ℕ) (word : Fin n → Fin 3)
    (x : Space) (t : ℝ) : Space :=
  iteratedFDeriv ℝ n (Function.uncurry velocity) (x, t) (coordinateWordDirections word)

/-- The coordinate jet as a time-dependent spatial field. -/
def coordinateJetField
    (velocity : VelocityField) (n : ℕ) (word : Fin n → Fin 3) : VelocityField :=
  fun x t ↦ coordinateJet velocity n word x t

/-- Half the squared Euclidean norm of one addressed coordinate jet. -/
def coordinateJetEnergyDensity
    (velocity : VelocityField) (n : ℕ) (word : Fin n → Fin 3)
    (x : Space) (t : ℝ) : ℝ :=
  kineticEnergyDensity (fun y ↦ coordinateJet velocity n word y t) x

/-- The full order-at-most-three coordinate--Frobenius density.  Ordered words retain every
coordinate tensor entry; symmetry is not used to collapse repeated mixed derivatives. -/
def coordinateH3EnergyDensity (velocity : VelocityField) (x : Space) (t : ℝ) : ℝ :=
  ∑ n : Fin 4, ∑ word : Fin (n : ℕ) → Fin 3,
    coordinateJetEnergyDensity velocity n word x t

/-- The corresponding finite quadratic energy, written as a sum of exact cube integrals. -/
def coordinateH3Energy (velocity : VelocityField) (t : ℝ) : ℝ :=
  ∑ n : Fin 4, ∑ word : Fin (n : ℕ) → Fin 3,
    periodicKineticEnergy (coordinateJetField velocity n word) t

/-- The genuine time-work population returned by differentiating the finite quadratic energy. -/
def coordinateH3TimeWork (velocity : VelocityField) (t : ℝ) : ℝ :=
  ∑ n : Fin 4, ∑ word : Fin (n : ℕ) → Fin 3,
    ∫ x in unitCube,
      inner ℝ
        (eulerianTimeJet (coordinateJetField velocity n word) x t)
        (coordinateJet velocity n word x t)

/-! ## Smoothness, integrability, positivity, and differentiation -/

/-- Every coordinate jet is jointly smooth on the genuine open interior cylinder. -/
theorem openPeriodicSolutionOn_coordinateJetField_contDiffOn
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (n : ℕ) (word : Fin n → Fin 3) :
    ContDiffOn ℝ ∞ (Function.uncurry (coordinateJetField velocity n word))
      (Soma.Holonics.Millennium.NavierStokesFiniteTimeVorticity.openSpaceTimeSlab T) := by
  let slab : Set (Space × ℝ) :=
    Soma.Holonics.Millennium.NavierStokesFiniteTimeVorticity.openSpaceTimeSlab T
  have hopen : IsOpen slab := by
    exact isOpen_univ.prod isOpen_Ioo
  have hvelocity : ContDiffOn ℝ ∞ (Function.uncurry velocity) slab := by
    apply solution.velocitySmooth.mono
    rintro ⟨x, t⟩ ⟨_hx, ht⟩
    exact ⟨Set.mem_univ x, ht.1.le, ht.2⟩
  intro z hz
  have hfield : ContDiffAt ℝ ∞ (Function.uncurry velocity) z :=
    hvelocity.contDiffAt (hopen.mem_nhds hz)
  have hjet : ContDiffAt ℝ ∞
      (iteratedFDeriv ℝ n (Function.uncurry velocity)) z :=
    contDiffAt_infty.mpr fun m ↦
      hfield.iteratedFDeriv_right (m := m) (by exact_mod_cast le_top)
  let evaluate :
      ((Space × ℝ) [×n]→L[ℝ] Space) →L[ℝ] Space :=
    ContinuousMultilinearMap.apply ℝ (fun _ : Fin n ↦ Space × ℝ) Space
      (coordinateWordDirections word)
  have hevaluate : ContDiffAt ℝ ∞
      (evaluate ∘ iteratedFDeriv ℝ n (Function.uncurry velocity)) z :=
    evaluate.contDiff.contDiffAt.comp z hjet
  have hfinal : ContDiffAt ℝ ∞
      (Function.uncurry (coordinateJetField velocity n word)) z := by
    have hfun : Function.uncurry (coordinateJetField velocity n word) =
        (fun z ↦ (iteratedFDeriv ℝ n (Function.uncurry velocity) z)
          (coordinateWordDirections word)) := by
      funext z
      rfl
    rw [hfun]
    exact hevaluate
  exact hfinal.contDiffWithinAt

/-- Every individual coordinate square is integrable on one periodic cube at an interior time. -/
theorem openPeriodicSolutionOn_coordinateJetEnergyDensity_integrable
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T)
    (n : ℕ) (word : Fin n → Fin 3) :
    IntegrableOn (fun x ↦ coordinateJetEnergyDensity velocity n word x t) unitCube := by
  have hfield := openPeriodicSolutionOn_coordinateJetField_contDiffOn solution n word
  have hslice : ContDiff ℝ ∞ (fun x ↦ coordinateJetField velocity n word x t) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    have hdomain :
        Soma.Holonics.Millennium.NavierStokesFiniteTimeVorticity.openSpaceTimeSlab T ∈
          nhds (x, t) :=
      prod_mem_nhds Filter.univ_mem (Ioo_mem_nhds ht.1 ht.2)
    have hjoint : ContDiffAt ℝ ∞
        (Function.uncurry (coordinateJetField velocity n word)) (x, t) :=
      hfield.contDiffAt hdomain
    simpa [Function.comp_def] using
      hjoint.comp x (contDiffAt_id.prodMk contDiffAt_const)
  have hcontinuous : Continuous
      (fun x ↦ coordinateJetEnergyDensity velocity n word x t) := by
    unfold coordinateJetEnergyDensity kineticEnergyDensity
    exact contDiff_const.mul (hslice.norm_sq ℝ) |>.continuous
  have hcubeCompact : IsCompact unitCube := by
    unfold unitCube
    exact (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr
      isCompact_Icc
  exact hcontinuous.continuousOn.integrableOn_compact hcubeCompact

/-- The complete finite coordinate density is integrable on every interior slice. -/
theorem openPeriodicSolutionOn_coordinateH3EnergyDensity_integrable
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    IntegrableOn (fun x ↦ coordinateH3EnergyDensity velocity x t) unitCube := by
  unfold coordinateH3EnergyDensity
  apply integrable_finset_sum Finset.univ
  intro n _hn
  apply integrable_finset_sum Finset.univ
  intro word _hword
  exact openPeriodicSolutionOn_coordinateJetEnergyDensity_integrable
    solution ht n word

/-- The sum-of-integrals energy is exactly the integral of the complete finite density. -/
theorem openPeriodicSolutionOn_coordinateH3Energy_eq_integral_density
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    coordinateH3Energy velocity t =
      ∫ x in unitCube, coordinateH3EnergyDensity velocity x t := by
  have hword : ∀ (n : Fin 4) (word : Fin (n : ℕ) → Fin 3),
      IntegrableOn (fun x ↦ coordinateJetEnergyDensity velocity n word x t) unitCube :=
    fun n word ↦ openPeriodicSolutionOn_coordinateJetEnergyDensity_integrable
      solution ht n word
  have hinner : ∀ n : Fin 4,
      IntegrableOn
        (fun x ↦ ∑ word : Fin (n : ℕ) → Fin 3,
          coordinateJetEnergyDensity velocity n word x t) unitCube := by
    intro n
    exact integrable_finset_sum Finset.univ (fun word _hword ↦ hword n word)
  unfold coordinateH3Energy coordinateH3EnergyDensity
  rw [integral_finset_sum Finset.univ (fun n _hn ↦ hinner n)]
  apply Finset.sum_congr rfl
  intro n _hn
  rw [integral_finset_sum Finset.univ (fun word _hword ↦ hword n word)]
  simp only [periodicKineticEnergy, coordinateJetEnergyDensity, coordinateJetField]

/-- Every coordinate--Frobenius energy occurrence is nonnegative. -/
theorem coordinateH3Energy_nonneg (velocity : VelocityField) (t : ℝ) :
    0 ≤ coordinateH3Energy velocity t := by
  unfold coordinateH3Energy periodicKineticEnergy kineticEnergyDensity
  apply Finset.sum_nonneg
  intro n _hn
  apply Finset.sum_nonneg
  intro word _hword
  apply integral_nonneg_of_ae
  filter_upwards with x
  positivity

/-- The complete coordinate--Frobenius energy has a genuine derivative on every interior time
occurrence.  The rate is constructed from the actual joint derivative and compact domination; it
is not an assumed continuation-rate function. -/
theorem openPeriodicSolutionOn_hasDerivAt_coordinateH3Energy
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    HasDerivAt (coordinateH3Energy velocity) (coordinateH3TimeWork velocity t) t := by
  have hword : ∀ (n : Fin 4) (word : Fin (n : ℕ) → Fin 3),
      HasDerivAt
        (periodicKineticEnergy (coordinateJetField velocity n word))
        (∫ x in unitCube,
          inner ℝ
            (eulerianTimeJet (coordinateJetField velocity n word) x t)
            (coordinateJet velocity n word x t)) t := by
    intro n word
    exact hasDerivAt_periodicKineticEnergy_eq_timeWork_of_contDiffOn_openSlab
      (coordinateJetField velocity n word)
      (openPeriodicSolutionOn_coordinateJetField_contDiffOn solution n word)
      ht.1 ht.2
  have hinner : ∀ n : Fin 4,
      HasDerivAt
        (fun τ ↦ ∑ word : Fin (n : ℕ) → Fin 3,
          periodicKineticEnergy (coordinateJetField velocity n word) τ)
        (∑ word : Fin (n : ℕ) → Fin 3,
          ∫ x in unitCube,
            inner ℝ
              (eulerianTimeJet (coordinateJetField velocity n word) x t)
              (coordinateJet velocity n word x t)) t := by
    intro n
    exact HasDerivAt.fun_sum fun word _hword ↦ hword n word
  have houter := HasDerivAt.fun_sum (u := Finset.univ)
    (fun n _hn ↦ hinner n)
  change HasDerivAt
    (fun τ ↦ ∑ n : Fin 4, ∑ word : Fin (n : ℕ) → Fin 3,
      periodicKineticEnergy (coordinateJetField velocity n word) τ)
    (∑ n : Fin 4, ∑ word : Fin (n : ℕ) → Fin 3,
      ∫ x in unitCube,
        inner ℝ
          (eulerianTimeJet (coordinateJetField velocity n word) x t)
          (coordinateJet velocity n word x t)) t
  exact houter

/-! ## Periodic top-transport cancellation -/

/-- At an interior solution time every joint coordinate jet returns across each spatial unit
face.  The proof differentiates the locally valid translated periodicity relation; no global
smooth extension outside the lifespan is used. -/
theorem openPeriodicSolutionOn_coordinateJet_isOnePeriodic
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T)
    (n : ℕ) (word : Fin n → Fin 3) :
    IsOnePeriodic (fun x ↦ coordinateJet velocity n word x t) := by
  intro x i
  let shift : Space × ℝ := (EuclideanSpace.single i 1, 0)
  let z : Space × ℝ := (x, t)
  let F : Space × ℝ → Space := Function.uncurry velocity
  have hperiodic : (fun q ↦ F (shift + q)) =ᶠ[nhds z] F := by
    filter_upwards [prod_mem_nhds Filter.univ_mem (Ioo_mem_nhds ht.1 ht.2)] with q hq
    change velocity (EuclideanSpace.single i 1 + q.1) (0 + q.2) = velocity q.1 q.2
    rw [zero_add, add_comm]
    exact solution.velocityPeriodic q.2 ⟨hq.2.1.le, hq.2.2⟩ q.1 i
  have hderivative := hperiodic.iteratedFDeriv ℝ n
  have hat := hderivative.self_of_nhds
  have hshift :
      iteratedFDeriv ℝ n (fun q : Space × ℝ ↦ F (shift + q)) z =
        iteratedFDeriv ℝ n F (shift + z) :=
    iteratedFDeriv_comp_add_left (𝕜 := ℝ) n shift z (f := F)
  have hmaps : shift + z = (x + EuclideanSpace.single i 1, t) := by
    ext <;> simp [shift, z, add_comm]
  change iteratedFDeriv ℝ n F (x + EuclideanSpace.single i 1, t)
      (coordinateWordDirections word) =
    iteratedFDeriv ℝ n F (x, t) (coordinateWordDirections word)
  rw [← hmaps, ← hshift]
  exact congrArg (fun L ↦ L (coordinateWordDirections word)) hat

/-- The top transport of every coordinate jet has zero net work on one periodic cube. -/
theorem openPeriodicSolutionOn_integral_coordinateJetTransport_eq_zero
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T)
    (n : ℕ) (word : Fin n → Fin 3) :
    ∫ x in unitCube,
      inner ℝ
        (fderiv ℝ (fun y ↦ coordinateJet velocity n word y t) x (velocity x t))
        (coordinateJet velocity n word x t) = 0 := by
  apply integral_transportWork_unitCube_eq_zero
  · exact (openPeriodicSolutionOn_velocitySlice_contDiff solution ht).of_le (by norm_num)
  · have hfield := openPeriodicSolutionOn_coordinateJetField_contDiffOn solution n word
    rw [contDiff_iff_contDiffAt]
    intro x
    have hdomain :
        Soma.Holonics.Millennium.NavierStokesFiniteTimeVorticity.openSpaceTimeSlab T ∈
          nhds (x, t) :=
      prod_mem_nhds Filter.univ_mem (Ioo_mem_nhds ht.1 ht.2)
    have hjoint : ContDiffAt ℝ ∞
        (Function.uncurry (coordinateJetField velocity n word)) (x, t) :=
      hfield.contDiffAt hdomain
    have hslice : ContDiffAt ℝ ∞
        (fun y ↦ coordinateJet velocity n word y t) x := by
      simpa [coordinateJetField, Function.comp_def] using
        hjoint.comp x (contDiffAt_id.prodMk contDiffAt_const)
    exact hslice.of_le (by norm_num)
  · exact solution.velocityPeriodic t ⟨ht.1.le, ht.2⟩
  · exact openPeriodicSolutionOn_coordinateJet_isOnePeriodic solution ht n word
  · exact fun x ↦ solution.incompressible x t ⟨ht.1.le, ht.2⟩

/-! ## One diagonal quadratic face of the exact unforced production identity -/

/-- The diagonal order-three scalar coefficient paired against the production law. -/
def diagonalThirdCoordinateCoefficient
    (velocity : VelocityField) (t : ℝ) (x direction : Space) (component : Fin 3) : ℝ :=
  iteratedDeriv 3
    (velocityComponentLine (fun y ↦ velocity y t) x direction component) 0

/-- Multiplying the exact third-directional PDE identity by its diagonal order-three coefficient
returns one honest quadratic production face.  This is still pointwise and directional: the
theorem does not claim the remaining commutator, viscosity, or pressure integrals are controlled
by `coordinateH3Energy`. -/
theorem openPeriodicSolutionOn_unforced_diagonalThirdCoordinateProductionPairing
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T)
    (x direction : Space) (component : Fin 3) :
    diagonalThirdCoordinateCoefficient velocity t x direction component *
          iteratedDeriv 3
            (eulerianTimeJetComponentLine velocity t x direction component) 0 +
        diagonalThirdCoordinateCoefficient velocity t x direction component *
          thirdDirectionalTransportFace (fun y ↦ velocity y t) x direction component =
      nu * diagonalThirdCoordinateCoefficient velocity t x direction component *
          iteratedDeriv 3
            (laplacianComponentLine (fun y ↦ velocity y t) x direction component) 0 -
        diagonalThirdCoordinateCoefficient velocity t x direction component *
          iteratedDeriv 3
            (pressureGradientComponentLine (fun y ↦ pressure y t) x direction component) 0 -
        diagonalThirdCoordinateCoefficient velocity t x direction component *
          thirdDirectionalCommutatorRemainder
            (fun y ↦ velocity y t) x direction component := by
  have hproduction :=
    openPeriodicSolutionOn_unforced_thirdDirectionalProductionIdentity
      solution ht x direction component
  calc
    diagonalThirdCoordinateCoefficient velocity t x direction component *
          iteratedDeriv 3
            (eulerianTimeJetComponentLine velocity t x direction component) 0 +
        diagonalThirdCoordinateCoefficient velocity t x direction component *
          thirdDirectionalTransportFace (fun y ↦ velocity y t) x direction component =
      diagonalThirdCoordinateCoefficient velocity t x direction component *
        (iteratedDeriv 3
            (eulerianTimeJetComponentLine velocity t x direction component) 0 +
          thirdDirectionalTransportFace (fun y ↦ velocity y t) x direction component) := by ring
    _ = diagonalThirdCoordinateCoefficient velocity t x direction component *
        (nu * iteratedDeriv 3
            (laplacianComponentLine (fun y ↦ velocity y t) x direction component) 0 -
          iteratedDeriv 3
            (pressureGradientComponentLine (fun y ↦ pressure y t) x direction component) 0 -
          thirdDirectionalCommutatorRemainder
            (fun y ↦ velocity y t) x direction component) := by rw [hproduction]
    _ = nu * diagonalThirdCoordinateCoefficient velocity t x direction component *
          iteratedDeriv 3
            (laplacianComponentLine (fun y ↦ velocity y t) x direction component) 0 -
        diagonalThirdCoordinateCoefficient velocity t x direction component *
          iteratedDeriv 3
            (pressureGradientComponentLine (fun y ↦ pressure y t) x direction component) 0 -
        diagonalThirdCoordinateCoefficient velocity t x direction component *
          thirdDirectionalCommutatorRemainder
            (fun y ↦ velocity y t) x direction component := by ring

section Audit

#print axioms openPeriodicSolutionOn_coordinateJetField_contDiffOn
#print axioms openPeriodicSolutionOn_coordinateH3EnergyDensity_integrable
#print axioms openPeriodicSolutionOn_hasDerivAt_coordinateH3Energy
#print axioms openPeriodicSolutionOn_coordinateJet_isOnePeriodic
#print axioms openPeriodicSolutionOn_integral_coordinateJetTransport_eq_zero
#print axioms openPeriodicSolutionOn_unforced_diagonalThirdCoordinateProductionPairing

end Audit

end Soma.Holonics.Millennium.NavierStokesQuadraticH3Energy
