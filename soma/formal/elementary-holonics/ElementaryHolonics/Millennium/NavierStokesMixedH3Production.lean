import ElementaryHolonics.Millennium.NavierStokesCubicPolarization
import ElementaryHolonics.Millennium.NavierStokesCoordinateH1Production

/-!
# The mixed third-order Navier--Stokes production face

The predecessor proves that seven diagonal affine-line strokes recover one symmetric mixed third
Frechet derivative.  This owner applies the same seven-face operation to the actual unforced
periodic momentum identity.  The time, Laplacian, and pressure populations are identified with
genuine mixed third spatial derivatives; the top transport and lower commutator populations are
retained separately under the same polarization.

The result covers arbitrary triples of spatial directions and therefore every one of the 27
ordered coordinate words of length three.  It is pointwise.  No spatial pairing, pressure
integration, viscous integration by parts, commutator-energy estimate, or complete `H³` production
inequality is claimed here.
-/

noncomputable section

open ContDiff Set
open scoped Laplacian

namespace Soma.Holonics.Millennium.NavierStokesMixedH3Production

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesFiniteTimeVorticity
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPeriodicEnergy
open Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy
open Soma.Holonics.Millennium.NavierStokesH3Production
open Soma.Holonics.Millennium.NavierStokesCoordinateH1Production
open Soma.Holonics.Millennium.NavierStokesCubicPolarization
open Soma.Holonics.Millennium.NavierStokesTorusFourier

/-- For a smooth scalar spatial field, polarizing its actual third affine-line derivatives
returns six copies of the genuine mixed third Frechet derivative. -/
theorem cubicFacePolarization_iteratedDeriv_three_affineLine
    {f : Space → ℝ} (hf : ContDiff ℝ ∞ f) (base a b c : Space) :
    cubicFacePolarization
        (fun direction ↦
          iteratedDeriv 3 (fun s : ℝ ↦ f (base + s • direction)) 0)
        a b c =
      6 * trilinearValue (thirdFDerivAt f base) a b c := by
  simpa using
    (mixedThirdFDeriv_eq_seven_affineLineStrokes hf base a b c).symm

/-! ## Polarizing the seven actual diagonal PDE returns -/

/-- The seven diagonal unforced production identities combine into one exact mixed-direction
identity before any smooth-field identification is made. -/
theorem openPeriodicSolutionOn_unforced_polarizedThirdDirectionalProductionIdentity
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T)
    (base a b c : Space) (component : Fin 3) :
    cubicFacePolarization
          (fun direction ↦ iteratedDeriv 3
            (eulerianTimeJetComponentLine velocity t base direction component) 0)
          a b c +
        cubicFacePolarization
          (fun direction ↦ thirdDirectionalTransportFace
            (fun y ↦ velocity y t) base direction component)
          a b c =
      nu * cubicFacePolarization
          (fun direction ↦ iteratedDeriv 3
            (laplacianComponentLine (fun y ↦ velocity y t) base direction component) 0)
          a b c -
        cubicFacePolarization
          (fun direction ↦ iteratedDeriv 3
            (pressureGradientComponentLine (fun y ↦ pressure y t)
              base direction component) 0)
          a b c -
        cubicFacePolarization
          (fun direction ↦ thirdDirectionalCommutatorRemainder
            (fun y ↦ velocity y t) base direction component)
          a b c := by
  have habc := openPeriodicSolutionOn_unforced_thirdDirectionalProductionIdentity
    solution ht base (a + b + c) component
  have hab := openPeriodicSolutionOn_unforced_thirdDirectionalProductionIdentity
    solution ht base (a + b) component
  have hac := openPeriodicSolutionOn_unforced_thirdDirectionalProductionIdentity
    solution ht base (a + c) component
  have hbc := openPeriodicSolutionOn_unforced_thirdDirectionalProductionIdentity
    solution ht base (b + c) component
  have ha := openPeriodicSolutionOn_unforced_thirdDirectionalProductionIdentity
    solution ht base a component
  have hb := openPeriodicSolutionOn_unforced_thirdDirectionalProductionIdentity
    solution ht base b component
  have hc := openPeriodicSolutionOn_unforced_thirdDirectionalProductionIdentity
    solution ht base c component
  unfold cubicFacePolarization
  linear_combination habc - hab - hac - hbc + ha + hb + hc

/-! ## The spatial time-jet is a genuine smooth scalar field -/

/-- At an interior time, one velocity component of the Eulerian time jet is spatially smooth.
The proof uses the actual unforced momentum equation and the already-founded smooth viscosity,
pressure, and advection fields. -/
theorem openPeriodicSolutionOn_unforced_eulerianTimeJetComponentSpatial_contDiff
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) (component : Fin 3) :
    ContDiff ℝ ∞ (fun y ↦ eulerianTimeJet velocity y t component) := by
  have htime : ContDiff ℝ ∞ (fun y ↦ eulerianTimeJet velocity y t) :=
    openPeriodicSolutionOn_eulerianTimeJetSlice_contDiff solution ht
  simpa [Function.comp_def] using
    (EuclideanSpace.proj component).contDiff.comp htime

/-! ## The actual mixed third-order PDE -/

/-- **Exact mixed third-order production identity for the actual unforced solution.**  Time,
viscosity, and pressure are genuine mixed third spatial derivatives.  The nonlinear population
retains the separately polarized top-transport and commutator faces. -/
theorem openPeriodicSolutionOn_unforced_mixedThirdProductionIdentity
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T)
    (base a b c : Space) (component : Fin 3) :
    6 * trilinearValue
          (thirdFDerivAt (fun y ↦ eulerianTimeJet velocity y t component) base)
          a b c +
        cubicFacePolarization
          (fun direction ↦ thirdDirectionalTransportFace
            (fun y ↦ velocity y t) base direction component)
          a b c =
      nu * (6 * trilinearValue
          (thirdFDerivAt (fun y ↦ (Δ (fun q ↦ velocity q t)) y component) base)
          a b c) -
        6 * trilinearValue
          (thirdFDerivAt (fun y ↦ gradient (fun q ↦ pressure q t) y component) base)
          a b c -
        cubicFacePolarization
          (fun direction ↦ thirdDirectionalCommutatorRemainder
            (fun y ↦ velocity y t) base direction component)
          a b c := by
  let u : InitialVelocity := fun y ↦ velocity y t
  let p : Space → ℝ := fun y ↦ pressure y t
  have hu : ContDiff ℝ ∞ u :=
    openPeriodicSolutionOn_velocitySlice_contDiff solution ht
  have hp : ContDiff ℝ ∞ p :=
    openPeriodicSolutionOn_pressureSlice_contDiff solution ht
  have htime : ContDiff ℝ ∞
      (fun y ↦ eulerianTimeJet velocity y t component) :=
    openPeriodicSolutionOn_unforced_eulerianTimeJetComponentSpatial_contDiff
      solution ht component
  have hviscousVector : ContDiff ℝ ∞ (Δ u) := laplacian_contDiff hu
  have hviscous : ContDiff ℝ ∞ (fun y ↦ (Δ u) y component) := by
    simpa [Function.comp_def] using
      (EuclideanSpace.proj component).contDiff.comp hviscousVector
  have hpressureVector : ContDiff ℝ ∞ (gradient p) := gradient_contDiff hp
  have hpressure : ContDiff ℝ ∞ (fun y ↦ gradient p y component) := by
    simpa [Function.comp_def] using
      (EuclideanSpace.proj component).contDiff.comp hpressureVector
  have hpolar :=
    openPeriodicSolutionOn_unforced_polarizedThirdDirectionalProductionIdentity
      solution ht base a b c component
  have htimePolar := cubicFacePolarization_iteratedDeriv_three_affineLine
    htime base a b c
  have hviscousPolar := cubicFacePolarization_iteratedDeriv_three_affineLine
    hviscous base a b c
  have hpressurePolar := cubicFacePolarization_iteratedDeriv_three_affineLine
    hpressure base a b c
  have htimePolar' :
      cubicFacePolarization
          (fun direction ↦ iteratedDeriv 3
            (eulerianTimeJetComponentLine velocity t base direction component) 0)
          a b c =
        6 * trilinearValue
          (thirdFDerivAt (fun y ↦ eulerianTimeJet velocity y t component) base)
          a b c := by
    simpa [eulerianTimeJetComponentLine, affineSpatialLine] using htimePolar
  have hviscousPolar' :
      cubicFacePolarization
          (fun direction ↦ iteratedDeriv 3
            (laplacianComponentLine (fun y ↦ velocity y t)
              base direction component) 0)
          a b c =
        6 * trilinearValue
          (thirdFDerivAt (fun y ↦ (Δ (fun q ↦ velocity q t)) y component) base)
          a b c := by
    simpa [laplacianComponentLine, affineSpatialLine, u] using hviscousPolar
  have hpressurePolar' :
      cubicFacePolarization
          (fun direction ↦ iteratedDeriv 3
            (pressureGradientComponentLine (fun y ↦ pressure y t)
              base direction component) 0)
          a b c =
        6 * trilinearValue
          (thirdFDerivAt
            (fun y ↦ gradient (fun q ↦ pressure q t) y component) base)
          a b c := by
    simpa [pressureGradientComponentLine, affineSpatialLine, p] using hpressurePolar
  rw [htimePolar', hviscousPolar', hpressurePolar'] at hpolar
  exact hpolar

/-- Every ordered coordinate triple is an instance of the mixed production identity. -/
theorem openPeriodicSolutionOn_unforced_thirdCoordinateWordProductionIdentity
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T)
    (base : Space) (i j k component : Fin 3) :
    6 * trilinearValue
          (thirdFDerivAt (fun y ↦ eulerianTimeJet velocity y t component) base)
          (spatialBasisVector i) (spatialBasisVector j) (spatialBasisVector k) +
        cubicFacePolarization
          (fun direction ↦ thirdDirectionalTransportFace
            (fun y ↦ velocity y t) base direction component)
          (spatialBasisVector i) (spatialBasisVector j) (spatialBasisVector k) =
      nu * (6 * trilinearValue
          (thirdFDerivAt (fun y ↦ (Δ (fun q ↦ velocity q t)) y component) base)
          (spatialBasisVector i) (spatialBasisVector j) (spatialBasisVector k)) -
        6 * trilinearValue
          (thirdFDerivAt (fun y ↦ gradient (fun q ↦ pressure q t) y component) base)
          (spatialBasisVector i) (spatialBasisVector j) (spatialBasisVector k) -
        cubicFacePolarization
          (fun direction ↦ thirdDirectionalCommutatorRemainder
            (fun y ↦ velocity y t) base direction component)
          (spatialBasisVector i) (spatialBasisVector j) (spatialBasisVector k) := by
  exact openPeriodicSolutionOn_unforced_mixedThirdProductionIdentity
    solution ht base (spatialBasisVector i) (spatialBasisVector j)
      (spatialBasisVector k) component

section Audit

#print axioms cubicFacePolarization_iteratedDeriv_three_affineLine
#print axioms openPeriodicSolutionOn_unforced_polarizedThirdDirectionalProductionIdentity
#print axioms openPeriodicSolutionOn_unforced_eulerianTimeJetComponentSpatial_contDiff
#print axioms openPeriodicSolutionOn_unforced_mixedThirdProductionIdentity
#print axioms openPeriodicSolutionOn_unforced_thirdCoordinateWordProductionIdentity

end Audit

end Soma.Holonics.Millennium.NavierStokesMixedH3Production
