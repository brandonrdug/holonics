import ElementaryHolonics.Millennium.NavierStokesWeightedFourierReconstruction
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-!
# Smooth reconstruction of a finite native Fourier population

This owner closes the elementary finite-support case using the already constructed Euclidean
Fourier characters and finite sums.  It adds no Fourier engine and retains the common support
set for all three addressed components.
-/

noncomputable section

open Set
open scoped BigOperators ComplexConjugate

namespace Soma.Holonics.Millennium.NavierStokesFiniteFourierSmoothReconstruction

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesWeightedFourierReconstruction
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

/-- A single finite lattice aperture contains every nonzero native coefficient. -/
def NativeFiniteSupport (state : PeriodicVectorWeightedSobolev 3) : Prop :=
  ∃ support : Finset SpatialFrequency,
    ∀ (component : Fin 3) (k : SpatialFrequency),
      k ∉ support → nativeUnweightedComponent state component k = 0

/-- The finite complex Fourier synthesis associated with an addressed component. -/
def finiteNativeFourierSum
    (state : PeriodicVectorWeightedSobolev 3) (support : Finset SpatialFrequency)
    (component : Fin 3) (x : Space) : ℂ :=
  Finset.sum support (fun k ↦
    nativeUnweightedComponent state component k * euclideanFourierCharacter k x)

theorem contDiff_infty_euclideanFourierFactor
    (k : SpatialFrequency) (coordinate : Fin 3) :
    ContDiff ℝ ((↑(⊤ : ℕ∞)) : WithTop ℕ∞)
      (euclideanFourierFactor k coordinate) := by
  unfold euclideanFourierFactor
  rw [show (fun x : Space ↦ fourier (k coordinate)
      ((x coordinate : ℝ) : UnitAddCircle)) =
      (fun x : Space ↦ Complex.exp
        (2 * (Real.pi : ℂ) * Complex.I * (k coordinate : ℂ) *
          (x coordinate : ℂ))) by
    funext x
    rw [fourier_coe_apply]
    norm_num]
  have hcoordinate :
      ContDiff ℝ ((↑(⊤ : ℕ∞)) : WithTop ℕ∞)
        (fun x : Space ↦ x coordinate) := by
    simpa only [id_eq] using
      ((contDiff_piLp 2).mp (contDiff_id (𝕜 := ℝ)) coordinate)
  have hcoordinateComplex :
      ContDiff ℝ ((↑(⊤ : ℕ∞)) : WithTop ℕ∞)
        (fun x : Space ↦ (x coordinate : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hcoordinate
  have hexponent :
      ContDiff ℝ ((↑(⊤ : ℕ∞)) : WithTop ℕ∞)
        (fun x : Space ↦
          2 * (Real.pi : ℂ) * Complex.I * (k coordinate : ℂ) *
            (x coordinate : ℂ)) := by
    simpa only [mul_assoc] using
      (contDiff_const.mul hcoordinateComplex :
        ContDiff ℝ ((↑(⊤ : ℕ∞)) : WithTop ℕ∞)
          (fun x : Space ↦
            (2 * (Real.pi : ℂ) * Complex.I * (k coordinate : ℂ)) *
              (x coordinate : ℂ)))
  exact Complex.contDiff_exp.comp hexponent

theorem contDiff_infty_euclideanFourierCharacter
    (k : SpatialFrequency) :
    ContDiff ℝ ((↑(⊤ : ℕ∞)) : WithTop ℕ∞)
      (euclideanFourierCharacter k) := by
  unfold euclideanFourierCharacter
  apply contDiff_prod
  intro coordinate hcoordinate
  exact contDiff_infty_euclideanFourierFactor k coordinate

theorem contDiff_infty_finiteNativeFourierSum
    (state : PeriodicVectorWeightedSobolev 3) (support : Finset SpatialFrequency)
    (component : Fin 3) :
    ContDiff ℝ ((↑(⊤ : ℕ∞)) : WithTop ℕ∞)
      (finiteNativeFourierSum state support component) := by
  unfold finiteNativeFourierSum
  apply ContDiff.sum
  intro k hk
  exact (contDiff_const.mul (contDiff_infty_euclideanFourierCharacter k))

theorem tsum_euclideanNativeFourierPassage_eq_finiteNativeFourierSum
    (state : PeriodicVectorWeightedSobolev 3) (support : Finset SpatialFrequency)
    (component : Fin 3)
    (hsupport : ∀ (component : Fin 3) (k : SpatialFrequency),
      k ∉ support → nativeUnweightedComponent state component k = 0)
    (x : Space) :
    (∑' k : SpatialFrequency, euclideanNativeFourierPassage state component k x) =
      finiteNativeFourierSum state support component x := by
  unfold finiteNativeFourierSum
  rw [tsum_eq_sum (s := support)]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [euclideanNativeFourierPassage]
  · intro k hk
    rw [euclideanNativeFourierPassage, hsupport component k hk, zero_mul]

theorem reconstructedVelocity_component_eq_finiteNativeFourierSum
    (state : PeriodicVectorWeightedSobolev 3) (support : Finset SpatialFrequency)
    (component : Fin 3)
    (hsupport : ∀ (component : Fin 3) (k : SpatialFrequency),
      k ∉ support → nativeUnweightedComponent state component k = 0) :
    (fun x : Space ↦ reconstructedVelocity state x component) =
      (fun x : Space ↦ (finiteNativeFourierSum state support component x).re) := by
  funext x
  change (reconstructedTorusComplexComponent state component
      (euclideanToSpatialTorus x)).re = _
  rw [← tsum_euclideanNativeFourierPassage state component x,
    tsum_euclideanNativeFourierPassage_eq_finiteNativeFourierSum
      state support component hsupport x]

theorem contDiff_infty_reconstructedVelocity_component_of_nativeFiniteSupport
    (state : PeriodicVectorWeightedSobolev 3) (support : Finset SpatialFrequency)
    (component : Fin 3)
    (hsupport : ∀ (component : Fin 3) (k : SpatialFrequency),
      k ∉ support → nativeUnweightedComponent state component k = 0) :
    ContDiff ℝ ((↑(⊤ : ℕ∞)) : WithTop ℕ∞)
      (fun x : Space ↦ reconstructedVelocity state x component) := by
  rw [reconstructedVelocity_component_eq_finiteNativeFourierSum
    state support component hsupport]
  exact Complex.reCLM.contDiff.comp
    (contDiff_infty_finiteNativeFourierSum state support component)

theorem contDiff_infty_reconstructedVelocity_of_nativeFiniteSupport
    (state : PeriodicVectorWeightedSobolev 3) (hfinite : NativeFiniteSupport state) :
    ContDiff ℝ ((↑(⊤ : ℕ∞)) : WithTop ℕ∞)
      (reconstructedVelocity state) := by
  rcases hfinite with ⟨support, hsupport⟩
  rw [contDiff_piLp]
  intro component
  exact contDiff_infty_reconstructedVelocity_component_of_nativeFiniteSupport
    state support component hsupport

#print axioms contDiff_infty_reconstructedVelocity_of_nativeFiniteSupport

end Soma.Holonics.Millennium.NavierStokesFiniteFourierSmoothReconstruction
