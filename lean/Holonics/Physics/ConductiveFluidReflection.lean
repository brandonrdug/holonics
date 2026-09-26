import Holonics.Physics.FluidReceiverClosure

/-!
# Finite conductive-fluid reflection

This is a finite Galerkin algebraic composition.  It uses the actual projected
advective interaction and diagonal Stokes owner to construct the normalized finite
Galerkin MHD vector field. Continuum existence and lightning calibration retain their
separate source obligations.
-/

noncomputable section

open Holonics
open Holonics.Fluid.NavierStokesFiniteFourierHeat
open Holonics.Fluid.NavierStokesFiniteGalerkin
open Holonics.Fluid.NavierStokesTorusFourier
open Holonics.Fluid.NavierStokesFourierTriads
open Holonics.Fluid.NavierStokesMildFourierNonlinearity
open Holonics.Physics.FluidReceiverClosure

namespace Holonics.Physics.ConductiveFluidReflection

variable {carrier : Finset Holonics.Fluid.NavierStokesTorusFourier.SpatialFrequency}
  (aperture : Finset Holonics.Fluid.NavierStokesTorusFourier.SpatialFrequency)

abbrev State (carrier : Finset Holonics.Fluid.NavierStokesTorusFourier.SpatialFrequency) :=
  FiniteGalerkinState carrier

def B (carrier aperture : Finset Holonics.Fluid.NavierStokesTorusFourier.SpatialFrequency)
    (u v : State carrier) : State carrier :=
  finiteGalerkinProjectedInteraction carrier aperture u v

def S (carrier : Finset Holonics.Fluid.NavierStokesTorusFourier.SpatialFrequency)
    (nu : ℝ) (u : State carrier) : State carrier :=
  finiteGalerkinStokesPart nu u

theorem diffusion_plus (nu eta : ℝ) (u b : State carrier) :
    S carrier ((nu+eta)/2) (u+b) + S carrier ((nu-eta)/2) (u-b) =
      S carrier nu u + S carrier eta b := by
  funext output component
  simp [S, finiteGalerkinStokesPart, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem diffusion_minus (nu eta : ℝ) (u b : State carrier) :
    S carrier ((nu+eta)/2) (u-b) + S carrier ((nu-eta)/2) (u+b) =
      S carrier nu u - S carrier eta b := by
  funext output component
  simp [S, finiteGalerkinStokesPart, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

def Fu (carrier aperture : Finset Holonics.Fluid.NavierStokesTorusFourier.SpatialFrequency)
    (nu : ℝ) (u b : State carrier) : State carrier :=
  S carrier nu u - B carrier aperture u u + B carrier aperture b b

def Fb (carrier aperture : Finset Holonics.Fluid.NavierStokesTorusFourier.SpatialFrequency)
    (eta : ℝ) (u b : State carrier) : State carrier :=
  S carrier eta b - B carrier aperture u b + B carrier aperture b u

def zPlus (carrier : Finset Holonics.Fluid.NavierStokesTorusFourier.SpatialFrequency)
    (u b : State carrier) : State carrier := u + b
def zMinus (carrier : Finset Holonics.Fluid.NavierStokesTorusFourier.SpatialFrequency)
    (u b : State carrier) : State carrier := u - b

theorem elsasser_identity_plus (nu eta : ℝ) (u b : State carrier) :
    Fu carrier aperture nu u b + Fb carrier aperture eta u b =
      S carrier ((nu + eta) / 2) (zPlus carrier u b) +
        S carrier ((nu - eta) / 2) (zMinus carrier u b) -
          B carrier aperture (zMinus carrier u b) (zPlus carrier u b) := by
  simp only [Fu, Fb, zPlus, zMinus]
  rw [diffusion_plus]
  simp only [B, finiteGalerkinProjectedInteraction_sub_left, finiteGalerkinProjectedInteraction_add_right]
  abel

theorem elsasser_identity_minus (nu eta : ℝ) (u b : State carrier) :
    Fu carrier aperture nu u b - Fb carrier aperture eta u b =
      S carrier ((nu + eta) / 2) (zMinus carrier u b) +
        S carrier ((nu - eta) / 2) (zPlus carrier u b) -
          B carrier aperture (zPlus carrier u b) (zMinus carrier u b) := by
  simp only [Fu, Fb, zPlus, zMinus]
  rw [diffusion_minus]
  simp only [B, finiteGalerkinProjectedInteraction_add_left, finiteGalerkinProjectedInteraction_sub_right]
  abel

def complexImaginaryEvolution
    (carrier aperture : Finset Holonics.Fluid.NavierStokesTorusFourier.SpatialFrequency)
    (nu : ℝ) (u b : State carrier) : State carrier :=
  S carrier nu b - B carrier aperture u b - B carrier aperture b u

theorem complexImaginaryEvolution_differs_from_mhd (nu : ℝ) (u b : State carrier) :
    complexImaginaryEvolution carrier aperture nu u b - Fb carrier aperture nu u b =
      -2 • B carrier aperture b u := by
  simp only [complexImaginaryEvolution, Fb, sub_eq_add_neg]
  module

theorem complexRealProjection_retains_Bbb (nu : ℝ) (u b : State carrier) :
    (S carrier nu u - B carrier aperture u u + B carrier aperture b b) -
      (S carrier nu u - B carrier aperture u u) = B carrier aperture b b := by module

end Holonics.Physics.ConductiveFluidReflection
