import Holonics.Physics.ReceiverStressEnergy
import Holonics.Physics.ObserverBoundaryCurrent.Field
import Holonics.Transport.ChangingReceiver

/-!
# Observer-current charge on a regular slab

The stress field uses `ReceiverStressEnergy.Tensor`; both derivatives of the
participating covector survive in the force/deformation source. Actual product
and integral derivatives give a constant-time regular 1+1 balance, per declared
transverse area.

The covector field `u` is arbitrary in this theorem. A physical observer requires
a declared Lorentz metric and a future unit timelike vector `U` with `u = g U`.
The charge is mixed slice-normal/observer energy only with those identifications;
it is comoving energy when `U` aligns with the future unit slice normal. Energy
positivity requires a stress-energy condition (weak energy for the aligned
reading; dominant energy or an explicit mixed positivity condition otherwise).
These are consumer obligations. This balance asserts no constituted source
realization, positivity, mass shell, Lorentz covariance or singular boundary trace.
Refs #62 / #146.
-/

noncomputable section
namespace Holonics.Physics.ObserverBoundaryCurrent
open MeasureTheory Filter Set
open scoped Topology Interval
open Holonics.Physics.ReceiverStressEnergy
open Holonics.Transport.ChangingReceiver

/-- A participating observer covector reads the actual stress field. -/
def observerCurrent (T : ℝ → ℝ → Tensor) (u : ℝ → ℝ → Index → ℝ)
    (μ : Index) (t x : ℝ) : ℝ := -∑ ν, T t x μ ν * u t x ν

def timeRate (T dtT : ℝ → ℝ → Tensor) (u dtU : ℝ → ℝ → Index → ℝ)
    (t x : ℝ) : ℝ := -(∑ ν, (dtT t x 0 ν * u t x ν + T t x 0 ν * dtU t x ν))

def fluxRate (T dxT : ℝ → ℝ → Tensor) (u dxU : ℝ → ℝ → Index → ℝ)
    (t x : ℝ) : ℝ := -(∑ ν, (dxT t x 1 ν * u t x ν + T t x 1 ν * dxU t x ν))

def observerSource (T : ℝ → ℝ → Tensor) (u dtU dxU : ℝ → ℝ → Index → ℝ)
    (force : ℝ → Index → ℝ) (t x : ℝ) : ℝ :=
  -(∑ ν, (force x ν * u t x ν + T t x 0 ν * dtU t x ν + T t x 1 ν * dxU t x ν))

/-- The product derivative is proved for the field, rather than supplied as an
array. This is the time derivative of the actual observer density. -/
theorem observer_density_derivative
    (T dtT : ℝ → ℝ → Tensor) (u dtU : ℝ → ℝ → Index → ℝ) (t x : ℝ)
    (hT : ∀ ν, HasDerivAt (fun z => T z x 0 ν) (dtT t x 0 ν) t)
    (hU : ∀ ν, HasDerivAt (fun z => u z x ν) (dtU t x ν) t) :
    HasDerivAt (fun z => observerCurrent T u 0 z x) (timeRate T dtT u dtU t x) t := by
  simpa only [observerCurrent, timeRate] using
    field_contraction_hasDerivAt (fun s ν => T s x 0 ν) (fun s ν => u s x ν)
      (dtT t x 0) (dtU t x) t hT hU

theorem observer_flux_derivative
    (T dxT : ℝ → ℝ → Tensor) (u dxU : ℝ → ℝ → Index → ℝ) (t x : ℝ)
    (hT : ∀ ν, HasDerivAt (fun z => T t z 1 ν) (dxT t x 1 ν) x)
    (hU : ∀ ν, HasDerivAt (fun z => u t z ν) (dxU t x ν) x) :
    HasDerivAt (fun z => observerCurrent T u 1 t z) (fluxRate T dxT u dxU t x) x := by
  simpa only [observerCurrent, fluxRate] using
    field_contraction_hasDerivAt (fun z ν => T t z 1 ν) (fun z ν => u t z ν)
      (dxT t x 1) (dxU t x) x hT hU

/-- Complete force and observer-deformation terms on the 1+1 reduction. -/
theorem observer_local_balance
    (T dtT dxT : ℝ → ℝ → Tensor) (u dtU dxU : ℝ → ℝ → Index → ℝ)
    (force : ℝ → Index → ℝ) (t x : ℝ)
    (hforce : ∀ ν, dtT t x 0 ν + dxT t x 1 ν = force x ν) :
    timeRate T dtT u dtU t x + fluxRate T dxT u dxU t x =
      observerSource T u dtU dxU force t x := by
  exact field_contraction_force_balance (T t x 0) (T t x 1)
    (dtT t x 0) (dxT t x 1) (u t x) (dtU t x) (dxU t x) (force x) hforce

/-- Actual observer-current integral balance with its force, boundary and
observer-deformation terms. The caller supplies no integral rate or product
current derivative. A timelike unit covector is needed only for an energy reading. -/
theorem slab_observer_balance
    (T dtT dxT : ℝ → ℝ → Tensor) (u dtU dxU : ℝ → ℝ → Index → ℝ)
    (force : ℝ → Index → ℝ)
    {t l r : ℝ} {S : Set ℝ} {bound : ℝ → ℝ}
    (_hlr : l < r) (hS : S ∈ 𝓝 t)
    (hdt : ∀ s ∈ S, ∀ x ∈ uIcc l r, ∀ ν,
      HasDerivAt (fun z => T z x 0 ν) (dtT s x 0 ν) s)
    (hdtU : ∀ s ∈ S, ∀ x ∈ uIcc l r, ∀ ν,
      HasDerivAt (fun z => u z x ν) (dtU s x ν) s)
    (hdx : ∀ x ∈ uIcc l r, ∀ ν,
      HasDerivAt (fun z => T t z 1 ν) (dxT t x 1 ν) x)
    (hdxU : ∀ x ∈ uIcc l r, ∀ ν,
      HasDerivAt (fun z => u t z ν) (dxU t x ν) x)
    (hforce : ∀ x ∈ uIcc l r, ∀ ν,
      dtT t x 0 ν + dxT t x 1 ν = force x ν)
    (hFmeas : ∀ᶠ s in 𝓝 t, AEStronglyMeasurable
      (observerCurrent T u 0 s) (volume.restrict (Ι l r)))
    (hFint : IntervalIntegrable (observerCurrent T u 0 t) volume l r)
    (hdFmeas : AEStronglyMeasurable (timeRate T dtT u dtU t) (volume.restrict (Ι l r)))
    (hbound : ∀ᵐ x ∂volume, x ∈ Ι l r → ∀ s ∈ S,
      ‖timeRate T dtT u dtU s x‖ ≤ bound x)
    (hboundint : IntervalIntegrable bound volume l r)
    (hfluxint : IntervalIntegrable (fluxRate T dxT u dxU t) volume l r) :
    HasDerivAt (fun s => ∫ x in l..r, observerCurrent T u 0 s x)
      ((∫ x in l..r, observerSource T u dtU dxU force t x) -
        (observerCurrent T u 1 t r - observerCurrent T u 1 t l)) t := by
  have hp : ∀ᵐ x ∂volume, x ∈ Ι l r → ∀ s ∈ S,
      HasDerivAt (fun z => observerCurrent T u 0 z x) (timeRate T dtT u dtU s x) s := by
    filter_upwards [] with x
    intro hx s hs
    exact observer_density_derivative T dtT u dtU s x
      (hdt s hs x (uIoc_subset_uIcc hx)) (hdtU s hs x (uIoc_subset_uIcc hx))
  exact integral_balance_of_local_derivatives hS hFmeas hFint hdFmeas hbound hboundint hp
    (fun x hx => observer_flux_derivative T dxT u dxU t x (hdx x hx) (hdxU x hx))
    hfluxint (fun x hx => observer_local_balance T dtT dxT u dtU dxU force t x (hforce x hx))


end Holonics.Physics.ObserverBoundaryCurrent
