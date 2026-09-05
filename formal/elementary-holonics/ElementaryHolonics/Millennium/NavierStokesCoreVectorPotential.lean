import ElementaryHolonics.Millennium.NavierStokesAxisymmetricChart
import ElementaryHolonics.Millennium.NavierStokesRescalingSpace

/-!
# Core vector potentials

This owner realizes incompressible fields as actual curls on the Euclidean carrier.  The generic
divergence-of-curl identity uses the existing second-jet symmetry square, while the meridional
formula keeps the squared-radius factor and the axis in the chart.
-/

noncomputable section

open ContDiff Set
open scoped Topology

namespace Soma.Holonics.Millennium.NavierStokesCoreVectorPotential

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesAxisymmetricChart
open Soma.Holonics.Millennium.NavierStokesPeriodicEnergy
open Soma.Holonics.Millennium.NavierStokesVorticity

/-- The actual curl receiver of a vector potential on the Euclidean carrier. -/
def coreCurl (potential : InitialVelocity) : InitialVelocity :=
  fun x ↦ vorticityAt potential x

/-- Smooth potentials have smooth actual curls, since the curl is a continuous-linear face of the
spatial derivative. -/
theorem coreCurl_contDiff
    (potential : InitialVelocity) (hpotential : ContDiff ℝ ∞ potential) :
    ContDiff ℝ ∞ (coreCurl potential) := by
  have hderiv : ContDiff ℝ ∞ (fun x ↦ fderiv ℝ potential x) :=
    hpotential.fderiv_right (by simp)
  have hrepresentation : (fun x ↦ coreCurl potential x) =
      derivativeCurlLinearMap ∘ (fun x ↦ fderiv ℝ potential x) := by
    funext x
    exact (derivativeCurlLinearMap_apply (fderiv ℝ potential x)).symm
  change ContDiff ℝ ∞ (fun x ↦ coreCurl potential x)
  rw [hrepresentation]
  exact derivativeCurlLinearMap.contDiff.comp hderiv

/-- The actual curl preserves the spatial unit periods of its potential. -/
theorem coreCurl_isOnePeriodic
    (potential : InitialVelocity) (hperiodic : IsOnePeriodic potential) :
    IsOnePeriodic (coreCurl potential) := by
  intro x i
  change vorticityAt potential (x + EuclideanSpace.single i 1) = vorticityAt potential x
  exact congrArg derivativeCurlLinearMap (fderiv_isOnePeriodic potential hperiodic x i)

/-- An actual `C²` vector potential has divergence-free curl. -/
theorem divergence_coreCurl_eq_zero
    (potential : InitialVelocity) (hpotential : ContDiff ℝ 2 potential) (x : Space) :
    divergence (coreCurl potential) x = 0 := by
  change divergence (fun y : Space ↦ vorticityAt potential y) x = 0
  rw [← divergenceFromJacobian_velocityJacobianAt]
  rw [velocityJacobianAt_vorticity_eq_vorticityJacobianFromSecondJet
    potential x hpotential.contDiffAt]
  exact divergence_vorticityJacobian_eq_zero (secondJetAt potential x)
    (secondJetAt_hasMixedSpatialSymmetry potential x hpotential.contDiffAt)

/-- A meridional potential `(-y h, x h, g)` written through the existing axisymmetric chart. -/
def meridionalVectorPotential
    (h g : MeridionalProfile) : InitialVelocity :=
  axisymmetricVelocity (fun _ ↦ 0) h g

/-- The curl of `(-y h(s,z), x h(s,z), g(s,z))` is an axisymmetric velocity, with no division by
the radius and with all squared-radius factors retained at `s = 0`. -/
theorem vorticity_meridionalVectorPotential
    (h g : MeridionalProfile) (hh : ContDiff ℝ 2 h) (hg : ContDiff ℝ 2 g)
    (x : Space) :
    coreCurl (meridionalVectorPotential h g) x =
      axisymmetricVelocity
        (fun p ↦ -axialDerivative h p)
        (fun p ↦ -2 * radialDerivative g p)
    (fun p ↦ 2 * h p + 2 * p.1 * radialDerivative h p) x := by
  have hhdiff : Differentiable ℝ h := hh.differentiable (by norm_num)
  have hgdiff : Differentiable ℝ g := hg.differentiable (by norm_num)
  have haxis := vorticityAt_axisymmetricVelocity
    (fun _ : ℝ × ℝ ↦ 0) h g x
    (differentiableAt_const (c := (0 : ℝ)))
    (hhdiff (meridionalChart x))
    (hgdiff (meridionalChart x))
  rw [coreCurl, meridionalVectorPotential] at ⊢
  rw [haxis]
  simp [axisymmetricVelocity, assemble, meridionalChart, add_comm, axialDerivative]
  ring_nf

/-- Actual smooth meridional coefficients construct a smooth Cartesian potential. -/
theorem meridionalVectorPotential_contDiff (h g : MeridionalProfile)
    (hh : ContDiff ℝ ∞ h) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (meridionalVectorPotential h g) := by
  have h0 : ContDiff ℝ ∞ (fun x : Space ↦ x 0) := (coordinateProjection 0).contDiff
  have h1 : ContDiff ℝ ∞ (fun x : Space ↦ x 1) := (coordinateProjection 1).contDiff
  have h2 : ContDiff ℝ ∞ (fun x : Space ↦ x 2) := (coordinateProjection 2).contDiff
  have hm : ContDiff ℝ ∞ meridionalChart := ((h0.pow 2).add (h1.pow 2)).prodMk h2
  have hfirst := ((h1.mul (hh.comp hm)).neg).smul
    (contDiff_const : ContDiff ℝ ∞ (fun _ : Space ↦ EuclideanSpace.single (0 : Fin 3) (1 : ℝ)))
  have hsecond := (h0.mul (hh.comp hm)).smul
    (contDiff_const : ContDiff ℝ ∞ (fun _ : Space ↦ EuclideanSpace.single (1 : Fin 3) (1 : ℝ)))
  have hthird := (hg.comp hm).smul
    (contDiff_const : ContDiff ℝ ∞ (fun _ : Space ↦ EuclideanSpace.single (2 : Fin 3) (1 : ℝ)))
  unfold meridionalVectorPotential NavierStokesAxisymmetricChart.axisymmetricVelocity assemble
  simpa using (hfirst.add hsecond).add hthird

/-- A complete finite bivariate polynomial, with arbitrary real coefficient values. -/
def finitePolynomialProfile (Ns Nz : ℕ) (c : ℕ → ℕ → ℝ) : MeridionalProfile :=
  fun p ↦ ∑ m ∈ Finset.range Ns, ∑ n ∈ Finset.range Nz, c m n * p.1 ^ m * p.2 ^ n

theorem finitePolynomialProfile_contDiff (Ns Nz : ℕ) (c : ℕ → ℕ → ℝ) :
    ContDiff ℝ ∞ (finitePolynomialProfile Ns Nz c) := by
  unfold finitePolynomialProfile
  fun_prop

/-- This constructor admits every retained Euler and viscous coefficient, including free
fibres; it is not restricted to a low-degree witness. -/
def finitePolynomialPotential (Ns Nz : ℕ) (h g : ℕ → ℕ → ℝ) : InitialVelocity :=
  meridionalVectorPotential (finitePolynomialProfile Ns Nz h) (finitePolynomialProfile Ns Nz g)

theorem finitePolynomialPotential_contDiff (Ns Nz : ℕ) (h g : ℕ → ℕ → ℝ) :
    ContDiff ℝ ∞ (finitePolynomialPotential Ns Nz h g) :=
  meridionalVectorPotential_contDiff _ _ (finitePolynomialProfile_contDiff Ns Nz h)
    (finitePolynomialProfile_contDiff Ns Nz g)

def physicalPotential (ell q : ℝ) (potential : InitialVelocity) : InitialVelocity :=
  NavierStokesRescalingSpace.spatialPullback (ell / q) ell⁻¹ 0 potential

theorem physicalPotential_contDiff (ell q : ℝ) (potential : InitialVelocity)
    (hp : ContDiff ℝ ∞ potential) : ContDiff ℝ ∞ (physicalPotential ell q potential) := by
  have hpull := hp.comp (contDiff_const_smul ell⁻¹)
  unfold physicalPotential NavierStokesRescalingSpace.spatialPullback
  simpa only [Function.comp_def, zero_add] using
    (contDiff_const_smul (ell / q) : ContDiff ℝ ∞ (fun z : Space ↦ (ell / q) • z)).comp hpull

/-- The vector-potential scale reconstructs exactly the physical velocity normalizer. -/
theorem coreCurl_physicalPotential (ell q : ℝ) (potential : InitialVelocity)
    (hell : ell ≠ 0) (x : Space) :
    coreCurl (physicalPotential ell q potential) x =
      q⁻¹ • coreCurl potential (ell⁻¹ • x) := by
  change derivativeCurlLinearMap (fderiv ℝ (physicalPotential ell q potential) x) =
    q⁻¹ • derivativeCurlLinearMap (fderiv ℝ potential (ell⁻¹ • x))
  rw [physicalPotential, NavierStokesRescalingSpace.fderiv_spatialPullback, map_smul]
  have hscalar : ell / q * ell⁻¹ = q⁻¹ := by field_simp
  simp [smul_smul, hscalar]

#print axioms divergence_coreCurl_eq_zero
#print axioms coreCurl_contDiff
#print axioms coreCurl_isOnePeriodic
#print axioms vorticity_meridionalVectorPotential
#print axioms finitePolynomialPotential_contDiff
#print axioms coreCurl_physicalPotential

end Soma.Holonics.Millennium.NavierStokesCoreVectorPotential
