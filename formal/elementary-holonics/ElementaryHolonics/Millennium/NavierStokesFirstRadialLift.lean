import ElementaryHolonics.Millennium.NavierStokesAxialLift

/-!
# First radial lift product jets

This owner supplies the missing product-profile calculus used by the first radial lift.  The
product `s * f(z)` is differentiated as an actual function on the meridional plane; its radial
and axial receivers are then evaluated without introducing a cylindrical division.
-/

noncomputable section

open ContDiff Set

namespace Soma.Holonics.Millennium.NavierStokesFirstRadialLift

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesAxisymmetricChart
open Soma.Holonics.Millennium.NavierStokesAxialLift

theorem productProfile_jets
    (f : ℝ → ℝ) (f' : ℝ) (p : ℝ × ℝ) (hf : HasDerivAt f f' p.2) :
    DifferentiableAt ℝ (fun q : ℝ × ℝ ↦ q.1 * f q.2) p ∧
      radialDerivative (fun q : ℝ × ℝ ↦ q.1 * f q.2) p = f p.2 ∧
      axialDerivative (fun q : ℝ × ℝ ↦ q.1 * f q.2) p = p.1 * f' := by
  let fstCLM : ℝ × ℝ →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ
  let sndCLM : ℝ × ℝ →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℝ ℝ
  have hcomp := hf.hasFDerivAt.comp p sndCLM.hasFDerivAt
  have hprod := fstCLM.hasFDerivAt.mul hcomp
  change HasFDerivAt (fun q : ℝ × ℝ ↦ q.1 * f q.2) _ p at hprod
  have hdiff : DifferentiableAt ℝ (fun q : ℝ × ℝ ↦ q.1 * f q.2) p := by
    change DifferentiableAt ℝ (fun q : ℝ × ℝ ↦ fstCLM q * (f (sndCLM q))) p
    exact hprod.differentiableAt
  refine ⟨hdiff, ?_, ?_⟩
  · unfold radialDerivative
    have h := hprod.fderiv
    have h' := congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ ↦ L (1, 0)) h
    simpa [fstCLM, sndCLM] using h'
  · unfold axialDerivative
    have h := hprod.fderiv
    have h' := congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ ↦ L (0, 1)) h
    simpa [fstCLM, sndCLM] using h'

def linearProfile (f g : ℝ → ℝ) : MeridionalProfile := fun p ↦ f p.2 + p.1 * g p.2

def firstRadialV (W H : ℝ → ℝ) : MeridionalProfile :=
  linearProfile (fun z ↦ -deriv W z / 2) (fun z ↦ -deriv H z / 4)

def firstRadialOmega (F K : ℝ → ℝ) : MeridionalProfile :=
  linearProfile F K

def firstRadialZ (W H : ℝ → ℝ) : MeridionalProfile :=
  linearProfile W H

theorem firstRadialProfiles_contDiff
    (F W H K : ℝ → ℝ)
    (hF : ContDiff ℝ ∞ F) (hW : ContDiff ℝ ∞ W)
    (hH : ContDiff ℝ ∞ H) (hK : ContDiff ℝ ∞ K) :
    ContDiff ℝ ∞ (firstRadialV W H) ∧
      ContDiff ℝ ∞ (firstRadialOmega F K) ∧
      ContDiff ℝ ∞ (firstRadialZ W H) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold firstRadialV linearProfile
    fun_prop
  · unfold firstRadialOmega linearProfile
    fun_prop
  · unfold firstRadialZ linearProfile
    fun_prop

theorem addProfile_jets
    (f g : MeridionalProfile) (p : ℝ × ℝ)
    (hf : DifferentiableAt ℝ f p) (hg : DifferentiableAt ℝ g p) :
    radialDerivative (fun q ↦ f q + g q) p =
        radialDerivative f p + radialDerivative g p ∧
      axialDerivative (fun q ↦ f q + g q) p =
        axialDerivative f p + axialDerivative g p := by
  have h : fderiv ℝ (fun q : ℝ × ℝ ↦ f q + g q) p =
      fderiv ℝ f p + fderiv ℝ g p := by
    have hfun : (fun q : ℝ × ℝ ↦ f q + g q) = f + g := by
      funext q
      rfl
    rw [hfun]
    exact fderiv_add hf hg
  constructor
  · unfold radialDerivative
    rw [h]
    rfl
  · unfold axialDerivative
    rw [h]
    rfl

theorem linearProfile_jets (f g : ℝ → ℝ) (p : ℝ × ℝ) (f' g' : ℝ)
    (hf : HasDerivAt f f' p.2) (hg : HasDerivAt g g' p.2) :
    DifferentiableAt ℝ (linearProfile f g) p ∧ radialDerivative (linearProfile f g) p = g p.2 ∧
      axialDerivative (linearProfile f g) p = f' + p.1 * g' := by
  have ja := Soma.Holonics.Millennium.NavierStokesAxialLift.axialOnly_jet f p f' hf
  have jb := productProfile_jets g g' p hg
  have jadd := addProfile_jets _ _ p ja.1 jb.1
  refine ⟨ja.1.add jb.1, ?_, ?_⟩
  · exact jadd.1.trans (by rw [ja.2.1, jb.2.1, zero_add])
  · exact jadd.2.trans (by rw [ja.2.2, jb.2.2])

theorem firstRadialProfiles_jets (F W H K : ℝ → ℝ)
    (hF : ContDiff ℝ ∞ F) (hW : ContDiff ℝ ∞ W)
    (hH : ContDiff ℝ ∞ H) (hK : ContDiff ℝ ∞ K) (p : ℝ × ℝ) :
    (DifferentiableAt ℝ (firstRadialV W H) p ∧
      radialDerivative (firstRadialV W H) p = -deriv H p.2 / 4 ∧
      axialDerivative (firstRadialV W H) p = -deriv (deriv W) p.2 / 2 - p.1 * deriv (deriv H) p.2 / 4) ∧
    (DifferentiableAt ℝ (firstRadialOmega F K) p ∧
      radialDerivative (firstRadialOmega F K) p = K p.2 ∧
      axialDerivative (firstRadialOmega F K) p = deriv F p.2 + p.1 * deriv K p.2) ∧
    (DifferentiableAt ℝ (firstRadialZ W H) p ∧
      radialDerivative (firstRadialZ W H) p = H p.2 ∧
      axialDerivative (firstRadialZ W H) p = deriv W p.2 + p.1 * deriv H p.2) := by
  have hw1 : ContDiff ℝ ∞ (deriv W) := by fun_prop
  have hh1 : ContDiff ℝ ∞ (deriv H) := by fun_prop
  refine ⟨?_, ?_, ?_⟩
  · have h := linearProfile_jets (fun z ↦ -deriv W z / 2) (fun z ↦ -deriv H z / 4) p _ _
      (((hw1.differentiable (by simp) p.2).hasDerivAt.neg).div_const 2)
      (((hh1.differentiable (by simp) p.2).hasDerivAt.neg).div_const 4)
    refine ⟨h.1, h.2.1, h.2.2.trans ?_⟩
    ring
  · exact linearProfile_jets F K p _ _ ((hF.differentiable (by simp) p.2).hasDerivAt)
      ((hK.differentiable (by simp) p.2).hasDerivAt)
  · exact linearProfile_jets W H p _ _ ((hW.differentiable (by simp) p.2).hasDerivAt)
      ((hH.differentiable (by simp) p.2).hasDerivAt)

def firstRadialVelocity (F W H K : ℝ → ℝ) : InitialVelocity :=
  axisymmetricVelocity (firstRadialV W H) (firstRadialOmega F K) (firstRadialZ W H)

theorem divergence_firstRadialVelocity (F W H K : ℝ → ℝ)
    (hF : ContDiff ℝ ∞ F) (hW : ContDiff ℝ ∞ W)
    (hH : ContDiff ℝ ∞ H) (hK : ContDiff ℝ ∞ K) (x : Space) :
    divergence (firstRadialVelocity F W H K) x = 0 := by
  obtain ⟨hV,hO,hZ⟩ := firstRadialProfiles_jets F W H K hF hW hH hK (meridionalChart x)
  rw [firstRadialVelocity, divergence_axisymmetricVelocity _ _ _ x hV.1 hO.1 hZ.1,
    hV.2.1, hZ.2.2]
  simp only [firstRadialV, linearProfile]
  ring

def firstAxialCoefficient (alpha beta : ℝ) (W H : ℝ → ℝ) (z : ℝ) : ℝ :=
  (W z + beta * z) * deriv H z + (alpha + 2 * beta) * H z

def secondAxialCoefficient (W H : ℝ → ℝ) (z : ℝ) : ℝ := H z * deriv H z / 2

def firstSwirlCoefficient (alpha beta : ℝ) (F W H K : ℝ → ℝ) (z : ℝ) : ℝ :=
  (W z + beta * z) * deriv K z + (alpha + 3 * beta - 2 * deriv W z) * K z
    + H z * deriv F z - deriv H z * F z / 2

def secondSwirlCoefficient (H K : ℝ → ℝ) (z : ℝ) : ℝ :=
  H z * deriv K z - deriv H z * K z

theorem axialMomentum_firstRadial (alpha beta : ℝ) (F W H K : ℝ → ℝ)
    (hF : ContDiff ℝ ∞ F) (hW : ContDiff ℝ ∞ W)
    (hH : ContDiff ℝ ∞ H) (hK : ContDiff ℝ ∞ K) (p : ℝ × ℝ) :
    axialMomentum alpha beta (firstRadialV W H) (firstRadialOmega F K) (firstRadialZ W H) p =
      axialB F W alpha beta p.2 + p.1 * firstAxialCoefficient alpha beta W H p.2 +
        p.1 ^ 2 * secondAxialCoefficient W H p.2 := by
  obtain ⟨hV,hO,hZ⟩ := firstRadialProfiles_jets F W H K hF hW hH hK p
  rw [axialMomentum, hZ.2.1, hZ.2.2]
  simp only [firstRadialV, firstRadialZ, linearProfile, axialB, firstAxialCoefficient,
    secondAxialCoefficient]
  ring

theorem swirlMomentum_firstRadial (alpha beta : ℝ) (F W H K : ℝ → ℝ)
    (hF : ContDiff ℝ ∞ F) (hW : ContDiff ℝ ∞ W)
    (hH : ContDiff ℝ ∞ H) (hK : ContDiff ℝ ∞ K) (p : ℝ × ℝ) :
    swirlMomentum alpha beta (firstRadialV W H) (firstRadialOmega F K) (firstRadialZ W H) p =
      axialC F W alpha beta p.2 + p.1 * firstSwirlCoefficient alpha beta F W H K p.2 +
        p.1 ^ 2 * secondSwirlCoefficient H K p.2 := by
  obtain ⟨hV,hO,hZ⟩ := firstRadialProfiles_jets F W H K hF hW hH hK p
  rw [swirlMomentum, hO.2.1, hO.2.2]
  simp only [firstRadialV, firstRadialOmega, firstRadialZ, linearProfile, axialC,
    firstSwirlCoefficient, secondSwirlCoefficient]
  ring

theorem radialMomentum_firstRadial_axis (alpha beta : ℝ) (F W H K : ℝ → ℝ)
    (hF : ContDiff ℝ ∞ F) (hW : ContDiff ℝ ∞ W)
    (hH : ContDiff ℝ ∞ H) (hK : ContDiff ℝ ∞ K) (z : ℝ) :
    radialMomentum alpha beta (firstRadialV W H) (firstRadialOmega F K) (firstRadialZ W H) (0,z) =
      axialA F W alpha beta z := by
  obtain ⟨hV,hO,hZ⟩ := firstRadialProfiles_jets F W H K hF hW hH hK (0,z)
  rw [radialMomentum, hV.2.1, hV.2.2]
  simp [firstRadialV, firstRadialOmega, firstRadialZ, linearProfile, axialA]
  ring

theorem radialDerivative_quadraticProfile_axis (f g h : ℝ → ℝ) (z f' g' h' : ℝ)
    (hf : HasDerivAt f f' z) (hg : HasDerivAt g g' z) (hh : HasDerivAt h h' z) :
    radialDerivative (fun p : ℝ × ℝ ↦ f p.2 + p.1 * g p.2 + p.1 ^ 2 * h p.2) (0,z) = g z := by
  let fstCLM : ℝ × ℝ →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ ℝ
  let sndCLM : ℝ × ℝ →L[ℝ] ℝ := ContinuousLinearMap.snd ℝ ℝ ℝ
  have hfL := hf.hasFDerivAt.comp (0,z) sndCLM.hasFDerivAt
  have hgL := hg.hasFDerivAt.comp (0,z) sndCLM.hasFDerivAt
  have hhL := hh.hasFDerivAt.comp (0,z) sndCLM.hasFDerivAt
  have ht := (hfL.add (fstCLM.hasFDerivAt.mul hgL)).add ((fstCLM.hasFDerivAt.pow 2).mul hhL)
  change HasFDerivAt (fun p : ℝ × ℝ ↦ f p.2 + p.1 * g p.2 + p.1 ^ 2 * h p.2) _ (0,z) at ht
  rw [radialDerivative, ht.fderiv]
  simp [fstCLM, sndCLM]

theorem radialDerivative_axialMomentum_firstRadial_axis (alpha beta : ℝ) (F W H K : ℝ → ℝ)
    (hF : ContDiff ℝ ∞ F) (hW : ContDiff ℝ ∞ W)
    (hH : ContDiff ℝ ∞ H) (hK : ContDiff ℝ ∞ K) (z : ℝ) :
    radialDerivative (axialMomentum alpha beta (firstRadialV W H)
      (firstRadialOmega F K) (firstRadialZ W H)) (0,z) = firstAxialCoefficient alpha beta W H z := by
  have heq := funext (axialMomentum_firstRadial alpha beta F W H K hF hW hH hK)
  rw [heq]
  have h0 : ContDiff ℝ ∞ (axialB F W alpha beta) := by unfold axialB; fun_prop
  have h1 : ContDiff ℝ ∞ (firstAxialCoefficient alpha beta W H) := by unfold firstAxialCoefficient; fun_prop
  have h2 : ContDiff ℝ ∞ (secondAxialCoefficient W H) := by unfold secondAxialCoefficient; fun_prop
  exact radialDerivative_quadraticProfile_axis _ _ _ z _ _ _
    ((h0.differentiable (by simp) z).hasDerivAt) ((h1.differentiable (by simp) z).hasDerivAt)
    ((h2.differentiable (by simp) z).hasDerivAt)

theorem radialDerivative_swirlMomentum_firstRadial_axis (alpha beta : ℝ) (F W H K : ℝ → ℝ)
    (hF : ContDiff ℝ ∞ F) (hW : ContDiff ℝ ∞ W)
    (hH : ContDiff ℝ ∞ H) (hK : ContDiff ℝ ∞ K) (z : ℝ) :
    radialDerivative (swirlMomentum alpha beta (firstRadialV W H)
      (firstRadialOmega F K) (firstRadialZ W H)) (0,z) = firstSwirlCoefficient alpha beta F W H K z := by
  have heq := funext (swirlMomentum_firstRadial alpha beta F W H K hF hW hH hK)
  rw [heq]
  have h0 : ContDiff ℝ ∞ (axialC F W alpha beta) := by unfold axialC; fun_prop
  have h1 : ContDiff ℝ ∞ (firstSwirlCoefficient alpha beta F W H K) := by unfold firstSwirlCoefficient; fun_prop
  have h2 : ContDiff ℝ ∞ (secondSwirlCoefficient H K) := by unfold secondSwirlCoefficient; fun_prop
  exact radialDerivative_quadraticProfile_axis _ _ _ z _ _ _
    ((h0.differentiable (by simp) z).hasDerivAt) ((h1.differentiable (by simp) z).hasDerivAt)
    ((h2.differentiable (by simp) z).hasDerivAt)

section Audit

#print axioms productProfile_jets
#print axioms firstRadialProfiles_contDiff
#print axioms firstRadialProfiles_jets
#print axioms divergence_firstRadialVelocity
#print axioms axialMomentum_firstRadial
#print axioms swirlMomentum_firstRadial
#print axioms radialMomentum_firstRadial_axis
#print axioms radialDerivative_axialMomentum_firstRadial_axis
#print axioms radialDerivative_swirlMomentum_firstRadial_axis

end Audit

end Soma.Holonics.Millennium.NavierStokesFirstRadialLift
