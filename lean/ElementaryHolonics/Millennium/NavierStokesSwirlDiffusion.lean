import ElementaryHolonics.Millennium.NavierStokesSwirlCirculation

/-!
# Squared-radius swirl diffusion

This owner records the meridional second-jet identity for the actual angular momentum
`ell = s * Omega`.  It uses the Cartesian squared-radius coordinate `s` directly and retains the
axis; no cylindrical division is introduced.
-/

noncomputable section

open ContDiff Set InnerProductSpace
open scoped Laplacian

namespace Soma.Holonics.Millennium.NavierStokesSwirlDiffusion

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesAxisymmetricChart
open Soma.Holonics.Millennium.NavierStokesSwirlCirculation
open Soma.Holonics.Millennium.NavierStokesPeriodicEnergy

def radialSecondDerivative (f : MeridionalProfile) (p : ℝ × ℝ) : ℝ :=
  fderiv ℝ (radialDerivative f) p (1, 0)

def axialSecondDerivative (f : MeridionalProfile) (p : ℝ × ℝ) : ℝ :=
  fderiv ℝ (axialDerivative f) p (0, 1)

def meridionalDiffusion (f : MeridionalProfile) (p : ℝ × ℝ) : ℝ :=
  4 * p.1 * radialSecondDerivative f p + axialSecondDerivative f p

theorem angularMomentum_radialDerivative
    (Omega : MeridionalProfile) (p : ℝ × ℝ)
    (hOmega : DifferentiableAt ℝ Omega p) :
    radialDerivative (angularMomentum Omega) p =
      Omega p + p.1 * radialDerivative Omega p := by
  have hprod := (hasFDerivAt_fst (𝕜 := ℝ) (p := p)).mul hOmega.hasFDerivAt
  unfold radialDerivative angularMomentum
  rw [hprod.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
  simp [radialDerivative]
  ring

theorem angularMomentum_axialDerivative
    (Omega : MeridionalProfile) (p : ℝ × ℝ)
    (hOmega : DifferentiableAt ℝ Omega p) :
    axialDerivative (angularMomentum Omega) p =
      p.1 * axialDerivative Omega p := by
  have hprod := (hasFDerivAt_fst (𝕜 := ℝ) (p := p)).mul hOmega.hasFDerivAt
  unfold axialDerivative angularMomentum
  rw [hprod.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
  simp [axialDerivative]

theorem differentiableAt_radialDerivative
    (Omega : MeridionalProfile) (p : ℝ × ℝ)
    (hOmega : ContDiff ℝ 2 Omega) :
    DifferentiableAt ℝ (radialDerivative Omega) p := by
  have hD : ContDiff ℝ 1 (fderiv ℝ Omega) :=
    hOmega.fderiv_right (m := 1) (by norm_num)
  exact (hD.clm_apply (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ × ℝ => ((1 : ℝ), (0 : ℝ))))).differentiable
    (by norm_num) p

theorem differentiableAt_axialDerivative
    (Omega : MeridionalProfile) (p : ℝ × ℝ)
    (hOmega : ContDiff ℝ 2 Omega) :
    DifferentiableAt ℝ (axialDerivative Omega) p := by
  have hD : ContDiff ℝ 1 (fderiv ℝ Omega) :=
    hOmega.fderiv_right (m := 1) (by norm_num)
  exact (hD.clm_apply (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ × ℝ => ((0 : ℝ), (1 : ℝ))))).differentiable
    (by norm_num) p

theorem angularMomentum_radialSecondDerivative
    (Omega : MeridionalProfile) (p : ℝ × ℝ)
    (hOmega : ContDiff ℝ 2 Omega) :
    radialSecondDerivative (angularMomentum Omega) p =
      2 * radialDerivative Omega p + p.1 * radialSecondDerivative Omega p := by
  have hOmega' : DifferentiableAt ℝ Omega p := hOmega.differentiable (by norm_num) p
  have hRad := differentiableAt_radialDerivative Omega p hOmega
  have hfun :
      radialDerivative (angularMomentum Omega) =
        Omega + (fun q : ℝ × ℝ ↦ q.1) * radialDerivative Omega := by
    funext q
    rw [angularMomentum_radialDerivative Omega q (hOmega.differentiable (by norm_num) q)]
    rfl
  have hmul : DifferentiableAt ℝ
      ((fun q : ℝ × ℝ ↦ q.1) * radialDerivative Omega) p :=
    ((hasFDerivAt_fst (𝕜 := ℝ) (p := p)).mul hRad.hasFDerivAt).differentiableAt
  have hsum := fderiv_add hOmega' hmul
  rw [radialSecondDerivative, hfun, hsum]
  have hprod := (hasFDerivAt_fst (𝕜 := ℝ) (p := p)).mul hRad.hasFDerivAt
  rw [hprod.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
  simp [radialDerivative, radialSecondDerivative]
  ring

theorem angularMomentum_axialSecondDerivative
    (Omega : MeridionalProfile) (p : ℝ × ℝ)
    (hOmega : ContDiff ℝ 2 Omega) :
    axialSecondDerivative (angularMomentum Omega) p =
      p.1 * axialSecondDerivative Omega p := by
  have hOmega' : DifferentiableAt ℝ Omega p := hOmega.differentiable (by norm_num) p
  have hAx := differentiableAt_axialDerivative Omega p hOmega
  have hfun :
      axialDerivative (angularMomentum Omega) =
        (fun q : ℝ × ℝ ↦ q.1) * axialDerivative Omega := by
    funext q
    rw [angularMomentum_axialDerivative Omega q (hOmega.differentiable (by norm_num) q)]
    rfl
  have hmul := fderiv_mul
    ((hasFDerivAt_fst (𝕜 := ℝ) (p := p)).differentiableAt) hAx
  rw [axialSecondDerivative, hfun, hmul]
  have hfst : fderiv ℝ (fun q : ℝ × ℝ ↦ q.1) p (0, 1) = 0 := by
    rw [(hasFDerivAt_fst (𝕜 := ℝ) (p := p)).fderiv]
    simp
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply]
  rw [hfst]
  simp [axialDerivative, axialSecondDerivative]

theorem angularMomentum_meridionalDiffusion
    (Omega : MeridionalProfile) (p : ℝ × ℝ)
    (hOmega : ContDiff ℝ 2 Omega) :
    meridionalDiffusion (angularMomentum Omega) p =
      p.1 * (4 * p.1 * radialSecondDerivative Omega p +
        8 * radialDerivative Omega p + axialSecondDerivative Omega p) := by
  rw [meridionalDiffusion, angularMomentum_radialSecondDerivative Omega p hOmega,
    angularMomentum_axialSecondDerivative Omega p hOmega]
  ring

theorem meridionalChart_contDiff : ContDiff ℝ 2 meridionalChart := by
  have h0 : ContDiff ℝ 2 (fun x : Space ↦ x 0) := (coordinateProjection 0).contDiff
  have h1 : ContDiff ℝ 2 (fun x : Space ↦ x 1) := (coordinateProjection 1).contDiff
  have h2 : ContDiff ℝ 2 (fun x : Space ↦ x 2) := (coordinateProjection 2).contDiff
  exact ((h0.pow 2).add (h1.pow 2)).prodMk h2

/-- The existing gradient and divergence owners already contain the second chain rule needed
by the scalar lift. This composition retains the axis in Cartesian coordinates. -/
theorem laplacian_profileLift (f : MeridionalProfile) (hf : ContDiff ℝ 2 f) (x : Space) :
    Δ (fun y ↦ f (meridionalChart y)) x =
      4 * (meridionalChart x).1 * radialSecondDerivative f (meridionalChart x) +
        4 * radialDerivative f (meridionalChart x) + axialSecondDerivative f (meridionalChart x) := by
  have hgrad : gradient (fun y ↦ f (meridionalChart y)) =
      axisymmetricVelocity (fun p ↦ 2 * radialDerivative f p) (fun _ ↦ 0) (axialDerivative f) := by
    funext y
    rw [gradient_axisymmetricPressure f y (hf.differentiable (by norm_num) _)]
    simp [axisymmetricVelocity]
    congr 1 <;> ring
  have hlift : ContDiff ℝ 2 (fun y ↦ f (meridionalChart y)) := hf.comp meridionalChart_contDiff
  rw [← divergence_gradient_eq_laplacian (fun y ↦ f (meridionalChart y)) hlift x, hgrad]
  have hrad := differentiableAt_radialDerivative f (meridionalChart x) hf
  have hax := differentiableAt_axialDerivative f (meridionalChart x) hf
  rw [divergence_axisymmetricVelocity _ _ _ x (hrad.const_mul 2) (by fun_prop) hax]
  have hscaled : radialDerivative (fun p ↦ 2 * radialDerivative f p) (meridionalChart x) =
      2 * radialSecondDerivative f (meridionalChart x) := by
    change fderiv ℝ (fun p ↦ 2 * radialDerivative f p) (meridionalChart x) (1, 0) = _
    rw [(hrad.hasFDerivAt.const_mul 2).fderiv]
    simp [radialSecondDerivative, radialDerivative]
  rw [hscaled]
  change 2 * (2 * radialDerivative f (meridionalChart x)) +
    2 * (meridionalChart x).1 * (2 * radialSecondDerivative f (meridionalChart x)) +
    axialSecondDerivative f (meridionalChart x) = _
  ring

theorem gradient_product (f g : Space → ℝ) (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) :
    gradient (fun x ↦ f x * g x) = fun x ↦ f x • gradient g x + g x • gradient f x := by
  funext x
  apply ext_inner_right ℝ
  intro direction
  rw [inner_gradient_left, fderiv_fun_mul (hf x) (hg x)]
  simp [inner_add_left, real_inner_smul_left, inner_gradient_left]

theorem divergence_sum (u v : InitialVelocity) (x : Space)
    (hu : DifferentiableAt ℝ u x) (hv : DifferentiableAt ℝ v x) :
    divergence (fun y ↦ u y + v y) x = divergence u x + divergence v x := by
  unfold divergence
  rw [fderiv_fun_add hu hv]
  change LinearMap.trace ℝ Space ((fderiv ℝ u x).toLinearMap + (fderiv ℝ v x).toLinearMap) = _
  rw [map_add]

theorem laplacian_product (f g : Space → ℝ) (hf : ContDiff ℝ 2 f)
    (hg : ContDiff ℝ 2 g) (x : Space) :
    Δ (fun y ↦ f y * g y) x =
      f x * Δ g x + g x * Δ f x + 2 * inner ℝ (gradient f x) (gradient g x) := by
  have hfd := hf.differentiable (by norm_num)
  have hgd := hg.differentiable (by norm_num)
  have hfgrad := (gradient_contDiff_one f hf).differentiable (by norm_num)
  have hggrad := (gradient_contDiff_one g hg).differentiable (by norm_num)
  have hfg : DifferentiableAt ℝ (fun y ↦ f y • gradient g y) x := (hfd x).smul (hggrad x)
  have hgf : DifferentiableAt ℝ (fun y ↦ g y • gradient f y) x := (hgd x).smul (hfgrad x)
  rw [← divergence_gradient_eq_laplacian _ (hf.mul hg) x, gradient_product f g hfd hgd,
    divergence_sum (fun y ↦ f y • gradient g y) (fun y ↦ g y • gradient f y) x hfg hgf,
    divergence_pressureFlux _ _ x (hggrad x) (hfd x),
    divergence_pressureFlux _ _ x (hfgrad x) (hgd x),
    divergence_gradient_eq_laplacian g hg x, divergence_gradient_eq_laplacian f hf x,
    real_inner_comm (gradient g x) (gradient f x)]
  ring

theorem laplacian_coordinate (i : Fin 3) (x : Space) :
    Δ (fun y : Space ↦ y i) x = 0 := by
  rw [congrFun (laplacian_eq_iteratedFDeriv_orthonormalBasis _
    (EuclideanSpace.basisFun (Fin 3) ℝ)) x]
  have hd : fderiv ℝ (fun y : Space ↦ y i) = fun _ ↦ coordinateProjection i := by
    funext y
    exact (coordinateProjection i).fderiv
  have hdd : fderiv ℝ (fun _ : Space ↦ coordinateProjection i) x = 0 :=
    (hasFDerivAt_const (x := x) (coordinateProjection i)).fderiv
  simp only [iteratedFDeriv_two_apply, hd, hdd, ContinuousLinearMap.zero_apply,
    Finset.sum_const_zero]

/-- Actual Cartesian coordinate carriers return the angular vector-Laplacian coefficient. -/
theorem laplacian_coordinate_mul_profileLift (f : MeridionalProfile) (hf : ContDiff ℝ 2 f)
    (i : Fin 2) (x : Space) :
    Δ (fun y : Space ↦ y i.castSucc * f (meridionalChart y)) x =
      x i.castSucc * (4 * (meridionalChart x).1 * radialSecondDerivative f (meridionalChart x) +
        8 * radialDerivative f (meridionalChart x) + axialSecondDerivative f (meridionalChart x)) := by
  have h := laplacian_product (fun y : Space ↦ y i.castSucc)
    (fun y ↦ f (meridionalChart y)) (coordinateProjection i.castSucc).contDiff
    (hf.comp meridionalChart_contDiff) x
  have hd : fderiv ℝ (fun y : Space ↦ y i.castSucc) x = coordinateProjection i.castSucc :=
    (coordinateProjection i.castSucc).fderiv
  rw [laplacian_coordinate, laplacian_profileLift f hf x, inner_gradient_left, hd] at h
  have hgradient := gradient_axisymmetricPressure f x (hf.differentiable (by norm_num) _)
  rw [hgradient] at h
  fin_cases i <;> simp [coordinateProjection] at h ⊢ <;> nlinarith [h]

def swirlDiffusionCoefficient (f : MeridionalProfile) (p : ℝ × ℝ) : ℝ :=
  4 * p.1 * radialSecondDerivative f p + 8 * radialDerivative f p + axialSecondDerivative f p

theorem swirlDiffusionCoefficient_contDiff (f : MeridionalProfile) (hf : ContDiff ℝ 3 f) :
    ContDiff ℝ 1 (swirlDiffusionCoefficient f) := by
  have hd2 : ContDiff ℝ 2 (fderiv ℝ f) := hf.fderiv_right (m := 2) (by norm_num)
  have hr2 : ContDiff ℝ 2 (radialDerivative f) := hd2.clm_apply contDiff_const
  have hz2 : ContDiff ℝ 2 (axialDerivative f) := hd2.clm_apply contDiff_const
  have hrr : ContDiff ℝ 1 (radialSecondDerivative f) :=
    (hr2.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hzz : ContDiff ℝ 1 (axialSecondDerivative f) :=
    (hz2.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hr1 : ContDiff ℝ 1 (radialDerivative f) := hr2.of_le (by norm_num)
  unfold swirlDiffusionCoefficient
  have hfst : ContDiff ℝ 1 (fun p : ℝ × ℝ ↦ p.1) := contDiff_fst
  exact (((contDiff_const.mul hfst).mul hrr).add (contDiff_const.mul hr1)).add hzz

/-- The diffusion value vanishes on the axis but its actual radial derivative returns the
swirl diffusion source there. The zero value receiver does not erase this jet. -/
theorem angularMomentum_diffusion_axis_jet (Omega : MeridionalProfile)
    (hOmega : ContDiff ℝ 3 Omega) (z : ℝ) :
    meridionalDiffusion (angularMomentum Omega) (0, z) = 0 ∧
      radialDerivative (meridionalDiffusion (angularMomentum Omega)) (0, z) =
        8 * radialDerivative Omega (0, z) + axialSecondDerivative Omega (0, z) := by
  have hfun : meridionalDiffusion (angularMomentum Omega) =
      angularMomentum (swirlDiffusionCoefficient Omega) := by
    funext p
    exact angularMomentum_meridionalDiffusion Omega p (hOmega.of_le (by norm_num))
  rw [hfun]
  constructor
  · simp [angularMomentum]
  · rw [angularMomentum_radialDerivative _ _
      ((swirlDiffusionCoefficient_contDiff Omega hOmega).differentiable (by norm_num) _)]
    simp [swirlDiffusionCoefficient]

theorem coordinate_profileLift_contDiff (f : MeridionalProfile) (hf : ContDiff ℝ 2 f)
    (i : Fin 3) : ContDiff ℝ 2 (fun y : Space ↦ y i * f (meridionalChart y)) :=
  (coordinateProjection i).contDiff.mul (hf.comp meridionalChart_contDiff)

theorem axisymmetricVelocity_contDiff (V Omega W : MeridionalProfile)
    (hV : ContDiff ℝ 2 V) (hOmega : ContDiff ℝ 2 Omega) (hW : ContDiff ℝ 2 W) :
    ContDiff ℝ 2 (axisymmetricVelocity V Omega W) := by
  have h0 := (coordinate_profileLift_contDiff V hV 0).sub
    (coordinate_profileLift_contDiff Omega hOmega 1)
  have h1 := (coordinate_profileLift_contDiff V hV 1).add
    (coordinate_profileLift_contDiff Omega hOmega 0)
  have h2 : ContDiff ℝ 2 (fun y ↦ W (meridionalChart y)) := hW.comp meridionalChart_contDiff
  exact ((h0.smul contDiff_const).add (h1.smul contDiff_const)).add (h2.smul contDiff_const)

/-- The meridional diffusion is the actual angular projection of the vector Laplacian. -/
theorem cartesian_laplacian_angularMomentum (V Omega W : MeridionalProfile)
    (hV : ContDiff ℝ 2 V) (hOmega : ContDiff ℝ 2 Omega) (hW : ContDiff ℝ 2 W) (x : Space) :
    x 0 * (Δ (axisymmetricVelocity V Omega W) x) 1 -
      x 1 * (Δ (axisymmetricVelocity V Omega W) x) 0 =
      meridionalDiffusion (angularMomentum Omega) (meridionalChart x) := by
  have hu := axisymmetricVelocity_contDiff V Omega W hV hOmega hW
  have hcomponent : ∀ i : Fin 3,
      Δ (fun y ↦ axisymmetricVelocity V Omega W y i) x =
        (Δ (axisymmetricVelocity V Omega W) x) i := by
    intro i
    simpa [Function.comp_def] using (hu.contDiffAt (x := x)).laplacian_CLM_comp_left
      (l := EuclideanSpace.proj i)
  have hscalar0 (f : MeridionalProfile) (hf : ContDiff ℝ 2 f) :
      Δ (fun y : Space ↦ y 0 * f (meridionalChart y)) x =
        x 0 * swirlDiffusionCoefficient f (meridionalChart x) := by
    simpa [Fin.castSucc, swirlDiffusionCoefficient] using
      laplacian_coordinate_mul_profileLift f hf (0 : Fin 2) x
  have hscalar1 (f : MeridionalProfile) (hf : ContDiff ℝ 2 f) :
      Δ (fun y : Space ↦ y 1 * f (meridionalChart y)) x =
        x 1 * swirlDiffusionCoefficient f (meridionalChart x) := by
    simpa [Fin.castSucc, swirlDiffusionCoefficient] using
      laplacian_coordinate_mul_profileLift f hf (1 : Fin 2) x
  have h0 : (Δ (axisymmetricVelocity V Omega W) x) 0 =
      x 0 * swirlDiffusionCoefficient V (meridionalChart x) -
        x 1 * swirlDiffusionCoefficient Omega (meridionalChart x) := by
    rw [← hcomponent 0]
    simp only [axisymmetricVelocity, assemble_zero]
    change Δ ((fun y : Space ↦ y 0 * V (meridionalChart y)) -
      (fun y ↦ y 1 * Omega (meridionalChart y))) x = _
    rw [(coordinate_profileLift_contDiff V hV 0).contDiffAt.laplacian_sub
      (coordinate_profileLift_contDiff Omega hOmega 1).contDiffAt]
    rw [hscalar0 V hV, hscalar1 Omega hOmega]
  have h1 : (Δ (axisymmetricVelocity V Omega W) x) 1 =
      x 1 * swirlDiffusionCoefficient V (meridionalChart x) +
        x 0 * swirlDiffusionCoefficient Omega (meridionalChart x) := by
    rw [← hcomponent 1]
    simp only [axisymmetricVelocity, assemble_one]
    change Δ ((fun y : Space ↦ y 1 * V (meridionalChart y)) +
      (fun y ↦ y 0 * Omega (meridionalChart y))) x = _
    rw [(coordinate_profileLift_contDiff V hV 1).contDiffAt.laplacian_add
      (coordinate_profileLift_contDiff Omega hOmega 0).contDiffAt]
    rw [hscalar1 V hV, hscalar0 Omega hOmega]
  rw [h0, h1, angularMomentum_meridionalDiffusion Omega (meridionalChart x) hOmega]
  unfold swirlDiffusionCoefficient meridionalChart
  ring

#print axioms angularMomentum_radialDerivative
#print axioms angularMomentum_axialDerivative
#print axioms differentiableAt_radialDerivative
#print axioms differentiableAt_axialDerivative
#print axioms angularMomentum_radialSecondDerivative
#print axioms angularMomentum_axialSecondDerivative
#print axioms angularMomentum_meridionalDiffusion
#print axioms laplacian_profileLift
#print axioms laplacian_product
#print axioms laplacian_coordinate_mul_profileLift
#print axioms cartesian_laplacian_angularMomentum
#print axioms angularMomentum_diffusion_axis_jet

end Soma.Holonics.Millennium.NavierStokesSwirlDiffusion
