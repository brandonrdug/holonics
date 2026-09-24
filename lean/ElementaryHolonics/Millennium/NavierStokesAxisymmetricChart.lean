import ElementaryHolonics.Millennium.NavierStokesPeriodicEnergy

/-!
# A Cartesian axisymmetric chart that retains the axis

The meridional address is `(x₀²+x₁²,x₂)`. Radial and azimuthal coefficients reconstruct the
actual Cartesian field `(x₀ V-x₁ Ω,x₁ V+x₀ Ω,W)`, without division by the radius. All jets in
this owner are derivatives of those actual coefficient functions.
-/

noncomputable section

open ContDiff Set InnerProductSpace
open scoped BigOperators Laplacian

namespace Soma.Holonics.Millennium.NavierStokesAxisymmetricChart

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesPeriodicFlux
open Soma.Holonics.Millennium.NavierStokesVorticity

abbrev MeridionalProfile := ℝ × ℝ → ℝ

def coordinateProjection (i : Fin 3) : Space →L[ℝ] ℝ := EuclideanSpace.proj i

def meridionalChart (x : Space) : ℝ × ℝ := (x 0 ^ 2 + x 1 ^ 2, x 2)

def radialDerivative (f : MeridionalProfile) (p : ℝ × ℝ) : ℝ := fderiv ℝ f p (1, 0)

def axialDerivative (f : MeridionalProfile) (p : ℝ × ℝ) : ℝ := fderiv ℝ f p (0, 1)

def meridionalJet (x : Space) : Space →L[ℝ] ℝ × ℝ :=
  ((2 * x 0) • coordinateProjection 0 + (2 * x 1) • coordinateProjection 1).prod
    (coordinateProjection 2)

theorem meridionalChart_hasFDerivAt (x : Space) :
    HasFDerivAt meridionalChart (meridionalJet x) x := by
  have h0 := (coordinateProjection 0).hasFDerivAt (x := x)
  have h1 := (coordinateProjection 1).hasFDerivAt (x := x)
  have h2 := (coordinateProjection 2).hasFDerivAt (x := x)
  convert ((h0.pow 2).add (h1.pow 2)).prodMk h2 using 1 <;>
    first | rfl | simp [meridionalChart, meridionalJet, coordinateProjection]

theorem meridionalJet_apply (x direction : Space) :
    meridionalJet x direction = (2 * (x 0 * direction 0 + x 1 * direction 1), direction 2) := by
  simp [meridionalJet, coordinateProjection]
  ring

theorem profile_fderiv_apply (f : MeridionalProfile) (p : ℝ × ℝ) (a b : ℝ) :
    fderiv ℝ f p (a, b) = a * radialDerivative f p + b * axialDerivative f p := by
  rw [show (a,b) = a • ((1 : ℝ), (0 : ℝ)) + b • ((0 : ℝ), (1 : ℝ)) by simp]
  rw [map_add, map_smul, map_smul]
  rfl

theorem profileLift_hasFDerivAt (f : MeridionalProfile) (x : Space)
    (hf : DifferentiableAt ℝ f (meridionalChart x)) :
    HasFDerivAt (fun y ↦ f (meridionalChart y))
      ((fderiv ℝ f (meridionalChart x)).comp (meridionalJet x)) x :=
  hf.hasFDerivAt.comp x (meridionalChart_hasFDerivAt x)

theorem profileLift_fderiv_apply (f : MeridionalProfile) (x direction : Space)
    (hf : DifferentiableAt ℝ f (meridionalChart x)) :
    fderiv ℝ (fun y ↦ f (meridionalChart y)) x direction =
      2 * (x 0 * direction 0 + x 1 * direction 1) * radialDerivative f (meridionalChart x)
        + direction 2 * axialDerivative f (meridionalChart x) := by
  rw [(profileLift_hasFDerivAt f x hf).fderiv, ContinuousLinearMap.comp_apply,
    meridionalJet_apply, profile_fderiv_apply]

def assemble (a b c : ℝ) : Space :=
  a • EuclideanSpace.single 0 1 + b • EuclideanSpace.single 1 1 + c • EuclideanSpace.single 2 1

@[simp] theorem assemble_zero (a b c : ℝ) : assemble a b c 0 = a := by simp [assemble]
@[simp] theorem assemble_one (a b c : ℝ) : assemble a b c 1 = b := by simp [assemble]
@[simp] theorem assemble_two (a b c : ℝ) : assemble a b c 2 = c := by simp [assemble]

def axisymmetricVelocity (V Omega W : MeridionalProfile) : InitialVelocity := fun x ↦
  assemble (x 0 * V (meridionalChart x) - x 1 * Omega (meridionalChart x))
    (x 1 * V (meridionalChart x) + x 0 * Omega (meridionalChart x)) (W (meridionalChart x))

def profileJet (f : MeridionalProfile) (x direction : Space) : ℝ :=
  2 * (x 0 * direction 0 + x 1 * direction 1) * radialDerivative f (meridionalChart x)
    + direction 2 * axialDerivative f (meridionalChart x)

/-- The actual Cartesian derivative retains the meridional source jet and the rotation carrier. -/
theorem fderiv_axisymmetricVelocity_apply (V Omega W : MeridionalProfile) (x direction : Space)
    (hV : DifferentiableAt ℝ V (meridionalChart x))
    (hOmega : DifferentiableAt ℝ Omega (meridionalChart x))
    (hW : DifferentiableAt ℝ W (meridionalChart x)) :
    fderiv ℝ (axisymmetricVelocity V Omega W) x direction =
      assemble
        (direction 0 * V (meridionalChart x) + x 0 * profileJet V x direction
          - direction 1 * Omega (meridionalChart x) - x 1 * profileJet Omega x direction)
        (direction 1 * V (meridionalChart x) + x 1 * profileJet V x direction
          + direction 0 * Omega (meridionalChart x) + x 0 * profileJet Omega x direction)
        (profileJet W x direction) := by
  have h0 := (coordinateProjection 0).hasFDerivAt (x := x)
  have h1 := (coordinateProjection 1).hasFDerivAt (x := x)
  have hVl := profileLift_hasFDerivAt V x hV
  have hOl := profileLift_hasFDerivAt Omega x hOmega
  have hWl := profileLift_hasFDerivAt W x hW
  have ha := (h0.mul hVl).sub (h1.mul hOl)
  have hb := (h1.mul hVl).add (h0.mul hOl)
  have hfield := ((ha.smul_const (EuclideanSpace.single (0 : Fin 3) (1 : ℝ) : Space)).add
    (hb.smul_const (EuclideanSpace.single (1 : Fin 3) (1 : ℝ) : Space))).add
      (hWl.smul_const (EuclideanSpace.single (2 : Fin 3) (1 : ℝ) : Space))
  change HasFDerivAt (axisymmetricVelocity V Omega W) _ x at hfield
  rw [hfield.fderiv]
  ext i
  fin_cases i <;>
    simp [assemble, profileJet, coordinateProjection, ContinuousLinearMap.comp_apply, meridionalJet_apply,
      profile_fderiv_apply] <;> ring

theorem divergence_axisymmetricVelocity (V Omega W : MeridionalProfile) (x : Space)
    (hV : DifferentiableAt ℝ V (meridionalChart x))
    (hOmega : DifferentiableAt ℝ Omega (meridionalChart x))
    (hW : DifferentiableAt ℝ W (meridionalChart x)) :
    divergence (axisymmetricVelocity V Omega W) x =
      2 * V (meridionalChart x) + 2 * (meridionalChart x).1 * radialDerivative V (meridionalChart x)
        + axialDerivative W (meridionalChart x) := by
  rw [← sum_coordinate_fderiv_eq_divergence]
  simp_rw [ContinuousLinearMap.comp_apply,
    fderiv_axisymmetricVelocity_apply V Omega W x _ hV hOmega hW,
    equiv_symm_single_eq_basisFun, EuclideanSpace.basisFun_apply]
  simp [Fin.sum_univ_succ, profileJet, meridionalChart]
  ring

def radialMomentum (alpha beta : ℝ) (V Omega W : MeridionalProfile) (p : ℝ × ℝ) : ℝ :=
  (alpha + beta) * V p + (W p + beta * p.2) * axialDerivative V p
    + 2 * p.1 * (V p + beta) * radialDerivative V p + V p ^ 2 - Omega p ^ 2

def swirlMomentum (alpha beta : ℝ) (V Omega W : MeridionalProfile) (p : ℝ × ℝ) : ℝ :=
  (alpha + beta + 2 * V p) * Omega p + (W p + beta * p.2) * axialDerivative Omega p
    + 2 * p.1 * (V p + beta) * radialDerivative Omega p

def axialMomentum (alpha beta : ℝ) (V Omega W : MeridionalProfile) (p : ℝ × ℝ) : ℝ :=
  alpha * W p + (W p + beta * p.2) * axialDerivative W p
    + 2 * p.1 * (V p + beta) * radialDerivative W p

/-- The normalized Euler momentum before pressure, as the exact Cartesian field of three
meridional source coefficients. No cylindrical division is used at the axis. -/
theorem normalizedMomentum_axisymmetricVelocity
    (alpha beta : ℝ) (V Omega W : MeridionalProfile) (x : Space)
    (hV : DifferentiableAt ℝ V (meridionalChart x))
    (hOmega : DifferentiableAt ℝ Omega (meridionalChart x))
    (hW : DifferentiableAt ℝ W (meridionalChart x)) :
    fderiv ℝ (axisymmetricVelocity V Omega W) x (axisymmetricVelocity V Omega W x)
      + beta • fderiv ℝ (axisymmetricVelocity V Omega W) x x
      + alpha • axisymmetricVelocity V Omega W x =
    assemble
      (x 0 * radialMomentum alpha beta V Omega W (meridionalChart x)
        - x 1 * swirlMomentum alpha beta V Omega W (meridionalChart x))
      (x 1 * radialMomentum alpha beta V Omega W (meridionalChart x)
        + x 0 * swirlMomentum alpha beta V Omega W (meridionalChart x))
      (axialMomentum alpha beta V Omega W (meridionalChart x)) := by
  rw [fderiv_axisymmetricVelocity_apply V Omega W x _ hV hOmega hW,
    fderiv_axisymmetricVelocity_apply V Omega W x x hV hOmega hW]
  ext i
  fin_cases i <;>
    simp [axisymmetricVelocity, assemble, profileJet, radialMomentum, swirlMomentum,
      axialMomentum, meridionalChart] <;> ring

theorem gradient_axisymmetricPressure (P : MeridionalProfile) (x : Space)
    (hP : DifferentiableAt ℝ P (meridionalChart x)) :
    gradient (fun y ↦ P (meridionalChart y)) x =
      assemble (2 * x 0 * radialDerivative P (meridionalChart x))
        (2 * x 1 * radialDerivative P (meridionalChart x)) (axialDerivative P (meridionalChart x)) := by
  apply ext_inner_right ℝ
  intro direction
  rw [inner_gradient_left, profileLift_fderiv_apply P x direction hP]
  simp [assemble, inner_add_left, real_inner_smul_left, PiLp.inner_apply, Fin.sum_univ_succ]
  ring

/-- Curl keeps the radial pressure compatibility current and the complete swirl derivative. -/
theorem vorticityAt_axisymmetricVelocity (V Omega W : MeridionalProfile) (x : Space)
    (hV : DifferentiableAt ℝ V (meridionalChart x))
    (hOmega : DifferentiableAt ℝ Omega (meridionalChart x))
    (hW : DifferentiableAt ℝ W (meridionalChart x)) :
    vorticityAt (axisymmetricVelocity V Omega W) x =
      assemble
        (x 1 * (2 * radialDerivative W (meridionalChart x) - axialDerivative V (meridionalChart x))
          - x 0 * axialDerivative Omega (meridionalChart x))
        (x 0 * (axialDerivative V (meridionalChart x) - 2 * radialDerivative W (meridionalChart x))
          - x 1 * axialDerivative Omega (meridionalChart x))
        (2 * Omega (meridionalChart x) +
          2 * (meridionalChart x).1 * radialDerivative Omega (meridionalChart x)) := by
  ext i
  fin_cases i <;>
    simp [vorticityAt, velocityJacobianAt, curlFromJacobian, jacobianMatrix_apply,
      fderiv_axisymmetricVelocity_apply V Omega W x _ hV hOmega hW,
      EuclideanSpace.basisFun_apply, profileJet, assemble, meridionalChart] <;> ring

/-- Away from the axis the complete Cartesian receiver reconstructs all three scalar defects. -/
theorem rotatingCarrier_eq_zero_iff (x : Space) (A C B : ℝ)
    (haxis : x 0 ^ 2 + x 1 ^ 2 ≠ 0) :
    assemble (x 0 * A - x 1 * C) (x 1 * A + x 0 * C) B = 0 ↔
      A = 0 ∧ C = 0 ∧ B = 0 := by
  constructor
  · intro h
    have h0 := congrArg (fun v : Space ↦ v 0) h
    have h1 := congrArg (fun v : Space ↦ v 1) h
    have h2 := congrArg (fun v : Space ↦ v 2) h
    simp only [assemble_zero, assemble_one, assemble_two, PiLp.zero_apply] at h0 h1 h2
    have hA : (x 0 ^ 2 + x 1 ^ 2) * A = 0 := by
      linear_combination x 0 * h0 + x 1 * h1
    have hC : (x 0 ^ 2 + x 1 ^ 2) * C = 0 := by
      linear_combination x 0 * h1 - x 1 * h0
    exact ⟨(mul_eq_zero.mp hA).resolve_left haxis, (mul_eq_zero.mp hC).resolve_left haxis, h2⟩
  · rintro ⟨rfl, rfl, rfl⟩
    simp [assemble]

/-- At the axis the same value receiver retains an entire radial/swirl fibre. -/
theorem rotatingCarrier_axis_eq_zero_iff (z A C B : ℝ) :
    assemble ((assemble 0 0 z) 0 * A - (assemble 0 0 z) 1 * C)
      ((assemble 0 0 z) 1 * A + (assemble 0 0 z) 0 * C) B = 0 ↔ B = 0 := by
  simp [assemble, smul_eq_zero]

/-- A derivative receiver recovers swirl at an axis where the horizontal value receiver vanishes. -/
theorem vorticityAt_axisymmetricVelocity_axis (V Omega W : MeridionalProfile) (z : ℝ)
    (hV : DifferentiableAt ℝ V (0, z))
    (hOmega : DifferentiableAt ℝ Omega (0, z))
    (hW : DifferentiableAt ℝ W (0, z)) :
    vorticityAt (axisymmetricVelocity V Omega W) (assemble 0 0 z) = assemble 0 0 (2 * Omega (0, z)) := by
  have hchart : meridionalChart (assemble 0 0 z) = (0, z) := by simp [meridionalChart]
  rw [vorticityAt_axisymmetricVelocity V Omega W (assemble 0 0 z)
    (by simpa [hchart] using hV) (by simpa [hchart] using hOmega) (by simpa [hchart] using hW)]
  simp [hchart]

#print axioms meridionalChart_hasFDerivAt
#print axioms fderiv_axisymmetricVelocity_apply
#print axioms divergence_axisymmetricVelocity
#print axioms normalizedMomentum_axisymmetricVelocity
#print axioms gradient_axisymmetricPressure
#print axioms vorticityAt_axisymmetricVelocity
#print axioms rotatingCarrier_eq_zero_iff
#print axioms rotatingCarrier_axis_eq_zero_iff
#print axioms vorticityAt_axisymmetricVelocity_axis

end Soma.Holonics.Millennium.NavierStokesAxisymmetricChart
