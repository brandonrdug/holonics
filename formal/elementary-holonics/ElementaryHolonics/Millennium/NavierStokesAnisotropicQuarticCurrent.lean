import ElementaryHolonics.Millennium.NavierStokesQuarticPressureCurrent
import ElementaryHolonics.Millennium.NavierStokesAnisotropicFrame

/-!
# Anisotropic quartic pressure current

The axial harmonic mode is deformed by a factored parameter `epsilon`; applying the corresponding
diagonal metric keeps its negative gradient a regular cubic current, including at `epsilon = 0`.
-/

noncomputable section

open ContDiff Function Set Topology InnerProductSpace
open scoped Laplacian

namespace Soma.Holonics.Millennium.NavierStokesAnisotropicQuarticCurrent

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesAxisymmetricChart
open Soma.Holonics.Millennium.NavierStokesPeriodicEnergy
open Soma.Holonics.Millennium.NavierStokesPeriodicCubeInterpolation
open Soma.Holonics.Millennium.NavierStokesPeriodicFlux
open Soma.Holonics.Millennium.NavierStokesQuarticPressureCurrent
open Soma.Holonics.Millennium.NavierStokesAnisotropicFrame
open Soma.Holonics.Millennium.NavierStokesVorticity

def anisotropicHax (epsilon : ℝ) (x : Space) : ℝ :=
  x 2 ^ 4 - 3 * epsilon * radiusSq x * x 2 ^ 2 +
    (3 / 8) * epsilon ^ 2 * radiusSq x ^ 2

def anisotropicQuarticPressure (epsilon D b c : ℝ) (x : Space) : ℝ :=
  D * anisotropicHax epsilon x + b * Hcos x + c * Hsin x

def regularAxialForce (epsilon : ℝ) : InitialVelocity := fun x ↦
  assemble
    (6 * x 0 * x 2 ^ 2 - (3 / 2) * epsilon * x 0 * radiusSq x)
    (6 * x 1 * x 2 ^ 2 - (3 / 2) * epsilon * x 1 * radiusSq x)
    (-4 * x 2 ^ 3 + 6 * epsilon * radiusSq x * x 2)

def axialFrameCurrent : InitialVelocity := fun x ↦
  assemble
    (-(3 / 2) * x 0 * radiusSq x)
    (-(3 / 2) * x 1 * radiusSq x)
    (6 * radiusSq x * x 2)

def anisotropicQuarticCurrent (epsilon kappa b c : ℝ) : InitialVelocity :=
  fun x ↦ kappa • regularAxialForce epsilon x + quarticPressureCurrent 0 b c x

theorem regularAxialForce_decompose (epsilon : ℝ) :
    regularAxialForce epsilon = regularAxialForce 0 + epsilon • axialFrameCurrent := by
  funext x
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [regularAxialForce, axialFrameCurrent, assemble, radiusSq] <;> ring

theorem quarticPressureCurrent_angular_decompose (b c : ℝ) :
    quarticPressureCurrent 0 b c =
      b • quarticPressureCurrent 0 1 0 + c • quarticPressureCurrent 0 0 1 := by
  funext x
  apply PiLp.ext
  intro i
  fin_cases i <;>
    simp [quarticPressureCurrent, gradient_quarticPressure, assemble, radiusSq] <;> ring

theorem anisotropicQuarticCurrent_decompose
    (epsilon kappa b c : ℝ) (x : Space) :
    anisotropicQuarticCurrent epsilon kappa b c x =
      kappa • regularAxialForce 0 x +
        (kappa * epsilon) • axialFrameCurrent x +
        b • quarticPressureCurrent 0 1 0 x +
        c • quarticPressureCurrent 0 0 1 x := by
  rw [anisotropicQuarticCurrent, regularAxialForce_decompose,
    quarticPressureCurrent_angular_decompose]
  simp only [Pi.add_apply, Pi.smul_apply, smul_add, smul_smul]
  abel

/-- Differentiation retains the connection current of the moving aspect basis. -/
theorem anisotropicQuarticCurrent_hasDerivWithinAt
    (epsilon kappa b c : ℝ → ℝ) (s : Set ℝ) (τ epsilonJet kappaJet bJet cJet : ℝ)
    (he : HasDerivWithinAt epsilon epsilonJet s τ)
    (hk : HasDerivWithinAt kappa kappaJet s τ)
    (hb : HasDerivWithinAt b bJet s τ) (hc : HasDerivWithinAt c cJet s τ) (x : Space) :
    HasDerivWithinAt (fun t ↦ anisotropicQuarticCurrent (epsilon t) (kappa t) (b t) (c t) x)
      (kappaJet • regularAxialForce (epsilon τ) x +
        (kappa τ * epsilonJet) • axialFrameCurrent x +
        bJet • quarticPressureCurrent 0 1 0 x + cJet • quarticPressureCurrent 0 0 1 x) s τ := by
  have h := (((hk.smul_const (regularAxialForce 0 x)).add
    ((hk.fun_mul he).smul_const (axialFrameCurrent x))).add
      (hb.smul_const (quarticPressureCurrent 0 1 0 x))).add
        (hc.smul_const (quarticPressureCurrent 0 0 1 x))
  convert h using 1 <;> try rfl
  · funext t
    exact anisotropicQuarticCurrent_decompose (epsilon t) (kappa t) (b t) (c t) x
  · rw [regularAxialForce_decompose]
    simp only [Pi.add_apply, Pi.smul_apply, smul_add, smul_smul, add_smul]
    abel

theorem anisotropicQuarticCurrent_hasDerivAt
    (epsilon kappa b c : ℝ → ℝ) (τ epsilonJet kappaJet bJet cJet : ℝ)
    (he : HasDerivAt epsilon epsilonJet τ) (hk : HasDerivAt kappa kappaJet τ)
    (hb : HasDerivAt b bJet τ) (hc : HasDerivAt c cJet τ) (x : Space) :
    HasDerivAt (fun t ↦ anisotropicQuarticCurrent (epsilon t) (kappa t) (b t) (c t) x)
      (kappaJet • regularAxialForce (epsilon τ) x +
        (kappa τ * epsilonJet) • axialFrameCurrent x +
        bJet • quarticPressureCurrent 0 1 0 x + cJet • quarticPressureCurrent 0 0 1 x) τ := by
  exact (anisotropicQuarticCurrent_hasDerivWithinAt epsilon kappa b c Set.univ
    τ epsilonJet kappaJet bJet cJet he.hasDerivWithinAt hk.hasDerivWithinAt
      hb.hasDerivWithinAt hc.hasDerivWithinAt x).hasDerivAt Filter.univ_mem

def fiveTermQuarticPressure (A B C D E : ℝ) (x : Space) : ℝ :=
  A * (x 0 ^ 4 + x 1 ^ 4) + B * x 0 ^ 2 * x 1 ^ 2 +
    C * radiusSq x * x 2 ^ 2 + D * x 2 ^ 4 + E * Hsin x

theorem fiveTermQuarticPressure_split (A B C D E epsilon : ℝ) (x : Space) :
    fiveTermQuarticPressure A B C D E x =
      ((6 * A + B - 3 * epsilon ^ 2 * D) / 8) * radiusSq x ^ 2 +
        (C + 3 * epsilon * D) * radiusSq x * x 2 ^ 2 +
        D * anisotropicHax epsilon x +
        ((2 * A - B) / 8) * Hcos x + E * Hsin x := by
  unfold fiveTermQuarticPressure anisotropicHax Hcos Hsin radiusSq
  ring

theorem anisotropicQuarticPressure_contDiff (epsilon D b c : ℝ) :
    ContDiff ℝ ∞ (anisotropicQuarticPressure epsilon D b c) := by
  unfold anisotropicQuarticPressure anisotropicHax Hcos Hsin radiusSq
  fun_prop

private theorem coordinate_fderiv (i : Fin 3) (x : Space) :
    fderiv ℝ (fun y : Space ↦ y i) x = EuclideanSpace.proj i := by
  convert (EuclideanSpace.proj i : Space →L[ℝ] ℝ).fderiv (x := x) using 1 <;> rfl

theorem anisotropicQuarticPressure_fderiv (epsilon D b c : ℝ) (x : Space) :
    fderiv ℝ (anisotropicQuarticPressure epsilon D b c) x =
      (D * (-6 * epsilon * x 0 * x 2 ^ 2 +
          (3 / 2) * epsilon ^ 2 * x 0 * radiusSq x) +
        b * (4 * x 0 ^ 3 - 12 * x 0 * x 1 ^ 2) +
        c * (3 * x 0 ^ 2 * x 1 - x 1 ^ 3)) • coordinateProjection 0 +
      (D * (-6 * epsilon * x 1 * x 2 ^ 2 +
          (3 / 2) * epsilon ^ 2 * x 1 * radiusSq x) +
        b * (4 * x 1 ^ 3 - 12 * x 0 ^ 2 * x 1) +
        c * (x 0 ^ 3 - 3 * x 0 * x 1 ^ 2)) • coordinateProjection 1 +
      (D * (4 * x 2 ^ 3 - 6 * epsilon * radiusSq x * x 2)) • coordinateProjection 2 := by
  unfold anisotropicQuarticPressure anisotropicHax Hcos Hsin radiusSq
  ext direction
  simp (disch := fun_prop) only [fderiv_fun_add, fderiv_fun_sub, fderiv_fun_mul,
    fderiv_fun_pow, coordinate_fderiv, fderiv_const]
  simp [coordinateProjection]
  ring

theorem gradient_anisotropicQuarticPressure (epsilon D b c : ℝ) (x : Space) :
    gradient (anisotropicQuarticPressure epsilon D b c) x =
      assemble
        (D * (-6 * epsilon * x 0 * x 2 ^ 2 + (3 / 2) * epsilon ^ 2 * x 0 * radiusSq x) +
          b * (4 * x 0 ^ 3 - 12 * x 0 * x 1 ^ 2) +
          c * (3 * x 0 ^ 2 * x 1 - x 1 ^ 3))
        (D * (-6 * epsilon * x 1 * x 2 ^ 2 + (3 / 2) * epsilon ^ 2 * x 1 * radiusSq x) +
          b * (4 * x 1 ^ 3 - 12 * x 0 ^ 2 * x 1) +
          c * (x 0 ^ 3 - 3 * x 0 * x 1 ^ 2))
        (D * (4 * x 2 ^ 3 - 6 * epsilon * radiusSq x * x 2)) := by
  apply ext_inner_right ℝ
  intro direction
  rw [inner_gradient_left, anisotropicQuarticPressure_fderiv]
  simp [assemble, inner_add_left, real_inner_smul_left, PiLp.inner_apply]
  ring

theorem neg_diagonalMetric_gradient_eq_current (epsilon D b c : ℝ) (x : Space) :
    -(diagonalFrame 1 epsilon) (gradient (anisotropicQuarticPressure epsilon D b c) x) =
      (epsilon * D) • regularAxialForce epsilon x + quarticPressureCurrent 0 b c x := by
  rw [gradient_anisotropicQuarticPressure]
  simp [regularAxialForce, quarticPressureCurrent, gradient_quarticPressure,
    diagonalFrame_apply, assemble, radiusSq]
  ext i
  fin_cases i <;> simp [regularAxialForce, quarticPressureCurrent,
    gradient_quarticPressure, assemble, radiusSq] <;> ring

theorem anisotropicQuarticCurrent_zero (epsilon kappa b c : ℝ) :
    anisotropicQuarticCurrent epsilon kappa b c 0 = 0 := by
  have hforce : regularAxialForce epsilon 0 = 0 := by
    simp [regularAxialForce, radiusSq, assemble]
  simp [anisotropicQuarticCurrent, hforce, quarticPressureCurrent_zero]

theorem anisotropicQuarticCurrent_contDiff (epsilon kappa b c : ℝ) :
    ContDiff ℝ ∞ (anisotropicQuarticCurrent epsilon kappa b c) := by
  have hreg : ContDiff ℝ ∞ (regularAxialForce epsilon) := by
    unfold regularAxialForce radiusSq assemble
    fun_prop
  exact (hreg.const_smul kappa).add (quarticPressureCurrent_contDiff 0 b c)

theorem anisotropicQuarticCurrent_eq_zero_iff (epsilon kappa b c : ℝ) :
    anisotropicQuarticCurrent epsilon kappa b c = 0 ↔
      kappa = 0 ∧ b = 0 ∧ c = 0 := by
  constructor
  · intro h
    have hz := congrArg (fun f : InitialVelocity ↦ f (assemble 0 0 1) 2) h
    have hx := congrArg (fun f : InitialVelocity ↦ f (assemble 1 0 0) 0) h
    have hy := congrArg (fun f : InitialVelocity ↦ f (assemble 1 0 0) 1) h
    simp [anisotropicQuarticCurrent, regularAxialForce, quarticPressureCurrent,
      gradient_quarticPressure, assemble, radiusSq] at hz hx hy
    have hk : kappa = 0 := by linarith
    have hquartic : quarticPressureCurrent 0 b c = 0 := by
      funext x
      have hx' := congrArg (fun f : InitialVelocity ↦ f x) h
      rw [hk] at hx'
      simpa [anisotropicQuarticCurrent] using hx'
    rcases (quarticPressureCurrent_eq_zero_iff 0 b c).mp hquartic with ⟨_, hb, hc⟩
    exact ⟨hk, hb, hc⟩
  · rintro ⟨rfl, rfl, rfl⟩
    funext x
    simp [anisotropicQuarticCurrent, quarticPressureCurrent, gradient_quarticPressure,
      regularAxialForce, assemble, radiusSq]

theorem divergence_regularAxialForce (epsilon : ℝ) (x : Space) :
    divergence (regularAxialForce epsilon) x = 0 := by
  have hreg : ContDiff ℝ 1 (regularAxialForce epsilon) := by
    unfold regularAxialForce radiusSq assemble
    fun_prop
  rw [← divergenceFromJacobian_velocityJacobianAt]
  simp only [divergenceFromJacobian, Fin.sum_univ_three, velocityJacobianAt,
    jacobianMatrix_apply]
  rw [← fderiv_component_apply _ hreg x _ 0, ← fderiv_component_apply _ hreg x _ 1,
    ← fderiv_component_apply _ hreg x _ 2]
  simp (disch := fun_prop) [regularAxialForce, radiusSq, assemble,
    coordinateProjection, fderiv_fun_add, fderiv_fun_sub, fderiv_fun_mul,
    fderiv_fun_pow, coordinate_fderiv, fderiv_const, EuclideanSpace.basisFun_apply]
  ring

theorem regularAxialForce_fderiv_zero (epsilon : ℝ) :
    fderiv ℝ (regularAxialForce epsilon) 0 = 0 := by
  have hreg : ContDiff ℝ 1 (regularAxialForce epsilon) := by
    unfold regularAxialForce radiusSq assemble
    fun_prop
  ext direction component
  change (fderiv ℝ (regularAxialForce epsilon) 0 direction) component = 0
  rw [← fderiv_component_apply _ hreg 0 direction component]
  simp_rw [regularAxialForce]
  fin_cases component <;>
    simp (disch := fun_prop) [assemble, radiusSq, coordinate_fderiv,
      fderiv_fun_add, fderiv_fun_sub, fderiv_fun_mul, fderiv_fun_pow,
      fderiv_const] <;> norm_num

theorem anisotropicQuarticCurrent_fderiv_zero (epsilon kappa b c : ℝ) :
    fderiv ℝ (anisotropicQuarticCurrent epsilon kappa b c) 0 = 0 := by
  have hreg := regularAxialForce_fderiv_zero epsilon
  have hquartic := quarticPressureCurrent_fderiv_zero 0 b c
  have hregSmooth : ContDiff ℝ 1 (regularAxialForce epsilon) := by
    unfold regularAxialForce radiusSq assemble
    fun_prop
  have hquarticSmooth : ContDiff ℝ 1 (quarticPressureCurrent 0 b c) :=
    (quarticPressureCurrent_contDiff 0 b c).of_le (WithTop.coe_le_coe.mpr le_top)
  unfold anisotropicQuarticCurrent
  rw [fderiv_fun_add]
  · rw [fderiv_fun_smul]
    · simp [hreg, hquartic]
    · exact differentiableAt_const (c := kappa)
    · exact (hregSmooth.differentiable (by norm_num)) 0
  · exact ((hregSmooth.const_smul kappa).differentiable (by norm_num)) 0
  · exact (hquarticSmooth.differentiable (by norm_num)) 0

theorem divergence_anisotropicQuarticCurrent (epsilon kappa b c : ℝ) (x : Space) :
    divergence (anisotropicQuarticCurrent epsilon kappa b c) x = 0 := by
  have hreg : ContDiff ℝ 1 (regularAxialForce epsilon) := by
    unfold regularAxialForce radiusSq assemble
    fun_prop
  have hquartic : ContDiff ℝ 1 (quarticPressureCurrent 0 b c) :=
    (quarticPressureCurrent_contDiff 0 b c).of_le (WithTop.coe_le_coe.mpr le_top)
  have hreg0 : (fderiv ℝ (regularAxialForce epsilon) x).trace ℝ Space = 0 := by
    simpa [divergence] using divergence_regularAxialForce epsilon x
  have hquartic0 : (fderiv ℝ (quarticPressureCurrent 0 b c) x).trace ℝ Space = 0 := by
    simpa [divergence] using divergence_quarticPressureCurrent 0 b c x
  unfold anisotropicQuarticCurrent divergence
  rw [fderiv_fun_add ((hreg.const_smul kappa).differentiable (by norm_num) x)
    (hquartic.differentiable (by norm_num) x)]
  rw [fderiv_fun_smul (differentiableAt_const (c := kappa))
    (hreg.differentiable (by norm_num) x)]
  simp [fderiv_const]
  rw [hreg0, hquartic0]
  simp

/-- The two particular coefficients retain the complete trace/source of this quartic family. -/
def quarticTracePressure (L M : ℝ) (x : Space) : ℝ :=
  L * radiusSq x ^ 2 + M * radiusSq x * x 2 ^ 2

theorem gradient_quarticTracePressure (L M : ℝ) (x : Space) :
    gradient (quarticTracePressure L M) x =
      assemble (4 * L * x 0 * radiusSq x + 2 * M * x 0 * x 2 ^ 2)
        (4 * L * x 1 * radiusSq x + 2 * M * x 1 * x 2 ^ 2)
        (2 * M * radiusSq x * x 2) := by
  apply ext_inner_right ℝ
  intro direction
  rw [inner_gradient_left]
  unfold quarticTracePressure radiusSq
  simp (disch := fun_prop) only [fderiv_fun_add, fderiv_fun_mul, fderiv_fun_pow,
    coordinate_fderiv, fderiv_const]
  simp [assemble, inner_add_left, real_inner_smul_left, PiLp.inner_apply, Fin.sum_univ_three]
  ring

theorem divergence_metric_gradient_quarticTracePressure (epsilon L M : ℝ) (x : Space) :
    divergence (fun y ↦ diagonalFrame 1 epsilon (gradient (quarticTracePressure L M) y)) x =
      (16 * L + 2 * epsilon * M) * radiusSq x + 4 * M * x 2 ^ 2 := by
  let F : InitialVelocity := fun y ↦
    assemble (4 * L * y 0 * radiusSq y + 2 * M * y 0 * y 2 ^ 2)
      (4 * L * y 1 * radiusSq y + 2 * M * y 1 * y 2 ^ 2)
      (2 * epsilon * M * radiusSq y * y 2)
  have heq : (fun y ↦ diagonalFrame 1 epsilon (gradient (quarticTracePressure L M) y)) = F := by
    funext y
    rw [gradient_quarticTracePressure, diagonalFrame_apply]
    ext i
    fin_cases i <;> simp [F, assemble] <;> ring
  rw [heq]
  have hF : ContDiff ℝ 1 F := by unfold F radiusSq assemble; fun_prop
  rw [← divergenceFromJacobian_velocityJacobianAt]
  simp only [divergenceFromJacobian, Fin.sum_univ_three, velocityJacobianAt, jacobianMatrix_apply]
  rw [← fderiv_component_apply _ hF x _ 0, ← fderiv_component_apply _ hF x _ 1,
    ← fderiv_component_apply _ hF x _ 2]
  unfold F radiusSq
  simp (disch := fun_prop) [assemble, fderiv_fun_add, fderiv_fun_mul, fderiv_fun_pow,
    coordinate_fderiv, fderiv_const, EuclideanSpace.basisFun_apply]
  ring

/-- The raw pressure chart gains an axial null fibre when its metric factor is zero. -/
theorem raw_harmonic_force_eq_zero_iff (epsilon D b c : ℝ) :
    (fun x ↦ -diagonalFrame 1 epsilon (gradient (anisotropicQuarticPressure epsilon D b c) x)) = 0 ↔
      epsilon * D = 0 ∧ b = 0 ∧ c = 0 := by
  have heq : (fun x ↦ -diagonalFrame 1 epsilon
      (gradient (anisotropicQuarticPressure epsilon D b c) x)) =
      anisotropicQuarticCurrent epsilon (epsilon * D) b c :=
    funext (neg_diagonalMetric_gradient_eq_current epsilon D b c)
  rw [heq, anisotropicQuarticCurrent_eq_zero_iff]

def horizontalTraceForce : InitialVelocity := fun x ↦
  assemble (-4 * x 0 * radiusSq x) (-4 * x 1 * radiusSq x) 0

def mixedTraceForce (epsilon : ℝ) : InitialVelocity := fun x ↦
  assemble (-2 * x 0 * x 2 ^ 2) (-2 * x 1 * x 2 ^ 2) (-2 * epsilon * radiusSq x * x 2)

def mixedTraceConnection : InitialVelocity := fun x ↦
  assemble 0 0 (-2 * radiusSq x * x 2)

def fullQuarticPressureForce (epsilon L M kappa b c : ℝ) : InitialVelocity := fun x ↦
  L • horizontalTraceForce x + M • mixedTraceForce epsilon x +
    anisotropicQuarticCurrent epsilon kappa b c x

theorem mixedTraceForce_decompose (epsilon : ℝ) :
    mixedTraceForce epsilon = mixedTraceForce 0 + epsilon • mixedTraceConnection := by
  funext x
  ext i
  fin_cases i <;> simp [mixedTraceForce, mixedTraceConnection, assemble] <;> ring

theorem neg_metric_gradient_quarticTracePressure (epsilon L M : ℝ) (x : Space) :
    -diagonalFrame 1 epsilon (gradient (quarticTracePressure L M) x) =
      L • horizontalTraceForce x + M • mixedTraceForce epsilon x := by
  rw [gradient_quarticTracePressure, diagonalFrame_apply]
  ext i
  fin_cases i <;> simp [horizontalTraceForce, mixedTraceForce, assemble] <;> ring

/-- The complete pressure force includes both source terms and all harmonic terms. -/
theorem fullQuarticPressureForce_eq_negative_gradient
    (epsilon L M D b c : ℝ) (x : Space) :
    -diagonalFrame 1 epsilon
        (gradient (fun y ↦ quarticTracePressure L M y + anisotropicQuarticPressure epsilon D b c y) x) =
      fullQuarticPressureForce epsilon L M (epsilon * D) b c x := by
  have ht : ContDiff ℝ 1 (quarticTracePressure L M) := by
    unfold quarticTracePressure radiusSq
    fun_prop
  have hh : ContDiff ℝ 1 (anisotropicQuarticPressure epsilon D b c) :=
    (anisotropicQuarticPressure_contDiff epsilon D b c).of_le (WithTop.coe_le_coe.mpr le_top)
  have hgrad : gradient
      (fun y ↦ quarticTracePressure L M y + anisotropicQuarticPressure epsilon D b c y) x =
      gradient (quarticTracePressure L M) x + gradient (anisotropicQuarticPressure epsilon D b c) x := by
    unfold gradient
    rw [fderiv_fun_add (ht.differentiable (by norm_num) x) (hh.differentiable (by norm_num) x), map_add]
  rw [hgrad, map_add, neg_add, neg_metric_gradient_quarticTracePressure,
    neg_diagonalMetric_gradient_eq_current]
  rfl

theorem fullQuarticPressureForce_hasDerivWithinAt
    (epsilon L M kappa b c : ℝ → ℝ) (s : Set ℝ)
    (τ epsilonJet LJet MJet kappaJet bJet cJet : ℝ)
    (he : HasDerivWithinAt epsilon epsilonJet s τ)
    (hL : HasDerivWithinAt L LJet s τ) (hM : HasDerivWithinAt M MJet s τ)
    (hk : HasDerivWithinAt kappa kappaJet s τ)
    (hb : HasDerivWithinAt b bJet s τ) (hc : HasDerivWithinAt c cJet s τ) (x : Space) :
    HasDerivWithinAt
      (fun t ↦ fullQuarticPressureForce (epsilon t) (L t) (M t) (kappa t) (b t) (c t) x)
      (fullQuarticPressureForce (epsilon τ) LJet MJet kappaJet bJet cJet x +
        epsilonJet • (M τ • mixedTraceConnection x + kappa τ • axialFrameCurrent x)) s τ := by
  have htrace := ((hL.smul_const (horizontalTraceForce x)).add
    (hM.smul_const (mixedTraceForce 0 x))).add
      ((hM.fun_mul he).smul_const (mixedTraceConnection x))
  have hh := anisotropicQuarticCurrent_hasDerivWithinAt epsilon kappa b c s
    τ epsilonJet kappaJet bJet cJet he hk hb hc x
  have h := htrace.add hh
  convert h using 1 <;> try rfl
  · funext t
    rw [fullQuarticPressureForce, mixedTraceForce_decompose]
    simp only [Pi.add_apply, Pi.smul_apply, smul_add, smul_smul]
    abel
  · unfold fullQuarticPressureForce anisotropicQuarticCurrent
    rw [mixedTraceForce_decompose, quarticPressureCurrent_angular_decompose]
    simp only [Pi.add_apply, Pi.smul_apply, smul_add, smul_smul, add_smul]
    module

#print axioms anisotropicQuarticPressure_contDiff
#print axioms anisotropicQuarticCurrent_hasDerivWithinAt
#print axioms anisotropicQuarticCurrent_hasDerivAt
#print axioms fiveTermQuarticPressure_split
#print axioms anisotropicQuarticPressure_fderiv
#print axioms gradient_anisotropicQuarticPressure
#print axioms neg_diagonalMetric_gradient_eq_current
#print axioms anisotropicQuarticCurrent_zero
#print axioms anisotropicQuarticCurrent_contDiff
#print axioms anisotropicQuarticCurrent_eq_zero_iff
#print axioms divergence_regularAxialForce
#print axioms regularAxialForce_fderiv_zero
#print axioms anisotropicQuarticCurrent_fderiv_zero
#print axioms divergence_anisotropicQuarticCurrent
#print axioms gradient_quarticTracePressure
#print axioms divergence_metric_gradient_quarticTracePressure
#print axioms raw_harmonic_force_eq_zero_iff
#print axioms fullQuarticPressureForce_eq_negative_gradient
#print axioms fullQuarticPressureForce_hasDerivWithinAt

end Soma.Holonics.Millennium.NavierStokesAnisotropicQuarticCurrent
