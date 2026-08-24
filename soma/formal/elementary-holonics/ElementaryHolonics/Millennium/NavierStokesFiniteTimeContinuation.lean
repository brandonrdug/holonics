import ElementaryHolonics.Millennium.NavierStokesFiniteTimeEnstrophy
import ElementaryHolonics.Millennium.NavierStokesVorticityControl

/-!
# Finite-time vorticity control and the continuation obstruction

Uniform interior Jacobian and curl-forcing bounds close the scalar enstrophy inequality on every
compact interval strictly inside a finite lifespan.  The concluding alternative keeps extension
past the terminal face separate from the estimate, exposing the exact continuation input that the
present formalization does not supply.
-/

noncomputable section

open ContDiff InnerProductSpace MeasureTheory Real Set
open scoped Laplacian

namespace Soma.Holonics.Millennium.NavierStokesFiniteTimeVorticity

open Soma.Holonics.Millennium
open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesFiniteTime
open Soma.Holonics.Millennium.NavierStokesPeriodicEnergy
open Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy
open Soma.Holonics.Millennium.NavierStokesPeriodicFlux
open Soma.Holonics.Millennium.NavierStokesVorticity
open Soma.Holonics.Millennium.NavierStokesVorticityControl

/-! ## Finite-interval control and its remaining terminal fibre -/

/-- The vorticity-dissipation integrand is admitted on every interior finite-slab slice. -/
theorem periodicSolutionOn_vorticityDissipation_integrable
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : PeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) :
    IntegrableOn (fun x => ∑ i : Fin 3,
      ‖gradient (fun y => vorticityField velocity y t i) x‖ ^ 2) unitCube := by
  have hcubeCompact : IsCompact unitCube := by
    unfold unitCube
    exact (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr
      isCompact_Icc
  have homega : ContDiff ℝ 2 (fun x => vorticityField velocity x t) :=
    periodicSolutionOn_vorticityField_contDiff_two solution ht0 htT
  have hcomponent : ∀ i : Fin 3,
      ContDiff ℝ 2 (fun x => vorticityField velocity x t i) := by
    intro i
    simpa [Function.comp_def] using (EuclideanSpace.proj i).contDiff.comp homega
  have hintegrand : Continuous (fun x => ∑ i : Fin 3,
      ‖gradient (fun y => vorticityField velocity y t i) x‖ ^ 2) := by
    apply continuous_finset_sum
    intro i _hi
    exact (gradient_contDiff_one _ (hcomponent i)).norm_sq ℝ |>.continuous
  exact hintegrand.continuousOn.integrableOn_compact hcubeCompact

/-- The finite-slab viscous coefficient times dissipation is nonnegative for nonnegative
viscosity. -/
theorem periodicSolutionOn_viscousVorticityDissipation_nonneg
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : PeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) (hnu : 0 ≤ nu) :
    0 ≤ nu * periodicVorticityDissipation velocity t :=
  mul_nonneg hnu (periodicVorticityDissipation_nonneg velocity t
    (periodicSolutionOn_vorticityDissipation_integrable solution ht0 htT))

/-- Stretching work is integrable on every interior finite-slab slice. -/
theorem periodicSolutionOn_vortexStretching_integrable
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : PeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) :
    IntegrableOn (fun x =>
      inner ℝ
        (fderiv ℝ (fun y => velocity y t) x (vorticityField velocity x t))
        (vorticityField velocity x t)) unitCube := by
  have hcubeCompact : IsCompact unitCube := by
    unfold unitCube
    exact (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr
      isCompact_Icc
  have hu : ContDiff ℝ ∞ (fun x => velocity x t) :=
    smoothSolutionOn_velocitySpatialSmooth solution.toSmoothSolutionOn ht0 htT
  have homega : ContDiff ℝ 2 (fun x => vorticityField velocity x t) :=
    periodicSolutionOn_vorticityField_contDiff_two solution ht0 htT
  have hstretched : Continuous (fun x =>
      fderiv ℝ (fun y => velocity y t) x (vorticityField velocity x t)) :=
    (hu.continuous_fderiv_apply (by simp)).comp
      (continuous_id.prodMk homega.continuous)
  exact (hstretched.inner homega.continuous).continuousOn.integrableOn_compact
    hcubeCompact

/-- A uniform velocity-Jacobian bound controls finite-slab stretching by twice that bound times
enstrophy. -/
theorem periodicSolutionOn_vortexStretching_le_two_mul_jacobianBound_mul_enstrophy
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : PeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) (K : ℝ)
    (hK : ∀ x ∈ unitCube,
      ‖fderiv ℝ (fun y => velocity y t) x‖ ≤ K) :
    periodicVortexStretching velocity t ≤
      2 * K * periodicEnstrophy velocity t := by
  have hcubeCompact : IsCompact unitCube := by
    unfold unitCube
    exact (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr
      isCompact_Icc
  have hcubeMeasurable : MeasurableSet unitCube := hcubeCompact.measurableSet
  have homega : ContDiff ℝ 2 (fun x => vorticityField velocity x t) :=
    periodicSolutionOn_vorticityField_contDiff_two solution ht0 htT
  have hnormSqIntegrable : IntegrableOn
      (fun x => K * ‖vorticityField velocity x t‖ ^ 2) unitCube :=
    (continuous_const.mul (homega.continuous.norm.pow 2)).continuousOn
      |>.integrableOn_compact hcubeCompact
  have hstretchingIntegrable :=
    periodicSolutionOn_vortexStretching_integrable solution ht0 htT
  have huDiff : ∀ x, DifferentiableAt ℝ (fun y => velocity y t) x :=
    fun x => (smoothSolutionOn_velocitySpatialSmooth solution.toSmoothSolutionOn ht0 htT)
      |>.differentiable (by simp) x
  have hpoint : ∀ x ∈ unitCube,
      inner ℝ
          (fderiv ℝ (fun y => velocity y t) x (vorticityField velocity x t))
          (vorticityField velocity x t)
        ≤ K * ‖vorticityField velocity x t‖ ^ 2 := by
    intro x hx
    calc
      inner ℝ
          (fderiv ℝ (fun y => velocity y t) x (vorticityField velocity x t))
          (vorticityField velocity x t)
          ≤ |inner ℝ
              (fderiv ℝ (fun y => velocity y t) x (vorticityField velocity x t))
              (vorticityField velocity x t)| := le_abs_self _
      _ ≤ ‖fderiv ℝ (fun y => velocity y t) x‖ *
            ‖vorticityField velocity x t‖ ^ 2 :=
        abs_vortexStretching_le_jacobianNorm_mul_vorticityNormSq
          velocity x t (huDiff x)
      _ ≤ K * ‖vorticityField velocity x t‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (hK x hx) (sq_nonneg _)
  calc
    periodicVortexStretching velocity t
        ≤ ∫ x in unitCube, K * ‖vorticityField velocity x t‖ ^ 2 := by
          exact setIntegral_mono_on hstretchingIntegrable hnormSqIntegrable
            hcubeMeasurable hpoint
    _ = K * ∫ x in unitCube, ‖vorticityField velocity x t‖ ^ 2 := by
      rw [integral_const_mul]
    _ = 2 * K * periodicEnstrophy velocity t := by
      unfold periodicEnstrophy periodicKineticEnergy kineticEnergyDensity
      rw [integral_const_mul]
      ring

/-- Jacobian and curl-forcing controls close the finite-slab scalar rate inequality. -/
theorem periodicSolutionOn_enstrophyRate_le_of_jacobian_and_forcing_bounds
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : PeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) (hnu : 0 ≤ nu)
    (K F : ℝ)
    (hK : ∀ x ∈ unitCube,
      ‖fderiv ℝ (fun y => velocity y t) x‖ ≤ K)
    (hforce : periodicCurlForcingWork force velocity t ≤ F) :
    periodicEnstrophyRate nu force velocity t ≤
      2 * K * periodicEnstrophy velocity t + F := by
  have hdiss := periodicSolutionOn_viscousVorticityDissipation_nonneg
    solution ht0 htT hnu
  have hstretch :=
    periodicSolutionOn_vortexStretching_le_two_mul_jacobianBound_mul_enstrophy
      solution ht0 htT K hK
  unfold periodicEnstrophyRate
  linarith

/-- Uniform interior controls give the exact Grönwall bound on every compact interval strictly
inside the lifespan. -/
theorem periodicSolutionOn_enstrophy_le_gronwallBound
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : PeriodicSolutionOn T nu initial force velocity pressure)
    {a b : ℝ} (ha : 0 < a) (_hab : a ≤ b) (hbT : b < T) (hnu : 0 ≤ nu)
    (K F : ℝ)
    (hK : ∀ t ∈ Ico a b, ∀ x ∈ unitCube,
      ‖fderiv ℝ (fun y => velocity y t) x‖ ≤ K)
    (hforce : ∀ t ∈ Ico a b,
      periodicCurlForcingWork force velocity t ≤ F) :
    ∀ t ∈ Icc a b,
      periodicEnstrophy velocity t ≤
        gronwallBound (periodicEnstrophy velocity a) (2 * K) F (t - a) := by
  let E : ℝ → ℝ := periodicEnstrophy velocity
  let E' : ℝ → ℝ := periodicEnstrophyRate nu force velocity
  have hcontinuous : ContinuousOn E (Icc a b) := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le ha ht.1
    have htT : t < T := lt_of_le_of_lt ht.2 hbT
    exact (periodicSolutionOn_hasDerivAt_periodicEnstrophy_fromMomentum
      solution ht0 htT).continuousAt.continuousWithinAt
  have hderiv : ∀ t ∈ Ico a b, HasDerivWithinAt E (E' t) (Ici t) t := by
    intro t ht
    exact (periodicSolutionOn_hasDerivAt_periodicEnstrophy_fromMomentum solution
      (lt_of_lt_of_le ha ht.1) (lt_trans ht.2 hbT)).hasDerivWithinAt
  have hbound : ∀ t ∈ Ico a b, E' t ≤ 2 * K * E t + F := by
    intro t ht
    exact periodicSolutionOn_enstrophyRate_le_of_jacobian_and_forcing_bounds
      solution (lt_of_lt_of_le ha ht.1) (lt_trans ht.2 hbT)
        hnu K F (hK t ht) (hforce t ht)
  exact le_gronwallBound_of_liminf_deriv_right_le hcontinuous
    (fun t ht r hr => (hderiv t ht).liminf_right_slope_le hr)
    (le_refl _) hbound

/-- The exponential specialization when curl-forcing work is nonpositive. -/
theorem periodicSolutionOn_enstrophy_le_exponential_of_nonpositive_forcing
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : PeriodicSolutionOn T nu initial force velocity pressure)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (hnu : 0 ≤ nu)
    (K : ℝ)
    (hK : ∀ t ∈ Ico a b, ∀ x ∈ unitCube,
      ‖fderiv ℝ (fun y => velocity y t) x‖ ≤ K)
    (hforce : ∀ t ∈ Ico a b,
      periodicCurlForcingWork force velocity t ≤ 0) :
    ∀ t ∈ Icc a b,
      periodicEnstrophy velocity t ≤
        periodicEnstrophy velocity a * Real.exp ((2 * K) * (t - a)) := by
  intro t ht
  have h := periodicSolutionOn_enstrophy_le_gronwallBound
    solution ha hab hbT hnu K 0 hK hforce t ht
  simpa [gronwallBound_ε0] using h

/-- Uniform Jacobian and curl-forcing control throughout the open lifespan. -/
structure InteriorVorticityControl
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (_solution : PeriodicSolutionOn T nu initial force velocity pressure)
    (K F : ℝ) : Prop where
  jacobian : ∀ t ∈ Ioo 0 T, ∀ x ∈ unitCube,
    ‖fderiv ℝ (fun y => velocity y t) x‖ ≤ K
  curlForcing : ∀ t ∈ Ioo 0 T,
    periodicCurlForcingWork force velocity t ≤ F

/-- A finite periodic world-tube extends when the same fields carry a strictly longer periodic
slab.  A later restart/gluing theorem may replace this deliberately strict same-field receiver. -/
def PeriodicSolutionOn.CanExtendPast
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (_solution : PeriodicSolutionOn T nu initial force velocity pressure) : Prop :=
  ∃ S, T < S ∧ PeriodicSolutionOn S nu initial force velocity pressure

/-- The unresolved terminal continuation fibre for the finite periodic carrier. -/
def PeriodicSolutionOn.IsTerminal
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : PeriodicSolutionOn T nu initial force velocity pressure) : Prop :=
  ¬ solution.CanExtendPast

/-- The exact residual left when uniform interior vorticity controls coexist with failure of the
declared extension receiver. -/
def ControlledTerminalObstruction
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : PeriodicSolutionOn T nu initial force velocity pressure)
    (K F : ℝ) : Prop :=
  InteriorVorticityControl solution K F ∧ solution.IsTerminal

/-- Interior estimates do not choose the terminal branch: they return either an actual longer
periodic slab or the explicitly retained controlled terminal obstruction. -/
theorem extension_or_controlledTerminalObstruction
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : PeriodicSolutionOn T nu initial force velocity pressure)
    (K F : ℝ) (hcontrol : InteriorVorticityControl solution K F) :
    solution.CanExtendPast ∨ ControlledTerminalObstruction solution K F := by
  by_cases hext : solution.CanExtendPast
  · exact Or.inl hext
  · exact Or.inr ⟨hcontrol, hext⟩

/-- The combined finite-time return: every compact interior interval has the Grönwall estimate,
while terminal continuation remains a visibly separate alternative. -/
theorem controlled_enstrophy_and_extensionAlternative
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : PeriodicSolutionOn T nu initial force velocity pressure)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (hnu : 0 ≤ nu)
    (K F : ℝ) (hcontrol : InteriorVorticityControl solution K F) :
    (∀ t ∈ Icc a b,
      periodicEnstrophy velocity t ≤
        gronwallBound (periodicEnstrophy velocity a) (2 * K) F (t - a)) ∧
      (solution.CanExtendPast ∨ ControlledTerminalObstruction solution K F) := by
  constructor
  · apply periodicSolutionOn_enstrophy_le_gronwallBound
      solution ha hab hbT hnu K F
    · intro t ht x hx
      exact hcontrol.jacobian t
        ⟨lt_of_lt_of_le ha ht.1, lt_trans ht.2 hbT⟩ x hx
    · intro t ht
      exact hcontrol.curlForcing t
        ⟨lt_of_lt_of_le ha ht.1, lt_trans ht.2 hbT⟩
  · exact extension_or_controlledTerminalObstruction solution K F hcontrol


section Audit

#print axioms periodicSolutionOn_enstrophy_le_gronwallBound
#print axioms controlled_enstrophy_and_extensionAlternative

end Audit

end Soma.Holonics.Millennium.NavierStokesFiniteTimeVorticity
