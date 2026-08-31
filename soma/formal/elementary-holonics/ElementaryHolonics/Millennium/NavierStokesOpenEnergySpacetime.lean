import ElementaryHolonics.Millennium.NavierStokesCoordinateLowerEnergyEstimate
import ElementaryHolonics.Millennium.NavierStokesPeriodicEnstrophy
import ElementaryHolonics.Millennium.NavierStokesTerminalShellControl
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Open-lifespan kinetic energy and spacetime dissipation

This module attaches the exact order-zero production owner to the genuine half-open periodic
lifespan. It proves the unforced kinetic-energy derivative at every positive interior time and
then integrates that same identity on arbitrary compact interior intervals. No value or
regularity at the absent terminal face is used.
-/

noncomputable section

open ContDiff Filter InnerProductSpace MeasureTheory Set
open scoped BigOperators Interval Laplacian Topology

namespace Soma.Holonics.Millennium.NavierStokesOpenEnergySpacetime

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCoordinateH1Production
open Soma.Holonics.Millennium.NavierStokesCoordinateH3Production
open Soma.Holonics.Millennium.NavierStokesCoordinateLowerEnergyEstimate
open Soma.Holonics.Millennium.NavierStokesFiniteTimeVorticity
open Soma.Holonics.Millennium.NavierStokesH3Production
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPeriodicEnergy
open Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy
open Soma.Holonics.Millennium.NavierStokesPeriodicFlux
open Soma.Holonics.Millennium.NavierStokesQuadraticH3Energy
open Soma.Holonics.Millennium.NavierStokesTerminalShellControl
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesVorticity

/-! ## The exact positive-interior derivative -/

/-- The unique order-zero coordinate word is exactly the ordinary Eulerian kinetic work. -/
theorem coordinateH0TimeWork_eq_integral_eulerianTimeWork
    (velocity : VelocityField) (t : ℝ) :
    coordinateH0TimeWork velocity t =
      ∫ x in unitCube,
        inner ℝ (eulerianTimeJet velocity x t) (velocity x t) := by
  unfold coordinateH0TimeWork
  calc
    (∑ word : Fin 0 → Fin 3,
        ∫ x in unitCube,
          inner ℝ
            (eulerianTimeJet (coordinateJetField velocity 0 word) x t)
            (coordinateJet velocity 0 word x t)) =
        ∑ _word : Fin 0 → Fin 3,
          ∫ x in unitCube,
            inner ℝ (eulerianTimeJet velocity x t) (velocity x t) := by
      apply Finset.sum_congr rfl
      intro word _hword
      have hfield : coordinateJetField velocity 0 word = velocity := by
        funext x s
        exact coordinateJet_zero_eq_velocity velocity word x s
      rw [hfield]
      rfl
    _ = ∫ x in unitCube,
          inner ℝ (eulerianTimeJet velocity x t) (velocity x t) := by simp

/-- **[proved-derived] Exact unforced kinetic-energy derivative on the genuine open lifespan.**

Only `0 < t < T` is used. In particular, the theorem asserts neither a field value nor
smoothness at the absent terminal face `T`. -/
theorem openPeriodicSolutionOn_hasDerivAt_periodicKineticEnergy_unforced
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    HasDerivAt (periodicKineticEnergy velocity)
      (-nu * coordinateH0Dissipation velocity t) t := by
  have hsmooth : ContDiffOn ℝ ∞ (Function.uncurry velocity)
      (Soma.Holonics.Millennium.NavierStokesFiniteTimeVorticity.openSpaceTimeSlab T) := by
    apply solution.velocitySmooth.mono
    rintro ⟨x, time⟩ hxt
    exact ⟨Set.mem_univ x, hxt.2.1.le, hxt.2.2⟩
  have hderivative :=
    hasDerivAt_periodicKineticEnergy_eq_timeWork_of_contDiffOn_openSlab
      velocity hsmooth ht.1 ht.2
  rw [← coordinateH0TimeWork_eq_integral_eulerianTimeWork] at hderivative
  rw [openPeriodicSolutionOn_unforced_coordinateH0TimeWork_eq_dissipation
    solution ht] at hderivative
  exact hderivative

/-! ## Compact-interior continuity and integration -/

/-- Restricting the joint velocity derivative to the spatial port recovers the derivative of
the fixed-time velocity slice. -/
theorem openPeriodicSolutionOn_fderiv_velocitySlice_eq_jointSpatialDerivative
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (x : Space) (t : Ioo (0 : ℝ) T) :
    fderiv ℝ (fun y ↦ velocity y t.1) x =
      (fderiv ℝ (Function.uncurry velocity) (x, t.1)).comp spatialInclusion := by
  let interiorCylinder : Set (Space × ℝ) := Set.univ ×ˢ Set.Ioo (0 : ℝ) T
  have hopen : IsOpen interiorCylinder := isOpen_univ.prod isOpen_Ioo
  have hvelocity : ContDiffOn ℝ ∞ (Function.uncurry velocity) interiorCylinder := by
    apply solution.velocitySmooth.mono
    rintro ⟨y, s⟩ ⟨_hy, hs⟩
    exact ⟨Set.mem_univ y, hs.1.le, hs.2⟩
  have hvelocityAt : ContDiffAt ℝ 1 (Function.uncurry velocity) (x, t.1) :=
    (hvelocity.contDiffAt (hopen.mem_nhds ⟨Set.mem_univ x, t.2⟩)).of_le
      (by norm_num)
  have hjoint : DifferentiableAt ℝ (Function.uncurry velocity) (x, t.1) :=
    hvelocityAt.differentiableAt (by norm_num)
  have hslice := hjoint.hasFDerivAt.comp x
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) x t.1)
  simpa [Function.comp_def, spatialInclusion] using hslice.fderiv

/-- The joint spatial velocity derivative is continuous throughout the strict-interior
space--time cylinder. -/
theorem openPeriodicSolutionOn_jointSpatialVelocityDerivative_continuousOn
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure) :
    ContinuousOn
      (fun z : Space × ℝ ↦
        (fderiv ℝ (Function.uncurry velocity) z).comp spatialInclusion)
      (Set.univ ×ˢ Set.Ioo (0 : ℝ) T) := by
  let interiorCylinder : Set (Space × ℝ) := Set.univ ×ˢ Set.Ioo (0 : ℝ) T
  have hopen : IsOpen interiorCylinder := isOpen_univ.prod isOpen_Ioo
  have hvelocity : ContDiffOn ℝ ∞ (Function.uncurry velocity) interiorCylinder := by
    apply solution.velocitySmooth.mono
    rintro ⟨x, t⟩ ⟨_hx, ht⟩
    exact ⟨Set.mem_univ x, ht.1.le, ht.2⟩
  have hderivative : ContDiffOn ℝ ∞
      (fderiv ℝ (Function.uncurry velocity)) interiorCylinder :=
    hvelocity.fderiv_of_isOpen hopen (by simp)
  have hrestrict :=
    ((ContinuousLinearMap.compL ℝ Space (Space × ℝ) Space).flip spatialInclusion).contDiff
      |>.comp_contDiffOn hderivative
  simpa [interiorCylinder, Function.comp_def] using hrestrict.continuousOn

/-- The order-zero dissipation is interval-integrable on every compact subinterval of the
strict interior. -/
theorem openPeriodicSolutionOn_coordinateH0Dissipation_intervalIntegrable
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) :
    IntervalIntegrable (coordinateH0Dissipation velocity) volume a b := by
  have habInterior : Icc a b ⊆ Ioo (0 : ℝ) T := by
    intro t ht
    exact ⟨ha.trans_le ht.1, ht.2.trans_lt hbT⟩
  let swap : Icc a b × Space → Space × ℝ := fun z ↦ (z.2, z.1.1)
  have hswap : Continuous swap :=
    continuous_snd.prodMk (continuous_subtype_val.comp continuous_fst)
  have hswapMem : ∀ z, swap z ∈ Set.univ ×ˢ Ioo (0 : ℝ) T := by
    rintro ⟨t, x⟩
    exact ⟨Set.mem_univ x, habInterior t.2⟩
  have hjoint : Continuous (fun z : Icc a b × Space ↦
      (fderiv ℝ (Function.uncurry velocity) (z.2, z.1.1)).comp spatialInclusion) := by
    simpa [swap, Function.comp_def] using
      (openPeriodicSolutionOn_jointSpatialVelocityDerivative_continuousOn solution)
        |>.comp_continuous hswap hswapMem
  have hdensity : Continuous (Function.uncurry
      (fun t : Icc a b ↦ fun x : Space ↦
        ∑ component : Fin 3,
          ‖gradient (fun y ↦ velocity y t.1 component) x‖ ^ 2)) := by
    let expressed : Icc a b × Space → ℝ := fun z ↦
      ∑ component : Fin 3,
        ‖(toDual ℝ Space).symm
          ((EuclideanSpace.proj component).comp
            ((fderiv ℝ (Function.uncurry velocity) (z.2, z.1.1)).comp
              spatialInclusion))‖ ^ 2
    have hexpressed : Continuous expressed := by
      dsimp [expressed]
      fun_prop
    apply hexpressed.congr
    rintro ⟨t, x⟩
    apply Finset.sum_congr rfl
    intro component _hcomponent
    congr 2
    unfold gradient
    have htInterior : t.1 ∈ Ioo (0 : ℝ) T := habInterior t.2
    have hsliceDiff : DifferentiableAt ℝ (fun y ↦ velocity y t.1) x :=
      (openPeriodicSolutionOn_velocitySlice_contDiff solution htInterior).differentiable
        (by simp) x
    have hcomponentDerivative :
        fderiv ℝ (fun y ↦ velocity y t.1 component) x =
          (EuclideanSpace.proj component).comp
            (fderiv ℝ (fun y ↦ velocity y t.1) x) := by
      change fderiv ℝ ((EuclideanSpace.proj component) ∘
        (fun y ↦ velocity y t.1)) x = _
      exact ((EuclideanSpace.proj component).hasFDerivAt.comp x
        hsliceDiff.hasFDerivAt).fderiv
    rw [hcomponentDerivative,
      openPeriodicSolutionOn_fderiv_velocitySlice_eq_jointSpatialDerivative solution x
        ⟨t.1, htInterior⟩]
  have hcubeCompact : IsCompact unitCube := by
    unfold unitCube
    exact (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr
      isCompact_Icc
  have hrestricted : Continuous (fun t : Icc a b ↦
      coordinateH0Dissipation velocity t.1) := by
    simpa [coordinateH0Dissipation] using
      continuous_parametric_integral_of_continuous hdensity hcubeCompact
  have hcontinuousOn : ContinuousOn (coordinateH0Dissipation velocity) (Icc a b) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact hrestricted
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  exact hcontinuousOn.integrableOn_compact isCompact_Icc

/-- **[proved-derived] Compact-interior unforced energy--dissipation identity.** -/
theorem openPeriodicSolutionOn_periodicKineticEnergy_add_integral_dissipation_eq
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) :
    periodicKineticEnergy velocity b +
        nu * ∫ t in a..b, coordinateH0Dissipation velocity t =
      periodicKineticEnergy velocity a := by
  have hderiv : ∀ t ∈ [[a, b]],
      HasDerivAt (periodicKineticEnergy velocity)
        (-nu * coordinateH0Dissipation velocity t) t := by
    intro t ht
    have ht' : t ∈ Icc a b := by simpa [uIcc_of_le hab] using ht
    exact openPeriodicSolutionOn_hasDerivAt_periodicKineticEnergy_unforced solution
      ⟨ha.trans_le ht'.1, ht'.2.trans_lt hbT⟩
  have hint :=
    (openPeriodicSolutionOn_coordinateH0Dissipation_intervalIntegrable solution ha hab hbT)
      |>.const_mul (-nu)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [intervalIntegral.integral_const_mul] at hftc
  calc
    periodicKineticEnergy velocity b +
        nu * ∫ t in a..b, coordinateH0Dissipation velocity t =
      periodicKineticEnergy velocity b -
        (-nu * ∫ t in a..b, coordinateH0Dissipation velocity t) := by ring
    _ = periodicKineticEnergy velocity a := by rw [hftc]; ring

/-! ## The open-slab spacetime estimate -/

/-- Kinetic energy is nonnegative at every time for which the field is defined. -/
theorem periodicKineticEnergy_nonneg (velocity : VelocityField) (t : ℝ) :
    0 ≤ periodicKineticEnergy velocity t := by
  unfold periodicKineticEnergy kineticEnergyDensity
  exact integral_nonneg fun x ↦ mul_nonneg (by norm_num) (sq_nonneg _)

/-- Kinetic energy is continuous on a compact initial subslab.  This uses the present initial
face but no terminal value. -/
theorem openPeriodicSolutionOn_periodicKineticEnergy_continuousOn_initial
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {b : ℝ} (hbT : b < T) :
    ContinuousOn (periodicKineticEnergy velocity) (Icc (0 : ℝ) b) := by
  let swap : Icc (0 : ℝ) b × Space → Space × ℝ := fun z ↦ (z.2, z.1.1)
  have hswap : Continuous swap :=
    continuous_snd.prodMk (continuous_subtype_val.comp continuous_fst)
  have hswapMem : ∀ z, swap z ∈
      Soma.Holonics.Millennium.NavierStokesOpenLifespan.openSpaceTimeSlab T := by
    rintro ⟨t, x⟩
    exact ⟨Set.mem_univ x, t.2.1, t.2.2.trans_lt hbT⟩
  have hvelocity : Continuous (fun z : Icc (0 : ℝ) b × Space ↦
      velocity z.2 z.1.1) := by
    simpa [swap, Function.comp_def] using
      solution.velocitySmooth.continuousOn.comp_continuous hswap hswapMem
  have hdensity : Continuous (Function.uncurry
      (fun t : Icc (0 : ℝ) b ↦ fun x : Space ↦
        kineticEnergyDensity (fun y ↦ velocity y t.1) x)) := by
    exact (continuous_const.mul (hvelocity.norm.pow 2)).congr (fun z ↦ by rfl)
  have hcubeCompact : IsCompact unitCube := by
    unfold unitCube
    exact (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr
      isCompact_Icc
  have hrestricted : Continuous (fun t : Icc (0 : ℝ) b ↦
      periodicKineticEnergy velocity t.1) := by
    simpa [periodicKineticEnergy] using
      continuous_parametric_integral_of_continuous hdensity hcubeCompact
  exact continuousOn_iff_continuous_domRestrict.mpr hrestricted

/-- The two compact endpoints used to exhaust the genuine open lifespan. -/
private def openEnergyLeftEndpoint (T : ℝ) (n : ℕ) : ℝ :=
  terminalDyadicRadius T (n + 2)

private def openEnergyRightEndpoint (T : ℝ) (n : ℕ) : ℝ :=
  T - terminalDyadicRadius T (n + 2)

private theorem openEnergyLeftEndpoint_tendsto_zero (T : ℝ) :
    Tendsto (openEnergyLeftEndpoint T) atTop (nhds 0) := by
  change Tendsto (fun n : ℕ ↦ terminalDyadicRadius T (n + 2)) atTop (nhds 0)
  exact (tendsto_terminalDyadicRadius_atTop (T := T)).comp
    (tendsto_add_atTop_nat 2)

private theorem openEnergyRightEndpoint_tendsto_terminal (T : ℝ) :
    Tendsto (openEnergyRightEndpoint T) atTop (nhds T) := by
  change Tendsto (fun n : ℕ ↦ T - openEnergyLeftEndpoint T n) atTop (nhds T)
  simpa using (openEnergyLeftEndpoint_tendsto_zero T).const_sub T

private theorem openEnergy_endpoints_mem
    {T : ℝ} (hT : 0 < T) (n : ℕ) :
    0 < openEnergyLeftEndpoint T n ∧
      openEnergyLeftEndpoint T n ≤ openEnergyRightEndpoint T n ∧
      openEnergyRightEndpoint T n < T := by
  have hanti := terminalDyadicRadius_strictAnti hT
  have hrle : terminalDyadicRadius T (n + 2) ≤ terminalDyadicRadius T 2 :=
    hanti.antitone (by omega)
  have hradiusTwo : terminalDyadicRadius T 2 = T / 4 := by
    norm_num [terminalDyadicRadius, div_eq_mul_inv]
  have hrpos := terminalDyadicRadius_pos hT (n + 2)
  dsimp [openEnergyLeftEndpoint, openEnergyRightEndpoint]
  rw [hradiusTwo] at hrle
  constructor
  · exact hrpos
  constructor
  · linarith
  · linarith

/-- **[proved-derived] Global open-slab velocity-dissipation estimate.**

The dissipation is genuinely integrable and its complete spacetime mass is paid by the initial
kinetic energy.  The terminal face is reached only as an `AECover` limit of compact interior
intervals; neither a field value nor an energy trace at `T` is used. -/
theorem openPeriodicSolutionOn_coordinateH0Dissipation_integrableOn_and_integral_le
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) :
    IntegrableOn (coordinateH0Dissipation velocity) (Ioo (0 : ℝ) T) volume ∧
      (∫ t in Ioo (0 : ℝ) T, coordinateH0Dissipation velocity t) ≤
        periodicKineticEnergy velocity 0 / nu := by
  have hT : 0 < T := solution.terminal_pos
  have hleftTendsto := openEnergyLeftEndpoint_tendsto_zero T
  have hrightTendsto := openEnergyRightEndpoint_tendsto_terminal T
  have hleftMem : ∀ n : ℕ,
      openEnergyLeftEndpoint T n ∈ Icc (0 : ℝ) (T / 2) := by
    intro n
    have hendpoints := openEnergy_endpoints_mem hT n
    have horder := hendpoints.2.1
    dsimp [openEnergyLeftEndpoint, openEnergyRightEndpoint] at horder ⊢
    exact ⟨hendpoints.1.le, by linarith⟩
  have hleftWithin : Tendsto (openEnergyLeftEndpoint T) atTop
      (nhdsWithin 0 (Icc (0 : ℝ) (T / 2))) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hleftTendsto, Eventually.of_forall hleftMem⟩
  have henergyContinuous :=
    openPeriodicSolutionOn_periodicKineticEnergy_continuousOn_initial
      solution (by linarith : T / 2 < T)
  have hzeroMem : (0 : ℝ) ∈ Icc (0 : ℝ) (T / 2) :=
    ⟨le_rfl, by positivity⟩
  have henergyLeft : Tendsto
      (fun n : ℕ ↦ periodicKineticEnergy velocity (openEnergyLeftEndpoint T n))
      atTop (nhds (periodicKineticEnergy velocity 0)) :=
    (henergyContinuous.continuousWithinAt hzeroMem).tendsto.comp hleftWithin
  have henergyEventually : ∀ᶠ n in atTop,
      periodicKineticEnergy velocity (openEnergyLeftEndpoint T n) ≤
        periodicKineticEnergy velocity 0 + 1 := by
    filter_upwards [henergyLeft.eventually
      (Iio_mem_nhds (by linarith :
        periodicKineticEnergy velocity 0 < periodicKineticEnergy velocity 0 + 1))]
      with n hn
    exact hn.le
  have hlocal : ∀ n : ℕ,
      IntegrableOn (coordinateH0Dissipation velocity)
        (Ioc (openEnergyLeftEndpoint T n) (openEnergyRightEndpoint T n)) volume := by
    intro n
    have hendpoints := openEnergy_endpoints_mem hT n
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hendpoints.2.1).1
      (openPeriodicSolutionOn_coordinateH0Dissipation_intervalIntegrable solution
        hendpoints.1 hendpoints.2.1 hendpoints.2.2)
  have hbound : ∀ᶠ n in atTop,
      (∫ t in Ioc (openEnergyLeftEndpoint T n) (openEnergyRightEndpoint T n),
        ‖coordinateH0Dissipation velocity t‖) ≤
          (periodicKineticEnergy velocity 0 + 1) / nu := by
    filter_upwards [henergyEventually] with n henergy
    have hendpoints := openEnergy_endpoints_mem hT n
    have hidentity :=
      openPeriodicSolutionOn_periodicKineticEnergy_add_integral_dissipation_eq
        solution hendpoints.1 hendpoints.2.1 hendpoints.2.2
    have hnormIntegral :
        (∫ t in Ioc (openEnergyLeftEndpoint T n) (openEnergyRightEndpoint T n),
          ‖coordinateH0Dissipation velocity t‖) =
        ∫ t in Ioc (openEnergyLeftEndpoint T n) (openEnergyRightEndpoint T n),
          coordinateH0Dissipation velocity t := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro t _ht
      exact Real.norm_of_nonneg (coordinateH0Dissipation_nonneg velocity t)
    rw [hnormIntegral, ← intervalIntegral.integral_of_le hendpoints.2.1]
    have hterminalEnergy :=
      periodicKineticEnergy_nonneg velocity (openEnergyRightEndpoint T n)
    have hintegral :
        (∫ t in openEnergyLeftEndpoint T n..openEnergyRightEndpoint T n,
          coordinateH0Dissipation velocity t) ≤
        periodicKineticEnergy velocity (openEnergyLeftEndpoint T n) / nu := by
      rw [le_div_iff₀ hnu]
      nlinarith
    exact hintegral.trans ((div_le_div_iff_of_pos_right hnu).2 henergy)
  have hglobalIoc : IntegrableOn (coordinateH0Dissipation velocity)
      (Ioc (0 : ℝ) T) volume :=
    integrableOn_Ioc_of_intervalIntegral_norm_bounded
      (I := (periodicKineticEnergy velocity 0 + 1) / nu)
      hlocal hleftTendsto hrightTendsto hbound
  have hcompactBound : ∀ n : ℕ,
      (∫ t in Ioc (openEnergyLeftEndpoint T n) (openEnergyRightEndpoint T n),
        coordinateH0Dissipation velocity t) ≤
      periodicKineticEnergy velocity (openEnergyLeftEndpoint T n) / nu := by
    intro n
    have hendpoints := openEnergy_endpoints_mem hT n
    have hidentity :=
      openPeriodicSolutionOn_periodicKineticEnergy_add_integral_dissipation_eq
        solution hendpoints.1 hendpoints.2.1 hendpoints.2.2
    rw [← intervalIntegral.integral_of_le hendpoints.2.1]
    have hterminalEnergy :=
      periodicKineticEnergy_nonneg velocity (openEnergyRightEndpoint T n)
    rw [le_div_iff₀ hnu]
    nlinarith
  have hsubset : ∀ n : ℕ,
      Ioc (openEnergyLeftEndpoint T n) (openEnergyRightEndpoint T n) ⊆
        Ioc (0 : ℝ) T := by
    intro n t ht
    have hendpoints := openEnergy_endpoints_mem hT n
    exact ⟨hendpoints.1.trans ht.1, (ht.2.trans_lt hendpoints.2.2).le⟩
  have hcover : AECover (volume.restrict (Ioc (0 : ℝ) T)) atTop
      (fun n : ℕ ↦ Ioc (openEnergyLeftEndpoint T n) (openEnergyRightEndpoint T n)) :=
    aecover_Ioc_of_Ioc hleftTendsto hrightTendsto
  have hconvergenceRestricted :=
    hcover.integral_tendsto_of_countably_generated hglobalIoc
  have hconvergence : Tendsto
      (fun n : ℕ ↦
        ∫ t in Ioc (openEnergyLeftEndpoint T n) (openEnergyRightEndpoint T n),
          coordinateH0Dissipation velocity t)
      atTop
      (nhds (∫ t in Ioc (0 : ℝ) T, coordinateH0Dissipation velocity t)) := by
    apply hconvergenceRestricted.congr'
    filter_upwards [] with n
    rw [Measure.restrict_restrict measurableSet_Ioc,
      inter_eq_left.mpr (hsubset n)]
  have hlimitBound :
      (∫ t in Ioc (0 : ℝ) T, coordinateH0Dissipation velocity t) ≤
        periodicKineticEnergy velocity 0 / nu :=
    le_of_tendsto_of_tendsto hconvergence (henergyLeft.div_const nu)
      (Eventually.of_forall hcompactBound)
  refine ⟨(integrableOn_Ioc_iff_integrableOn_Ioo).1 hglobalIoc, ?_⟩
  simpa only [integral_Ioc_eq_integral_Ioo] using hlimitBound

/-! ## A coarse but unconditional vorticity consequence -/

/-- The square of matrix curl is at most twice the complete matrix square population. -/
theorem norm_curlFromJacobian_sq_le_two_mul_sum_sq (J : Matrix3) :
    ‖curlFromJacobian J‖ ^ 2 ≤
      2 * ∑ i : Fin 3, ∑ j : Fin 3, (J i j) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [Fin.sum_univ_succ]
  simp [curlFromJacobian]
  nlinarith [sq_nonneg (J 2 1 + J 1 2), sq_nonneg (J 0 2 + J 2 0),
    sq_nonneg (J 1 0 + J 0 1), sq_nonneg (J 0 0), sq_nonneg (J 1 1),
    sq_nonneg (J 2 2)]

/-- The complete matrix square population is the sum of the component-gradient squares. -/
theorem sum_norm_gradient_sq_eq_sum_velocityJacobianAt_sq
    (u : InitialVelocity) (x : Space) (hu : DifferentiableAt ℝ u x) :
    (∑ i : Fin 3, ‖gradient (fun y ↦ u y i) x‖ ^ 2) =
      ∑ i : Fin 3, ∑ j : Fin 3, (velocityJacobianAt u x i j) ^ 2 := by
  apply Finset.sum_congr rfl
  intro i _hi
  rw [EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [velocityJacobianAt, jacobianMatrix_apply]
  congr 1
  rw [← EuclideanSpace.inner_basisFun_real (Fin 3)
    (gradient (fun y ↦ u y i) x : Space) j, inner_gradient_left]
  have hcomponentDerivative :
      fderiv ℝ (fun y ↦ u y i) x =
        (EuclideanSpace.proj i).comp (fderiv ℝ u x) := by
    change fderiv ℝ ((EuclideanSpace.proj i) ∘ u) x = _
    exact ((EuclideanSpace.proj i).hasFDerivAt.comp x hu.hasFDerivAt).fderiv
  rw [hcomponentDerivative]
  rfl

/-- At every admitted strict-interior event, squared vorticity is bounded by twice the
velocity-gradient square population. -/
theorem openPeriodicSolutionOn_norm_vorticityField_sq_le_two_mul_gradient_sq
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) (x : Space) :
    ‖vorticityField velocity x t‖ ^ 2 ≤
      2 * ∑ component : Fin 3,
        ‖gradient (fun y ↦ velocity y t component) x‖ ^ 2 := by
  let u : InitialVelocity := fun y ↦ velocity y t
  have hu : DifferentiableAt ℝ u x :=
    (openPeriodicSolutionOn_velocitySlice_contDiff solution ht).differentiable
      (by simp) x
  calc
    ‖vorticityField velocity x t‖ ^ 2 =
        ‖curlFromJacobian (velocityJacobianAt u x)‖ ^ 2 := by rfl
    _ ≤ 2 * ∑ i : Fin 3, ∑ j : Fin 3,
        (velocityJacobianAt u x i j) ^ 2 :=
      norm_curlFromJacobian_sq_le_two_mul_sum_sq _
    _ = 2 * ∑ component : Fin 3,
        ‖gradient (fun y ↦ velocity y t component) x‖ ^ 2 := by
      rw [sum_norm_gradient_sq_eq_sum_velocityJacobianAt_sq u x hu]

/-- The spatial vorticity second moment on one strict-interior slice is at most twice the
order-zero dissipation. -/
theorem openPeriodicSolutionOn_integral_norm_vorticityField_sq_le_two_mul_dissipation
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    (∫ x in unitCube, ‖vorticityField velocity x t‖ ^ 2) ≤
      2 * coordinateH0Dissipation velocity t := by
  have hcubeCompact : IsCompact unitCube := by
    unfold unitCube
    exact (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr
      isCompact_Icc
  have hu : ContDiff ℝ ∞ (fun y ↦ velocity y t) :=
    openPeriodicSolutionOn_velocitySlice_contDiff solution ht
  have hrightContinuous : Continuous (fun x : Space ↦
      2 * ∑ component : Fin 3,
        ‖gradient (fun y ↦ velocity y t component) x‖ ^ 2) := by
    apply continuous_const.mul
    apply continuous_finsetSum
    intro component _hcomponent
    have hcomponent : ContDiff ℝ ∞ (fun y ↦ velocity y t component) :=
      by
        change ContDiff ℝ ∞ ((EuclideanSpace.proj component) ∘
          (fun y ↦ velocity y t))
        exact (EuclideanSpace.proj component).contDiff.comp hu
    exact (gradient_contDiff hcomponent).continuous.norm.pow 2
  have hrightIntegrable : IntegrableOn (fun x : Space ↦
      2 * ∑ component : Fin 3,
        ‖gradient (fun y ↦ velocity y t component) x‖ ^ 2) unitCube :=
    hrightContinuous.continuousOn.integrableOn_compact hcubeCompact
  calc
    (∫ x in unitCube, ‖vorticityField velocity x t‖ ^ 2) ≤
        ∫ x in unitCube, 2 * ∑ component : Fin 3,
          ‖gradient (fun y ↦ velocity y t component) x‖ ^ 2 := by
      apply setIntegral_mono_of_nonneg
      · intro x _hx
        exact sq_nonneg _
      · intro x _hx
        exact openPeriodicSolutionOn_norm_vorticityField_sq_le_two_mul_gradient_sq
          solution ht x
      · exact hrightIntegrable
    _ = 2 * coordinateH0Dissipation velocity t := by
      unfold coordinateH0Dissipation
      rw [integral_const_mul]

/-- Twice enstrophy is literally the spatial vorticity second moment. -/
theorem integral_norm_vorticityField_sq_eq_two_mul_periodicEnstrophy
    (velocity : VelocityField) (t : ℝ) :
    (∫ x in unitCube, ‖vorticityField velocity x t‖ ^ 2) =
      2 * periodicEnstrophy velocity t := by
  unfold periodicEnstrophy periodicKineticEnergy kineticEnergyDensity
  rw [integral_const_mul]
  ring

/-- Enstrophy is continuous throughout the strict interior. -/
theorem openPeriodicSolutionOn_periodicEnstrophy_continuousOn
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure) :
    ContinuousOn (periodicEnstrophy velocity) (Ioo (0 : ℝ) T) := by
  intro t ht
  let S : ℝ := (t + T) / 2
  have hSpos : 0 < S := by dsimp [S]; nlinarith [ht.1, ht.2]
  have htS : t < S := by dsimp [S]; nlinarith [ht.2]
  have hST : S < T := by dsimp [S]; nlinarith [ht.2]
  have hderivative := periodicSolutionOn_hasDerivAt_periodicEnstrophy_eq_timeWork
    (solution.toClosedInterior hSpos hST) ht.1 htS
  exact hderivative.continuousAt.continuousWithinAt

/-- **[proved-derived] Global open-slab vorticity second-moment bound.**

This is the coarse unconditional curl estimate; it does not use the sharper periodic
divergence-free Hodge identity. -/
theorem openPeriodicSolutionOn_vorticitySecondMoment_integrableOn_and_integral_le
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) :
    IntegrableOn
        (fun t ↦ ∫ x in unitCube, ‖vorticityField velocity x t‖ ^ 2)
        (Ioo (0 : ℝ) T) volume ∧
      (∫ t in Ioo (0 : ℝ) T,
        ∫ x in unitCube, ‖vorticityField velocity x t‖ ^ 2) ≤
        2 * (periodicKineticEnergy velocity 0 / nu) := by
  have hdissipation :=
    openPeriodicSolutionOn_coordinateH0Dissipation_integrableOn_and_integral_le
      solution hnu
  have henstrophyNonneg : ∀ t : ℝ, 0 ≤ periodicEnstrophy velocity t :=
    periodicKineticEnergy_nonneg (vorticityField velocity)
  have henstrophyLe : ∀ t ∈ Ioo (0 : ℝ) T,
      periodicEnstrophy velocity t ≤ coordinateH0Dissipation velocity t := by
    intro t ht
    have hslice :=
      openPeriodicSolutionOn_integral_norm_vorticityField_sq_le_two_mul_dissipation
        solution ht
    rw [integral_norm_vorticityField_sq_eq_two_mul_periodicEnstrophy] at hslice
    linarith
  have henstrophyMeasurable : AEStronglyMeasurable (periodicEnstrophy velocity)
      (volume.restrict (Ioo (0 : ℝ) T)) :=
    (openPeriodicSolutionOn_periodicEnstrophy_continuousOn solution)
      |>.aestronglyMeasurable measurableSet_Ioo
  have henstrophyIntegrable : IntegrableOn (periodicEnstrophy velocity)
      (Ioo (0 : ℝ) T) volume := by
    apply Integrable.mono' hdissipation.1 henstrophyMeasurable
    apply (ae_restrict_iff' measurableSet_Ioo).2
    filter_upwards with t
    intro ht
    rw [Real.norm_of_nonneg (henstrophyNonneg t)]
    exact henstrophyLe t ht
  have henstrophyIntegralLe :
      (∫ t in Ioo (0 : ℝ) T, periodicEnstrophy velocity t) ≤
        ∫ t in Ioo (0 : ℝ) T, coordinateH0Dissipation velocity t :=
    setIntegral_mono_on henstrophyIntegrable hdissipation.1 measurableSet_Ioo
      henstrophyLe
  have hmomentEq : ∀ t : ℝ,
      (∫ x in unitCube, ‖vorticityField velocity x t‖ ^ 2) =
        2 * periodicEnstrophy velocity t :=
    integral_norm_vorticityField_sq_eq_two_mul_periodicEnstrophy velocity
  have hmomentIntegrable : IntegrableOn
      (fun t ↦ ∫ x in unitCube, ‖vorticityField velocity x t‖ ^ 2)
      (Ioo (0 : ℝ) T) volume := by
    apply (integrableOn_congr_fun
      (s := Ioo (0 : ℝ) T) (f := fun t ↦
        ∫ x in unitCube, ‖vorticityField velocity x t‖ ^ 2)
      (g := fun t ↦ 2 * periodicEnstrophy velocity t)
      (fun t _ht ↦ hmomentEq t) measurableSet_Ioo).2
    exact henstrophyIntegrable.const_mul 2
  refine ⟨hmomentIntegrable, ?_⟩
  calc
    (∫ t in Ioo (0 : ℝ) T,
        ∫ x in unitCube, ‖vorticityField velocity x t‖ ^ 2) =
        ∫ t in Ioo (0 : ℝ) T, 2 * periodicEnstrophy velocity t := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro t _ht
      exact hmomentEq t
    _ = 2 * ∫ t in Ioo (0 : ℝ) T, periodicEnstrophy velocity t := by
      rw [integral_const_mul]
    _ ≤ 2 * ∫ t in Ioo (0 : ℝ) T,
        coordinateH0Dissipation velocity t := by linarith
    _ ≤ 2 * (periodicKineticEnergy velocity 0 / nu) := by
      exact mul_le_mul_of_nonneg_left hdissipation.2 (by norm_num)

section Audit

#print axioms openPeriodicSolutionOn_hasDerivAt_periodicKineticEnergy_unforced
#print axioms openPeriodicSolutionOn_periodicKineticEnergy_add_integral_dissipation_eq
#print axioms openPeriodicSolutionOn_coordinateH0Dissipation_integrableOn_and_integral_le
#print axioms openPeriodicSolutionOn_vorticitySecondMoment_integrableOn_and_integral_le

end Audit

end Soma.Holonics.Millennium.NavierStokesOpenEnergySpacetime
