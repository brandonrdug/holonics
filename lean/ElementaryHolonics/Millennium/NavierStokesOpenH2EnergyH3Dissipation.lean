import ElementaryHolonics.Millennium.NavierStokesOpenEnergySpacetime

/-!
# The open H2 energy and H3 viscous current

**[proved-derived; formal-checked]** This file differentiates the literal inhomogeneous
coordinate `H2` storage of an unforced periodic open solution.  Its viscous return is the full
order-one-through-order-three coordinate population: the order-zero storage produces first
spatial derivatives, the order-one storage produces second derivatives, and the order-two
storage produces third derivatives.  The undifferentiated Fourier/mean mode is deliberately not
called dissipation; it remains in the endpoint storage.

The exact compact-interior law is

`E2(b) + nu * integral_a^b D3 = E2(a) + integral_a^b P2`,

where `P2` is the signed sum of the first-order stretching current and all three faces of the
second-order commutator current.  No absolute value, Jacobian envelope, or terminal estimate is
inserted.  Consequently an endpoint-uniform `D3` bound requires an endpoint-uniform upper bound
on this actual signed `P2` integral.  The final theorem records that implication without assuming
that missing Navier--Stokes estimate.
-/

noncomputable section

open ContDiff InnerProductSpace MeasureTheory Set
open scoped BigOperators Interval Laplacian

namespace Soma.Holonics.Millennium.NavierStokesOpenH2EnergyH3Dissipation

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCoordinateH1Production
open Soma.Holonics.Millennium.NavierStokesCoordinateH2Production
open Soma.Holonics.Millennium.NavierStokesCoordinateH3Production
open Soma.Holonics.Millennium.NavierStokesCoordinateLowerEnergyEstimate
open Soma.Holonics.Millennium.NavierStokesFiniteTimeVorticity
open Soma.Holonics.Millennium.NavierStokesOpenEnergySpacetime
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPeriodicEnergy
open Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy
open Soma.Holonics.Millennium.NavierStokesPeriodicFlux
open Soma.Holonics.Millennium.NavierStokesQuadraticH3Energy
open Soma.Holonics.Millennium.NavierStokesTorusFourier

/-! ## Storage, viscous current, and signed nonlinear current -/

/-- The complete `1 + 3 + 9` coordinate--Frobenius storage through spatial order two. -/
def coordinateH2Energy (velocity : VelocityField) (t : ℝ) : ℝ :=
  ∑ n : Fin 3, ∑ word : Fin (n : ℕ) → Fin 3,
    periodicKineticEnergy (coordinateJetField velocity n word) t

/-- The derivative population of `coordinateH2Energy`, with all three orders still addressed. -/
def coordinateH2TotalTimeWork (velocity : VelocityField) (t : ℝ) : ℝ :=
  coordinateH0TimeWork velocity t + coordinateH1TimeWork velocity t +
    coordinateH2TimeWork velocity t

/-- The literal viscous population returned by differentiating `H2`: spatial orders one, two,
and three.  The order-zero/mean mode remains in storage and is not silently dissipated. -/
def coordinateH3ViscousDissipation (velocity : VelocityField) (t : ℝ) : ℝ :=
  coordinateH0Dissipation velocity t + coordinateH1Dissipation velocity t +
    coordinateH2Dissipation velocity t

/-- The signed nonlinear current entering the `H2` balance.  This retains the first-order
stretching face and the complete three-face, nine-word second-order commutator population. -/
def coordinateH2NonlinearProductionCurrent (velocity : VelocityField) (t : ℝ) : ℝ :=
  -coordinateH1StretchingWork velocity t - coordinateH2LowerWork velocity t

theorem coordinateH2Energy_nonneg (velocity : VelocityField) (t : ℝ) :
    0 ≤ coordinateH2Energy velocity t := by
  unfold coordinateH2Energy periodicKineticEnergy kineticEnergyDensity
  apply Finset.sum_nonneg
  intro n _hn
  apply Finset.sum_nonneg
  intro word _hword
  apply integral_nonneg_of_ae
  filter_upwards with x
  positivity

theorem coordinateH3ViscousDissipation_nonneg
    (velocity : VelocityField) (t : ℝ) :
    0 ≤ coordinateH3ViscousDissipation velocity t := by
  unfold coordinateH3ViscousDissipation
  exact add_nonneg
    (add_nonneg (coordinateH0Dissipation_nonneg velocity t)
      (coordinateH1Dissipation_nonneg velocity t))
    (coordinateH2Dissipation_nonneg velocity t)

/-! ## Genuine differentiation and exact PDE production -/

theorem openPeriodicSolutionOn_hasDerivAt_coordinateH2Energy
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    HasDerivAt (coordinateH2Energy velocity)
      (coordinateH2TotalTimeWork velocity t) t := by
  have hword : ∀ (n : Fin 3) (word : Fin (n : ℕ) → Fin 3),
      HasDerivAt
        (periodicKineticEnergy (coordinateJetField velocity n word))
        (∫ x in unitCube,
          inner ℝ
            (eulerianTimeJet (coordinateJetField velocity n word) x t)
            (coordinateJet velocity n word x t)) t := by
    intro n word
    exact hasDerivAt_periodicKineticEnergy_eq_timeWork_of_contDiffOn_openSlab
      (coordinateJetField velocity n word)
      (openPeriodicSolutionOn_coordinateJetField_contDiffOn solution n word)
      ht.1 ht.2
  have hinner : ∀ n : Fin 3,
      HasDerivAt
        (fun tau ↦ ∑ word : Fin (n : ℕ) → Fin 3,
          periodicKineticEnergy (coordinateJetField velocity n word) tau)
        (∑ word : Fin (n : ℕ) → Fin 3,
          ∫ x in unitCube,
            inner ℝ
              (eulerianTimeJet (coordinateJetField velocity n word) x t)
              (coordinateJet velocity n word x t)) t := by
    intro n
    exact HasDerivAt.fun_sum fun word _hword ↦ hword n word
  have houter := HasDerivAt.fun_sum (u := Finset.univ)
    (fun n _hn ↦ hinner n)
  change HasDerivAt
    (fun tau ↦ ∑ n : Fin 3, ∑ word : Fin (n : ℕ) → Fin 3,
      periodicKineticEnergy (coordinateJetField velocity n word) tau)
    (coordinateH2TotalTimeWork velocity t) t
  simpa [coordinateH2TotalTimeWork, coordinateH0TimeWork,
    coordinateH1TimeWork, coordinateH2TimeWork, Fin.sum_univ_succ, add_assoc]
    using houter

/-- **Exact pointwise H2 production law.**  The pressure and top transport currents have already
cancelled by the periodic PDE identities; the nonlinear lower current remains signed. -/
theorem openPeriodicSolutionOn_unforced_coordinateH2TotalTimeWork_eq_production
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    coordinateH2TotalTimeWork velocity t =
      -nu * coordinateH3ViscousDissipation velocity t +
        coordinateH2NonlinearProductionCurrent velocity t := by
  have hzero :=
    openPeriodicSolutionOn_unforced_coordinateH0TimeWork_eq_dissipation solution ht
  have hone :=
    openPeriodicSolutionOn_unforced_coordinateH1TimeWork_eq_production solution ht
  have htwo :=
    openPeriodicSolutionOn_unforced_coordinateH2TimeWork_eq_production solution ht
  unfold coordinateH2TotalTimeWork coordinateH3ViscousDissipation
    coordinateH2NonlinearProductionCurrent
  rw [hzero, hone, htwo]
  ring

theorem openPeriodicSolutionOn_hasDerivAt_coordinateH2Energy_eq_production
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    HasDerivAt (coordinateH2Energy velocity)
      (-nu * coordinateH3ViscousDissipation velocity t +
        coordinateH2NonlinearProductionCurrent velocity t) t := by
  rw [← openPeriodicSolutionOn_unforced_coordinateH2TotalTimeWork_eq_production
    solution ht]
  exact openPeriodicSolutionOn_hasDerivAt_coordinateH2Energy solution ht

/-! ## Compact-interior integrability from the actual joint smooth field -/

private theorem openPeriodicSolutionOn_fderiv_coordinateJetSlice_eq_jointSpatialDerivative
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (n : ℕ) (word : Fin n → Fin 3) (x : Space) (t : Ioo (0 : ℝ) T) :
    fderiv ℝ (fun y ↦ coordinateJet velocity n word y t.1) x =
      (fderiv ℝ (Function.uncurry (coordinateJetField velocity n word)) (x, t.1)).comp
        spatialInclusion := by
  have hfield : ContDiffOn ℝ ∞
      (Function.uncurry (coordinateJetField velocity n word))
      (Soma.Holonics.Millennium.NavierStokesFiniteTimeVorticity.openSpaceTimeSlab T) :=
    openPeriodicSolutionOn_coordinateJetField_contDiffOn solution n word
  have hjoint : DifferentiableAt ℝ
      (Function.uncurry (coordinateJetField velocity n word)) (x, t.1) :=
    (hfield.contDiffAt
      (prod_mem_nhds Filter.univ_mem (Ioo_mem_nhds t.2.1 t.2.2)))
      |>.differentiableAt (by simp)
  have hslice := hjoint.hasFDerivAt.comp x
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) x t.1)
  simpa [coordinateJetField, Function.comp_def, spatialInclusion] using hslice.fderiv

private theorem openPeriodicSolutionOn_jointSpatialCoordinateJetDerivative_continuousOn
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (n : ℕ) (word : Fin n → Fin 3) :
    ContinuousOn
      (fun z : Space × ℝ ↦
        (fderiv ℝ (Function.uncurry (coordinateJetField velocity n word)) z).comp
          spatialInclusion)
      (Set.univ ×ˢ Ioo (0 : ℝ) T) := by
  let slab : Set (Space × ℝ) := Set.univ ×ˢ Ioo (0 : ℝ) T
  have hopen : IsOpen slab := isOpen_univ.prod isOpen_Ioo
  have hfield : ContDiffOn ℝ ∞
      (Function.uncurry (coordinateJetField velocity n word)) slab :=
    openPeriodicSolutionOn_coordinateJetField_contDiffOn solution n word
  have hderivative : ContDiffOn ℝ ∞
      (fderiv ℝ (Function.uncurry (coordinateJetField velocity n word))) slab :=
    hfield.fderiv_of_isOpen hopen (by simp)
  have hrestrict :=
    ((ContinuousLinearMap.compL ℝ Space (Space × ℝ) Space).flip spatialInclusion).contDiff
      |>.comp_contDiffOn hderivative
  simpa [slab, Function.comp_def] using hrestrict.continuousOn

private theorem openPeriodicSolutionOn_coordinateOrderDissipation_intervalIntegrable
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (n : ℕ) :
    IntervalIntegrable
      (fun t ↦ ∑ word : Fin n → Fin 3,
        ∫ x in unitCube, ∑ component : Fin 3,
          ‖gradient (fun y ↦ coordinateJet velocity n word y t component) x‖ ^ 2)
      volume a b := by
  have habInterior : Icc a b ⊆ Ioo (0 : ℝ) T := by
    intro t ht
    exact ⟨ha.trans_le ht.1, ht.2.trans_lt hbT⟩
  have hcubeCompact : IsCompact unitCube := by
    unfold unitCube
    exact (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr
      isCompact_Icc
  have hword : ∀ word : Fin n → Fin 3, Continuous (fun t : Icc a b ↦
      ∫ x in unitCube, ∑ component : Fin 3,
        ‖gradient (fun y ↦ coordinateJet velocity n word y t.1 component) x‖ ^ 2) := by
    intro word
    let swap : Icc a b × Space → Space × ℝ := fun z ↦ (z.2, z.1.1)
    have hswap : Continuous swap :=
      continuous_snd.prodMk (continuous_subtype_val.comp continuous_fst)
    have hswapMem : ∀ z, swap z ∈ Set.univ ×ˢ Ioo (0 : ℝ) T := by
      rintro ⟨t, x⟩
      exact ⟨Set.mem_univ x, habInterior t.2⟩
    have hjoint : Continuous (fun z : Icc a b × Space ↦
        (fderiv ℝ (Function.uncurry (coordinateJetField velocity n word))
          (z.2, z.1.1)).comp spatialInclusion) := by
      simpa [swap, Function.comp_def] using
        (openPeriodicSolutionOn_jointSpatialCoordinateJetDerivative_continuousOn
          solution n word).comp_continuous hswap hswapMem
    have hdensity : Continuous (Function.uncurry
        (fun t : Icc a b ↦ fun x : Space ↦
          ∑ component : Fin 3,
            ‖gradient (fun y ↦ coordinateJet velocity n word y t.1 component) x‖ ^ 2)) := by
      let expressed : Icc a b × Space → ℝ := fun z ↦
        ∑ component : Fin 3,
          ‖(toDual ℝ Space).symm
            ((EuclideanSpace.proj component).comp
              ((fderiv ℝ (Function.uncurry (coordinateJetField velocity n word))
                (z.2, z.1.1)).comp spatialInclusion))‖ ^ 2
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
      have hfield : ContDiffOn ℝ ∞
          (Function.uncurry (coordinateJetField velocity n word))
          (Soma.Holonics.Millennium.NavierStokesFiniteTimeVorticity.openSpaceTimeSlab T) :=
        openPeriodicSolutionOn_coordinateJetField_contDiffOn solution n word
      have hsliceDiff : DifferentiableAt ℝ
          (fun y ↦ coordinateJet velocity n word y t.1) x :=
        ((hfield.contDiffAt
          (prod_mem_nhds Filter.univ_mem
            (Ioo_mem_nhds htInterior.1 htInterior.2))).comp x
          (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt (by simp)
      have hcomponentDerivative :
          fderiv ℝ (fun y ↦ coordinateJet velocity n word y t.1 component) x =
            (EuclideanSpace.proj component).comp
              (fderiv ℝ (fun y ↦ coordinateJet velocity n word y t.1) x) := by
        change fderiv ℝ ((EuclideanSpace.proj component) ∘
          (fun y ↦ coordinateJet velocity n word y t.1)) x = _
        exact ((EuclideanSpace.proj component).hasFDerivAt.comp x
          hsliceDiff.hasFDerivAt).fderiv
      rw [hcomponentDerivative,
        openPeriodicSolutionOn_fderiv_coordinateJetSlice_eq_jointSpatialDerivative
          solution n word x ⟨t.1, htInterior⟩]
    exact continuous_parametric_integral_of_continuous hdensity hcubeCompact
  have hrestricted : Continuous (fun t : Icc a b ↦
      ∑ word : Fin n → Fin 3,
        ∫ x in unitCube, ∑ component : Fin 3,
          ‖gradient (fun y ↦ coordinateJet velocity n word y t.1 component) x‖ ^ 2) := by
    apply continuous_finset_sum
    intro word _hword
    exact hword word
  have hcontinuousOn : ContinuousOn
      (fun t ↦ ∑ word : Fin n → Fin 3,
        ∫ x in unitCube, ∑ component : Fin 3,
          ‖gradient (fun y ↦ coordinateJet velocity n word y t component) x‖ ^ 2)
      (Icc a b) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact hrestricted
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  exact hcontinuousOn.integrableOn_compact isCompact_Icc

private theorem openPeriodicSolutionOn_coordinateOrderTimeWork_intervalIntegrable
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) (n : ℕ) :
    IntervalIntegrable
      (fun t ↦ ∑ word : Fin n → Fin 3,
        ∫ x in unitCube,
          inner ℝ
            (eulerianTimeJet (coordinateJetField velocity n word) x t)
            (coordinateJet velocity n word x t)) volume a b := by
  have habInterior : Icc a b ⊆ Ioo (0 : ℝ) T := by
    intro t ht
    exact ⟨ha.trans_le ht.1, ht.2.trans_lt hbT⟩
  have hcubeCompact : IsCompact unitCube := by
    unfold unitCube
    exact (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr
      isCompact_Icc
  have hword : ∀ word : Fin n → Fin 3, Continuous (fun t : Icc a b ↦
      ∫ x in unitCube,
        inner ℝ
          (eulerianTimeJet (coordinateJetField velocity n word) x t.1)
          (coordinateJet velocity n word x t.1)) := by
    intro word
    let slab : Set (Space × ℝ) := Set.univ ×ˢ Ioo (0 : ℝ) T
    let swap : Icc a b × Space → Space × ℝ := fun z ↦ (z.2, z.1.1)
    have hopen : IsOpen slab := isOpen_univ.prod isOpen_Ioo
    have hswap : Continuous swap :=
      continuous_snd.prodMk (continuous_subtype_val.comp continuous_fst)
    have hswapMem : ∀ z, swap z ∈ slab := by
      rintro ⟨t, x⟩
      exact ⟨Set.mem_univ x, habInterior t.2⟩
    have hfield : ContDiffOn ℝ ∞
        (Function.uncurry (coordinateJetField velocity n word)) slab :=
      openPeriodicSolutionOn_coordinateJetField_contDiffOn solution n word
    have hjet : Continuous (fun z : Icc a b × Space ↦
        coordinateJet velocity n word z.2 z.1.1) := by
      simpa [slab, swap, coordinateJetField, Function.comp_def] using
        hfield.continuousOn.comp_continuous hswap hswapMem
    have hderivative : ContDiffOn ℝ ∞
        (fderiv ℝ (Function.uncurry (coordinateJetField velocity n word))) slab :=
      hfield.fderiv_of_isOpen hopen (by simp)
    have htimeOn : ContinuousOn
        (fun z ↦ fderiv ℝ (Function.uncurry (coordinateJetField velocity n word)) z
          (0, 1)) slab :=
      (hderivative.clm_apply contDiffOn_const).continuousOn
    have htime : Continuous (fun z : Icc a b × Space ↦
        eulerianTimeJet (coordinateJetField velocity n word) z.2 z.1.1) := by
      simpa [slab, swap, eulerianTimeJet, Function.comp_def] using
        htimeOn.comp_continuous hswap hswapMem
    have hdensity : Continuous (Function.uncurry
        (fun t : Icc a b ↦ fun x : Space ↦
          inner ℝ
            (eulerianTimeJet (coordinateJetField velocity n word) x t.1)
            (coordinateJet velocity n word x t.1))) := by
      exact htime.inner hjet
    exact continuous_parametric_integral_of_continuous hdensity hcubeCompact
  have hrestricted : Continuous (fun t : Icc a b ↦
      ∑ word : Fin n → Fin 3,
        ∫ x in unitCube,
          inner ℝ
            (eulerianTimeJet (coordinateJetField velocity n word) x t.1)
            (coordinateJet velocity n word x t.1)) := by
    apply continuous_finset_sum
    intro word _hword
    exact hword word
  have hcontinuousOn : ContinuousOn
      (fun t ↦ ∑ word : Fin n → Fin 3,
        ∫ x in unitCube,
          inner ℝ
            (eulerianTimeJet (coordinateJetField velocity n word) x t)
            (coordinateJet velocity n word x t)) (Icc a b) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact hrestricted
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  exact hcontinuousOn.integrableOn_compact isCompact_Icc

theorem openPeriodicSolutionOn_coordinateH3ViscousDissipation_intervalIntegrable
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) :
    IntervalIntegrable (coordinateH3ViscousDissipation velocity) volume a b := by
  have hzero := openPeriodicSolutionOn_coordinateH0Dissipation_intervalIntegrable
    solution ha hab hbT
  have hone := openPeriodicSolutionOn_coordinateOrderDissipation_intervalIntegrable
    solution ha hab hbT 1
  have htwo := openPeriodicSolutionOn_coordinateOrderDissipation_intervalIntegrable
    solution ha hab hbT 2
  change IntervalIntegrable
    (fun t ↦ (coordinateH0Dissipation velocity t +
      coordinateH1Dissipation velocity t) + coordinateH2Dissipation velocity t)
    volume a b
  simpa [coordinateH1Dissipation, coordinateH2Dissipation] using
    (hzero.add hone).add htwo

private theorem openPeriodicSolutionOn_coordinateH2TotalTimeWork_intervalIntegrable
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) :
    IntervalIntegrable (coordinateH2TotalTimeWork velocity) volume a b := by
  have hzero := openPeriodicSolutionOn_coordinateOrderTimeWork_intervalIntegrable
    solution ha hab hbT 0
  have hone := openPeriodicSolutionOn_coordinateOrderTimeWork_intervalIntegrable
    solution ha hab hbT 1
  have htwo := openPeriodicSolutionOn_coordinateOrderTimeWork_intervalIntegrable
    solution ha hab hbT 2
  change IntervalIntegrable
    (fun t ↦ (coordinateH0TimeWork velocity t + coordinateH1TimeWork velocity t) +
      coordinateH2TimeWork velocity t) volume a b
  simpa [coordinateH0TimeWork, coordinateH1TimeWork, coordinateH2TimeWork] using
    (hzero.add hone).add htwo

theorem openPeriodicSolutionOn_coordinateH2NonlinearProductionCurrent_intervalIntegrable
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) :
    IntervalIntegrable (coordinateH2NonlinearProductionCurrent velocity) volume a b := by
  have hwork := openPeriodicSolutionOn_coordinateH2TotalTimeWork_intervalIntegrable
    solution ha hab hbT
  have hdiss := openPeriodicSolutionOn_coordinateH3ViscousDissipation_intervalIntegrable
    solution ha hab hbT
  apply (hwork.add (hdiss.const_mul nu)).congr_uIoo
  intro t ht
  rw [uIoo_of_le hab] at ht
  have hproduction :=
    openPeriodicSolutionOn_unforced_coordinateH2TotalTimeWork_eq_production solution
      ⟨ha.trans ht.1, ht.2.trans hbT⟩
  change coordinateH2TotalTimeWork velocity t +
    nu * coordinateH3ViscousDissipation velocity t =
      coordinateH2NonlinearProductionCurrent velocity t
  rw [hproduction]
  ring

/-! ## Exact compact balance and the remaining endpoint estimate -/

/-- **[proved-derived; formal-checked] Exact compact-interior H2--H3 balance.** -/
theorem openPeriodicSolutionOn_coordinateH2Energy_add_H3Dissipation_eq
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) :
    coordinateH2Energy velocity b +
        nu * ∫ t in a..b, coordinateH3ViscousDissipation velocity t =
      coordinateH2Energy velocity a +
        ∫ t in a..b, coordinateH2NonlinearProductionCurrent velocity t := by
  have hdiss := openPeriodicSolutionOn_coordinateH3ViscousDissipation_intervalIntegrable
    solution ha hab hbT
  have hproduction :=
    openPeriodicSolutionOn_coordinateH2NonlinearProductionCurrent_intervalIntegrable
      solution ha hab hbT
  have hrate : IntervalIntegrable
      (fun t ↦ -nu * coordinateH3ViscousDissipation velocity t +
        coordinateH2NonlinearProductionCurrent velocity t) volume a b :=
    (hdiss.const_mul (-nu)).add hproduction
  have hderiv : ∀ t ∈ [[a, b]],
      HasDerivAt (coordinateH2Energy velocity)
        (-nu * coordinateH3ViscousDissipation velocity t +
          coordinateH2NonlinearProductionCurrent velocity t) t := by
    intro t ht
    have ht' : t ∈ Icc a b := by simpa [uIcc_of_le hab] using ht
    exact openPeriodicSolutionOn_hasDerivAt_coordinateH2Energy_eq_production solution
      ⟨ha.trans_le ht'.1, ht'.2.trans_lt hbT⟩
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hrate
  rw [intervalIntegral.integral_add (hdiss.const_mul (-nu)) hproduction,
    intervalIntegral.integral_const_mul] at hftc
  linarith

/-- The exact source-specific estimate which closes the viscous current on one interval: an upper
bound on the signed nonlinear production integral.  No estimate of that current is assumed by the
PDE carrier itself. -/
theorem openPeriodicSolutionOn_integral_coordinateH3ViscousDissipation_le_of_production
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) {a b productionBudget : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (hproduction :
      (∫ t in a..b, coordinateH2NonlinearProductionCurrent velocity t) ≤
        productionBudget) :
    (∫ t in a..b, coordinateH3ViscousDissipation velocity t) ≤
      nu⁻¹ * (coordinateH2Energy velocity a + productionBudget) := by
  have hbalance := openPeriodicSolutionOn_coordinateH2Energy_add_H3Dissipation_eq
    solution ha hab hbT
  have hterminal := coordinateH2Energy_nonneg velocity b
  have hpaid :
      nu * (∫ t in a..b, coordinateH3ViscousDissipation velocity t) ≤
        coordinateH2Energy velocity a + productionBudget := by
    linarith
  calc
    (∫ t in a..b, coordinateH3ViscousDissipation velocity t) =
        nu⁻¹ * (nu * ∫ t in a..b,
          coordinateH3ViscousDissipation velocity t) := by
      field_simp
    _ ≤ nu⁻¹ * (coordinateH2Energy velocity a + productionBudget) :=
      mul_le_mul_of_nonneg_left hpaid (inv_nonneg.mpr hnu.le)

/-- Endpoint-uniformity from a fixed positive anchor is therefore *exactly reduced* to a uniform
upper budget for the signed nonlinear production current.  This theorem does not manufacture or
rename that missing source estimate. -/
theorem openPeriodicSolutionOn_coordinateH3ViscousDissipation_endpointUniform_of_productionBudget
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) {a productionBudget : ℝ} (ha : 0 < a) (_haT : a < T)
    (hproduction : ∀ b, a ≤ b → b < T →
      (∫ t in a..b, coordinateH2NonlinearProductionCurrent velocity t) ≤
        productionBudget) :
    ∀ b, a ≤ b → b < T →
      (∫ t in a..b, coordinateH3ViscousDissipation velocity t) ≤
        nu⁻¹ * (coordinateH2Energy velocity a + productionBudget) := by
  intro b hab hbT
  exact openPeriodicSolutionOn_integral_coordinateH3ViscousDissipation_le_of_production
    solution hnu ha hab hbT (hproduction b hab hbT)

/-- Uniformity while *both* compact faces move exposes both surviving payments separately.  The
left boundary storage must have a uniform trace budget, and the signed nonlinear current must
have a uniform upper budget.  These are the precise two source-specific estimates; neither is a
consequence of the algebraic clock separator or of periodic cancellation alone. -/
theorem openPeriodicSolutionOn_coordinateH3ViscousDissipation_allCompactIntervals_of_budgets
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (boundaryBudget productionBudget : ℝ)
    (hboundary : ∀ a, 0 < a → a < T →
      coordinateH2Energy velocity a ≤ boundaryBudget)
    (hproduction : ∀ a b, 0 < a → a ≤ b → b < T →
      (∫ t in a..b, coordinateH2NonlinearProductionCurrent velocity t) ≤
        productionBudget) :
    ∀ a b, 0 < a → a ≤ b → b < T →
      (∫ t in a..b, coordinateH3ViscousDissipation velocity t) ≤
        nu⁻¹ * (boundaryBudget + productionBudget) := by
  intro a b ha hab hbT
  have hlocal :=
    openPeriodicSolutionOn_integral_coordinateH3ViscousDissipation_le_of_production
      solution hnu ha hab hbT (hproduction a b ha hab hbT)
  exact hlocal.trans (mul_le_mul_of_nonneg_left
    (add_le_add (hboundary a ha (hab.trans_lt hbT)) (le_refl productionBudget))
    (inv_nonneg.mpr hnu.le))

section Audit

#print axioms openPeriodicSolutionOn_hasDerivAt_coordinateH2Energy_eq_production
#print axioms openPeriodicSolutionOn_coordinateH3ViscousDissipation_intervalIntegrable
#print axioms openPeriodicSolutionOn_coordinateH2Energy_add_H3Dissipation_eq
#print axioms openPeriodicSolutionOn_integral_coordinateH3ViscousDissipation_le_of_production
#print axioms
  openPeriodicSolutionOn_coordinateH3ViscousDissipation_endpointUniform_of_productionBudget
#print axioms
  openPeriodicSolutionOn_coordinateH3ViscousDissipation_allCompactIntervals_of_budgets

end Audit

end Soma.Holonics.Millennium.NavierStokesOpenH2EnergyH3Dissipation
