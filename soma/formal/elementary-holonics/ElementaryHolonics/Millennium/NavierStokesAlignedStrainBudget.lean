import ElementaryHolonics.Millennium.NavierStokesTransportedScalarMaximumPrinciple
import ElementaryHolonics.Millennium.NavierStokesCriticalOfficialPassage
import ElementaryHolonics.Millennium.NavierStokesInitialCriticalVorticityIntegrability
import ElementaryHolonics.Millennium.NavierStokesFiniteTimeEnstrophy
import ElementaryHolonics.Millennium.NavierStokesVorticityCanonicalCriticalBridge
import ElementaryHolonics.Millennium.NavierStokesForceObstruction
import ElementaryHolonics.Millennium.NavierStokesVorticityCanonicalModulus
import ElementaryHolonics.Millennium.NavierStokesVorticityCanonicalTime
import ElementaryHolonics.Millennium.NavierStokesVorticityDirectionPhysicalBridge
import ElementaryHolonics.Millennium.NavierStokesH2StorageDissipationPayment

/-!
# The aligned strain differential budgets the critical vorticity

The vortex-stretching term of the periodic Navier--Stokes vorticity equation is
`⟪(ω · ∇) u, ω⟫`.  Read along the vorticity's own frame it is the quadratic form of the strain
differential, the symmetric part of the velocity differential, on the vorticity: compression and
rotation along the frame cost nothing, and only extension is a source.  This module names that
signed receiver, the *aligned strain differential*, and proves that a continuous time budget for
it on any terminal tail controls the critical vorticity receiver and therefore returns the
existing compatible extension.

**Mechanism.**  The squared vorticity magnitude `q = ‖ω‖²` is a transported scalar with source:
its time and transport differentials come from the pointwise vorticity balance already proved on
every closed slab strictly inside the lifespan, its Laplacian dominates `2⟪ω, Δω⟫` by the exact
identity `Δ‖ω‖² = 2⟪ω, Δω⟫ + 2 Σᵢ ‖∂ᵢ ω‖²` proved here, and the stretching term is the aligned
strain differential.  The weighted maximum principle of the transported-scalar owner then bounds
`‖ω‖` on the tail by its value at the start of the tail times `exp ∫ A`.  The initial face is
already paid by `intervalIntegrable_criticalVorticityRate_initial`.

**Boundary.**  This is a conditional theorem.  Its hypothesis, `AlignedStrainBudget`, is a signed
receiver-relative quantity that is strictly weaker than an unsigned bound on the strain and is not
asserted to hold for every solution.  Nothing here claims Navier--Stokes regularity.
-/

noncomputable section

open ContDiff Set InnerProductSpace Filter Topology MeasureTheory
open scoped Laplacian

namespace Soma.Holonics.Millennium.NavierStokesAlignedStrainBudget

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPeriodicEnergy
open Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy
open Soma.Holonics.Millennium.NavierStokesFiniteTimeVorticity
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesCriticalVorticityRate
open Soma.Holonics.Millennium.NavierStokesVorticityCanonicalCriticalBridge
open Soma.Holonics.Millennium.NavierStokesInitialCriticalVorticityIntegrability
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeCompletedKernelPassage
open Soma.Holonics.Millennium.NavierStokesCriticalOfficialPassage
open Soma.Holonics.Millennium.NavierStokesForceObstruction
open Soma.Holonics.Millennium.NavierStokesTransportedScalarMaximumPrinciple
open Soma.Holonics.Millennium.NavierStokesVorticityCanonicalModulus
open Soma.Holonics.Millennium.NavierStokesVorticityCanonicalTime
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionPhysicalBridge
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionEnstrophyClosure
open Soma.Holonics.Millennium.NavierStokesH2StorageDissipationPayment

/-! ## Differentials along an affine line -/

section Line

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- [definition] The affine line through `x` in the direction `v`. -/
def line (x v : Space) (t : ℝ) : Space := x + t • v

theorem line_zero (x v : Space) : line x v 0 = x := by simp [line]

theorem hasDerivAt_line (x v : Space) (t : ℝ) : HasDerivAt (line x v) v t := by
  have h := ((hasDerivAt_id t).smul_const v).const_add x
  rw [one_smul] at h
  exact h

/-- [proved-derived; formal-checked] The differential of a `C²` field along a line. -/
theorem hasDerivAt_comp_line (f : Space → F) (hf : ContDiff ℝ 2 f) (x v : Space) (t : ℝ) :
    HasDerivAt (fun s => f (line x v s)) (fderiv ℝ f (line x v t) v) t :=
  ((hf.differentiable (by norm_num)) (line x v t)).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_line x v t)

/-- [proved-derived; formal-checked] The second differential along a line at its base point is
the iterated differential applied twice to the direction. -/
theorem hasDerivAt_fderiv_comp_line (f : Space → F) (hf : ContDiff ℝ 2 f) (x v : Space) :
    HasDerivAt (fun s => fderiv ℝ f (line x v s) v) (fderiv ℝ (fderiv ℝ f) x v v) 0 := by
  have hDf : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hDfd : Differentiable ℝ (fderiv ℝ f) := hDf.differentiable one_ne_zero
  have hKv' : fderiv ℝ (fun y => fderiv ℝ f y v) x v = fderiv ℝ (fderiv ℝ f) x v v := by
    rw [fderiv_clm_apply (hDfd x) (differentiableAt_const v)]
    simp
  have hKv : DifferentiableAt ℝ (fun y => fderiv ℝ f y v) (line x v 0) := by
    rw [line_zero]
    exact (hDfd x).clm_apply (differentiableAt_const v)
  have h := hKv.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_line x v 0)
  rw [line_zero, hKv'] at h
  exact h

end Line

/-! ## The Laplacian of the squared magnitude -/

/-- [proved-derived; formal-checked] Second differential of `‖ω‖²` in one direction. -/
theorem second_directional_norm_sq (w : Space → Space) (hw : ContDiff ℝ 2 w) (x v : Space) :
    fderiv ℝ (fderiv ℝ (fun y => ‖w y‖ ^ 2)) x v v =
      2 * inner ℝ (w x) (fderiv ℝ (fderiv ℝ w) x v v) + 2 * ‖fderiv ℝ w x v‖ ^ 2 := by
  have hq : ContDiff ℝ 2 (fun y => ‖w y‖ ^ 2) := ContDiff.norm_sq (𝕜 := ℝ) hw
  have hqline : deriv (deriv (fun s => ‖w (line x v s)‖ ^ 2)) 0 =
      fderiv ℝ (fderiv ℝ (fun y => ‖w y‖ ^ 2)) x v v := by
    have h1 : deriv (fun s => ‖w (line x v s)‖ ^ 2) =
        fun s => fderiv ℝ (fun y => ‖w y‖ ^ 2) (line x v s) v :=
      funext fun s => (hasDerivAt_comp_line (fun y => ‖w y‖ ^ 2) hq x v s).deriv
    rw [h1]
    exact (hasDerivAt_fderiv_comp_line (fun y => ‖w y‖ ^ 2) hq x v).deriv
  have hline : ∀ s, HasDerivAt (fun s => w (line x v s)) (fderiv ℝ w (line x v s) v) s :=
    hasDerivAt_comp_line w hw x v
  have h1' : deriv (fun s => ‖w (line x v s)‖ ^ 2) =
      fun s => 2 * inner ℝ (w (line x v s)) (fderiv ℝ w (line x v s) v) :=
    funext fun s => (HasDerivAt.norm_sq (hline s)).deriv
  have h2 : HasDerivAt (fun s => 2 * inner ℝ (w (line x v s)) (fderiv ℝ w (line x v s) v))
      (2 * (inner ℝ (w (line x v 0)) (fderiv ℝ (fderiv ℝ w) x v v) +
        inner ℝ (fderiv ℝ w (line x v 0) v) (fderiv ℝ w (line x v 0) v))) 0 :=
    (HasDerivAt.inner (𝕜 := ℝ) (hline 0) (hasDerivAt_fderiv_comp_line w hw x v)).const_mul 2
  rw [← hqline, h1', h2.deriv, line_zero, real_inner_self_eq_norm_sq]
  ring

/-- [proved-derived; formal-checked] `Δ‖ω‖² = 2⟪ω, Δω⟫ + 2 Σᵢ ‖∂ᵢ ω‖²` for a `C²` vector field. -/
theorem laplacian_norm_sq (w : Space → Space) (hw : ContDiff ℝ 2 w) (x : Space) :
    Δ (fun y => ‖w y‖ ^ 2) x =
      2 * inner ℝ (w x) (Δ w x) +
        2 * ∑ i, ‖fderiv ℝ w x (EuclideanSpace.basisFun (Fin 3) ℝ i)‖ ^ 2 := by
  rw [congrFun (laplacian_eq_iteratedFDeriv_orthonormalBasis (fun y => ‖w y‖ ^ 2)
    (EuclideanSpace.basisFun (Fin 3) ℝ)) x,
    congrFun (laplacian_eq_iteratedFDeriv_orthonormalBasis w
    (EuclideanSpace.basisFun (Fin 3) ℝ)) x, inner_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iteratedFDeriv_two_apply, iteratedFDeriv_two_apply]
  exact second_directional_norm_sq w hw x (EuclideanSpace.basisFun (Fin 3) ℝ i)

/-- [proved-derived; formal-checked] The Laplacian of the squared magnitude dominates twice the
magnitude's pairing with the vector Laplacian. -/
theorem two_mul_inner_laplacian_le_laplacian_norm_sq (w : Space → Space) (hw : ContDiff ℝ 2 w)
    (x : Space) :
    2 * inner ℝ (w x) (Δ w x) ≤ Δ (fun y => ‖w y‖ ^ 2) x := by
  rw [laplacian_norm_sq w hw x]
  have : 0 ≤ ∑ i, ‖fderiv ℝ w x (EuclideanSpace.basisFun (Fin 3) ℝ i)‖ ^ 2 :=
    Finset.sum_nonneg fun i _ => by positivity
  linarith

/-! ## The squared vorticity on the open lifespan -/

variable {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}

/-- [proved-derived; formal-checked] Interior joint smoothness of the vorticity at one event. -/
theorem vorticity_contDiffAt_interior
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (x : Space) {t : ℝ} (ht : t ∈ Ioo 0 T) :
    ContDiffAt ℝ ∞ (Function.uncurry (vorticityField velocity)) (x, t) :=
  (NavierStokesTorusVorticity.openPeriodicSolutionOn_vorticityField_contDiffOn_interior solution).contDiffAt
    ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ x, ht⟩)

/-- [proved-derived; formal-checked] The spatial vorticity slice is `C²` at interior times. -/
theorem vorticitySlice_contDiff
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    ContDiff ℝ 2 (fun y => vorticityField velocity y t) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  have hjoint : ContDiffAt ℝ 2 (Function.uncurry (vorticityField velocity)) (x, t) :=
    (vorticity_contDiffAt_interior solution x ht).of_le (WithTop.coe_le_coe.mpr le_top)
  have hpair : ContDiffAt ℝ 2 (fun y : Space => (y, t)) x :=
    contDiffAt_id.prodMk contDiffAt_const
  simpa [Function.comp_def] using hjoint.comp x hpair

/-- [proved-derived; formal-checked] The time differential of the vorticity at an interior event is
the Eulerian time jet. -/
theorem hasDerivAt_vorticity_time
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (x : Space) {t : ℝ} (ht : t ∈ Ioo 0 T) :
    HasDerivAt (fun s => vorticityField velocity x s)
      (eulerianTimeJet (vorticityField velocity) x t) t := by
  have hjoint :=
    ((vorticity_contDiffAt_interior solution x ht).differentiableAt (by simp)).hasFDerivAt
  have h := hjoint.comp_hasDerivAt t (hasFDerivAt_prodMk_right (𝕜 := ℝ) x t).hasDerivAt
  simpa [eulerianTimeJet, Function.comp_def] using h

/-- [definition] The aligned strain differential: the stretching term read along the vorticity's
own frame, `⟪(ω · ∇) u, ω⟫`.  By `inner_matrixAction_curl_eq_symmetricPart` only the symmetric
part of the velocity differential contributes. -/
def alignedStrain (velocity : VelocityField) (x : Space) (t : ℝ) : ℝ :=
  inner ℝ (fderiv ℝ (fun y => velocity y t) x (vorticityField velocity x t))
    (vorticityField velocity x t)

/-- [proved-derived; formal-checked] The squared vorticity magnitude is a transported scalar whose
only source is twice the aligned strain differential; viscosity enters with the sign of a
subsolution. -/
theorem vorticitySquare_law
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 ≤ nu) (x : Space) {t : ℝ} (ht : t ∈ Ioo 0 T) :
    derivWithin (fun s => ‖vorticityField velocity x s‖ ^ 2) (openTimeSlab T) t +
        fderiv ℝ (fun y => ‖vorticityField velocity y t‖ ^ 2) x (velocity x t) ≤
      2 * alignedStrain velocity x t +
        nu * Δ (fun y => ‖vorticityField velocity y t‖ ^ 2) x := by
  -- the closed slab strictly inside the lifespan carries the pointwise balance
  set S : ℝ := (t + T) / 2 with hS
  have hS0 : 0 < S := by rw [hS]; linarith [ht.1, ht.2]
  have hST : S < T := by rw [hS]; linarith [ht.2]
  have htS : t < S := by rw [hS]; linarith [ht.2]
  have hbal := smoothSolutionOn_pointwiseVorticityBalance_inner
    (solution.toClosedInterior hS0 hST).toSmoothSolutionOn ht.1 htS x
  rw [vorticityField_zero, inner_zero_left, add_zero] at hbal
  -- time differential
  have hnhds : openTimeSlab T ∈ 𝓝 t :=
    Filter.mem_of_superset (Ioo_mem_nhds ht.1 ht.2) Ioo_subset_Ico_self
  have htime : derivWithin (fun s => ‖vorticityField velocity x s‖ ^ 2) (openTimeSlab T) t =
      2 * inner ℝ (vorticityField velocity x t) (eulerianTimeJet (vorticityField velocity) x t) := by
    rw [derivWithin_of_mem_nhds hnhds]
    exact (HasDerivAt.norm_sq (hasDerivAt_vorticity_time solution x ht)).deriv
  -- spatial differential
  have hslice := vorticitySlice_contDiff solution ht
  have hspace : fderiv ℝ (fun y => ‖vorticityField velocity y t‖ ^ 2) x (velocity x t) =
      2 * inner ℝ (vorticityField velocity x t)
        (fderiv ℝ (fun y => vorticityField velocity y t) x (velocity x t)) := by
    rw [(HasFDerivAt.norm_sq ((hslice.differentiable (by norm_num)) x).hasFDerivAt).fderiv]
    simp [innerSL_apply_apply, two_smul]
    try ring
  -- Laplacian
  have hlap := two_mul_inner_laplacian_le_laplacian_norm_sq
    (fun y => vorticityField velocity y t) hslice x
  have hnuLap := mul_le_mul_of_nonneg_left hlap hnu
  rw [htime, hspace]
  unfold alignedStrain
  rw [real_inner_comm (vorticityField velocity x t) (eulerianTimeJet (vorticityField velocity) x t),
    real_inner_comm (vorticityField velocity x t)
      (fderiv ℝ (fun y => vorticityField velocity y t) x (velocity x t)),
    real_inner_comm (vorticityField velocity x t)
      (Δ (fun y => vorticityField velocity y t) x)] at hbal
  linarith

/-! ## The budget and its return -/

/-- [definition] A time budget for the aligned strain differential on a terminal tail.  The budget
is measurable, continuous on the open tail, and interval-integrable up to the terminal face; it
dominates the signed receiver relative to the squared magnitude.  It does not bound the strain
itself, and it is only required to be integrable, not bounded. -/
structure AlignedStrainBudget
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure) where
  start : ℝ
  start_pos : 0 < start
  start_lt : start < T
  budget : ℝ → ℝ
  budget_measurable : Measurable budget
  budget_continuousOn : ContinuousOn budget (Ioo start T)
  budget_integrable : IntervalIntegrable budget volume start T
  dominates : ∀ x, ∀ t ∈ Ioo start T,
    alignedStrain velocity x t ≤ budget t * ‖vorticityField velocity x t‖ ^ 2

namespace AlignedStrainBudget

variable {solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure}

/-- [definition] The budget clipped to the open tail, so that its primitive is globally defined. -/
def clipped (B : AlignedStrainBudget solution) (t : ℝ) : ℝ :=
  Set.indicator (Ioo B.start T) B.budget t

theorem clipped_eq (B : AlignedStrainBudget solution) {t : ℝ} (ht : t ∈ Ioo B.start T) :
    B.clipped t = B.budget t :=
  Set.indicator_of_mem ht _

theorem clipped_measurable (B : AlignedStrainBudget solution) : Measurable B.clipped :=
  B.budget_measurable.indicator measurableSet_Ioo

theorem clipped_integrable (B : AlignedStrainBudget solution) : Integrable B.clipped volume := by
  show Integrable (Set.indicator (Ioo B.start T) B.budget) volume
  rw [integrable_indicator_iff measurableSet_Ioo]
  exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le B.start_lt.le).1
    B.budget_integrable).mono_set Ioo_subset_Ioc_self

/-- [definition] The accumulated budget from the start of the tail. -/
def accumulated (B : AlignedStrainBudget solution) (t : ℝ) : ℝ :=
  ∫ τ in B.start..t, B.clipped τ

theorem continuous_accumulated (B : AlignedStrainBudget solution) : Continuous B.accumulated :=
  intervalIntegral.continuous_primitive (fun _ _ => B.clipped_integrable.intervalIntegrable)
    B.start

theorem hasDerivAt_accumulated (B : AlignedStrainBudget solution) {t : ℝ}
    (ht : t ∈ Ioo B.start T) :
    HasDerivAt B.accumulated (B.budget t) t := by
  have hev : B.clipped =ᶠ[𝓝 t] B.budget := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact B.clipped_eq hs
  have hcont : ContinuousAt B.clipped t :=
    (B.budget_continuousOn.continuousAt (isOpen_Ioo.mem_nhds ht)).congr_of_eventuallyEq hev
  have hint : IntervalIntegrable B.clipped volume B.start t :=
    B.clipped_integrable.intervalIntegrable
  have h := intervalIntegral.integral_hasDerivAt_right hint
    B.clipped_measurable.stronglyMeasurable.stronglyMeasurableAtFilter hcont
  rw [B.clipped_eq ht] at h
  exact h

/-- [definition] The exponential weight `exp (-2 ∫ A)` that removes the source. -/
def weight (B : AlignedStrainBudget solution) (t : ℝ) : ℝ :=
  Real.exp (-(2 * B.accumulated t))

theorem weight_pos (B : AlignedStrainBudget solution) (t : ℝ) : 0 < B.weight t :=
  Real.exp_pos _

theorem weight_start (B : AlignedStrainBudget solution) : B.weight B.start = 1 := by
  show Real.exp (-(2 * ∫ τ in B.start..B.start, B.clipped τ)) = 1
  rw [intervalIntegral.integral_same, mul_zero, neg_zero, Real.exp_zero]

theorem continuous_weight (B : AlignedStrainBudget solution) : Continuous B.weight :=
  Real.continuous_exp.comp (continuous_const.mul B.continuous_accumulated).neg

theorem hasDerivAt_weight (B : AlignedStrainBudget solution) {t : ℝ} (ht : t ∈ Ioo B.start T) :
    HasDerivAt B.weight (-(2 * B.budget t * B.weight t)) t := by
  have h1 : HasDerivAt (fun s => -(2 * B.accumulated s)) (-(2 * B.budget t)) t :=
    ((B.hasDerivAt_accumulated ht).const_mul 2).neg
  have h2 := h1.exp
  have hfun : B.weight = fun s => Real.exp (-(2 * B.accumulated s)) := rfl
  rw [hfun]
  convert h2 using 1
  ring

/-- [proved-derived; formal-checked] **The aligned strain budget bounds the vorticity on the
tail.**  On `Ico start T` the vorticity magnitude never exceeds its critical receiver at the start
of the tail times `exp` of the accumulated budget. -/
theorem norm_vorticity_le (B : AlignedStrainBudget solution) (hnu : 0 ≤ nu) (x : Space)
    {t : ℝ} (ht : t ∈ Ico B.start T) :
    ‖vorticityField velocity x t‖ ≤
      criticalVorticityRate solution B.start * Real.exp (B.accumulated t) := by
  have hstart : B.start ∈ Ioo 0 T := ⟨B.start_pos, B.start_lt⟩
  have hsub : (Set.univ : Set Space) ×ˢ Ico B.start T ⊆ (Set.univ : Set Space) ×ˢ Ioo 0 T := by
    rintro ⟨y, s⟩ ⟨_, hs⟩
    exact ⟨mem_univ y, lt_of_lt_of_le B.start_pos hs.1, hs.2⟩
  have hbound := transportedSubsolution_mul_weight_le_of_le_at hnu B.start_pos.le
    (fun y s => ‖vorticityField velocity y s‖ ^ 2) velocity B.budget B.weight
    (by
      show ContinuousOn (fun p : Space × ℝ => ‖Function.uncurry (vorticityField velocity) p‖ ^ 2)
        (Set.univ ×ˢ Ico B.start T)
      exact (((NavierStokesTorusVorticity.openPeriodicSolutionOn_vorticityField_contDiffOn_interior
        solution).continuousOn.mono
        hsub).norm).pow 2)
    (fun s hs => ContDiff.norm_sq (𝕜 := ℝ)
      (vorticitySlice_contDiff solution ⟨lt_trans B.start_pos hs.1, hs.2⟩))
    (fun y s hs =>
      (HasDerivAt.norm_sq
        (hasDerivAt_vorticity_time solution y ⟨lt_trans B.start_pos hs.1, hs.2⟩)).differentiableAt)
    (fun s hs y i => by
      have := openPeriodicSolutionOn_vorticityField_isOnePeriodic solution
        ⟨lt_of_lt_of_le B.start_pos hs.1, hs.2⟩ y i
      simp only at this ⊢
      rw [this])
    B.continuous_weight B.weight_pos B.weight_start
    (fun s hs => B.hasDerivAt_weight hs)
    (fun y s hs => by
      have hlaw := vorticitySquare_law solution hnu y ⟨lt_trans B.start_pos hs.1, hs.2⟩
      have hdom := B.dominates y s hs
      linarith)
    (criticalVorticityRate solution B.start ^ 2)
    (fun y => by
      have h := (criticalVorticityRate_le_iff solution hstart).1 le_rfl y
      exact pow_le_pow_left₀ (norm_nonneg _) h 2)
    x t ht
  have hC : 0 ≤ criticalVorticityRate solution B.start := criticalVorticityRate_nonneg solution _
  have hE := B.weight_pos t
  have hsq : ‖vorticityField velocity x t‖ ^ 2 ≤
      (criticalVorticityRate solution B.start * Real.exp (B.accumulated t)) ^ 2 := by
    have hexp : Real.exp (B.accumulated t) ^ 2 = (B.weight t)⁻¹ := by
      show Real.exp (B.accumulated t) ^ 2 = (Real.exp (-(2 * B.accumulated t)))⁻¹
      rw [← Real.exp_neg, ← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [mul_pow, hexp, ← div_eq_mul_inv, le_div_iff₀ hE]
    exact hbound
  exact le_trans (le_abs_self _)
    (abs_le_of_sq_le_sq hsq (mul_nonneg hC (Real.exp_pos _).le))

/-- [proved-derived; formal-checked] The critical vorticity receiver is interval-integrable on the
whole lifespan: the initial face is already paid unconditionally, and the budget bounds the tail. -/
theorem intervalIntegrable_criticalVorticityRate (B : AlignedStrainBudget solution)
    (hnu : 0 ≤ nu) :
    IntervalIntegrable (criticalVorticityRate solution) volume 0 T := by
  have hinit := intervalIntegrable_criticalVorticityRate_initial solution B.start_pos B.start_lt
  have htail : IntervalIntegrable (criticalVorticityRate solution) volume B.start T := by
    let g : ℝ → ℝ := fun t =>
      criticalVorticityRate solution B.start * Real.exp (B.accumulated t)
    have hg : Continuous g :=
      continuous_const.mul (Real.continuous_exp.comp B.continuous_accumulated)
    refine (hg.intervalIntegrable B.start T).mono_fun'
      ((criticalVorticityRate_measurable solution).aestronglyMeasurable.restrict) ?_
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_uIoc]
    refine Filter.Eventually.of_forall fun t ht => ?_
    rw [uIoc_of_le B.start_lt.le] at ht
    rw [Real.norm_of_nonneg (criticalVorticityRate_nonneg solution t)]
    have hg0 : 0 ≤ g t :=
      mul_nonneg (criticalVorticityRate_nonneg solution _) (Real.exp_pos _).le
    rcases eq_or_lt_of_le ht.2 with hT | hlt
    · have hout : t ∉ Ioo 0 T := fun h => by rw [hT] at h; exact lt_irrefl _ h.2
      simp only [criticalVorticityRate, hout, dite_false]
      exact hg0
    · have hint : t ∈ Ioo 0 T := ⟨lt_trans B.start_pos ht.1, hlt⟩
      exact (criticalVorticityRate_le_iff solution hint).2
        fun y => B.norm_vorticity_le hnu y ⟨ht.1.le, hlt⟩
  exact hinit.trans htail

/-- [proved-derived; formal-checked] An aligned strain budget returns the existing compatible
extension of the open periodic solution. -/
noncomputable def compatibleOpenPeriodicExtension (B : AlignedStrainBudget solution)
    (hnu : 0 < nu) : CompatibleOpenPeriodicExtension solution :=
  compatibleOpenPeriodicExtension_of_integrableCriticalVorticity solution hnu
    (B.intervalIntegrable_criticalVorticityRate hnu.le)

end AlignedStrainBudget

/-! ## The canonical budget: energy exterior, coherence interior -/

/-- [definition] The three-coordinate comparison cost: each passage from the coordinate `ℓ¹`
face to the Euclidean norm on `Fin 3` costs a factor `3` in the standing owners (the sharp cost
is `√3`).  The exponents below count those passages. -/
def coordinateComparison : ℝ := 3

/-- [definition] The exterior constant of the canonical budget: `2π` is the derivative multiplier
of the unit-torus character `e^{2πi k·x}`, and `3⁸` is eight coordinate comparisons.  It multiplies
`√(2E₀) = ‖u₀‖_{L²}`, the initial kinetic energy read as a norm. -/
def exteriorConstant : ℝ := 2 * Real.pi * coordinateComparison ^ 8

/-- [definition] The interior constant of the canonical budget: six coordinate comparisons, `3⁶`.
It multiplies the canonical vorticity derivative and the dyadic Hodge distance moment. -/
def interiorConstant : ℝ := coordinateComparison ^ 6

theorem exteriorConstant_eq : exteriorConstant = 13122 * Real.pi := by
  unfold exteriorConstant coordinateComparison
  ring

theorem interiorConstant_eq : interiorConstant = 729 := by
  unfold interiorConstant coordinateComparison
  norm_num

/-- [definition] The canonical budget.  Its first term is the exterior, low-frequency face of the
strain, paid by the initial kinetic energy alone and constant on the whole lifespan.  Its second
term is the interior, high-frequency face, paid by the canonical vorticity derivative through the
direction-coherence moment.  The constants are product expansions of the torus character
multiplier `2π` and the coordinate comparison `3`; they are those of the standing canonical
enstrophy coefficient. -/
def canonicalBudget
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : ℝ) : ℝ :=
  exteriorConstant * Real.sqrt (2 * periodicKineticEnergy velocity 0) +
    interiorConstant * openPeriodicCanonicalVorticityDerivativeRate solution t *
      totalDyadicHodgeDistanceMoment

theorem canonicalDerivativeRate_measurable
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure) :
    Measurable (openPeriodicCanonicalVorticityDerivativeRate solution) := by
  unfold openPeriodicCanonicalVorticityDerivativeRate
  exact (NNReal.continuous_coe.comp
    (openPeriodicCanonicalVorticityLipschitzConstant_continuous solution)).measurable.dite
      measurable_const measurableSet_Ioo

theorem canonicalDerivativeRate_continuousOn
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure) :
    ContinuousOn (openPeriodicCanonicalVorticityDerivativeRate solution) (Ioo 0 T) := by
  rw [continuousOn_iff_continuous_restrict]
  refine (NNReal.continuous_coe.comp
    (openPeriodicCanonicalVorticityLipschitzConstant_continuous solution)).congr ?_
  intro x
  exact (openPeriodicCanonicalVorticityDerivativeRate_eq solution x.2).symm

/-- [proved-derived; formal-checked] The aligned strain differential at every point is dominated
by the canonical budget times the squared vorticity magnitude.  The exterior face has already been
rebased to the initial energy. -/
theorem alignedStrain_le_canonicalBudget
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 ≤ nu) (x : Space) {t : ℝ} (ht : t ∈ Ioo 0 T) :
    alignedStrain velocity x t ≤
      canonicalBudget solution t * ‖vorticityField velocity x t‖ ^ 2 := by
  have hproj := openPeriodicPhysicalVortexStretchingAt_projection solution ⟨t, ht⟩ x
  have hbound := abs_openPeriodicPhysicalVortexStretchingAt_le_canonicalEnstrophyDensity
    solution ⟨t, ht⟩ (euclideanToSpatialTorus x)
  rw [torusVorticityEvolution_projection] at hbound
  have hcoef : openPeriodicCanonicalVorticityDirectionEnstrophyCoefficient solution ⟨t, ht⟩ ≤
      canonicalBudget solution t := by
    unfold openPeriodicCanonicalVorticityDirectionEnstrophyCoefficient canonicalBudget
    rw [openPeriodicCanonicalVorticityDerivativeRate_eq solution ht, exteriorConstant_eq,
      interiorConstant_eq]
    have hE := openPeriodicSolutionOn_periodicKineticEnergy_le_initial solution hnu ht
    have hsqrt : Real.sqrt (2 * periodicKineticEnergy velocity t) ≤
        Real.sqrt (2 * periodicKineticEnergy velocity 0) :=
      Real.sqrt_le_sqrt (by linarith)
    have hpi : 0 ≤ 13122 * Real.pi := by positivity
    have := mul_le_mul_of_nonneg_left hsqrt hpi
    linarith
  calc alignedStrain velocity x t
      = openPeriodicPhysicalVortexStretchingAt solution ⟨t, ht⟩ (euclideanToSpatialTorus x) :=
        hproj.symm
    _ ≤ |openPeriodicPhysicalVortexStretchingAt solution ⟨t, ht⟩ (euclideanToSpatialTorus x)| :=
        le_abs_self _
    _ ≤ openPeriodicCanonicalVorticityDirectionEnstrophyCoefficient solution ⟨t, ht⟩ *
          ‖vorticityField velocity x t‖ ^ 2 := hbound
    _ ≤ canonicalBudget solution t * ‖vorticityField velocity x t‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)

/-- [proved-derived; formal-checked] **Tail integrability of the canonical vorticity derivative
supplies an aligned strain budget.**  The exterior face costs a constant; only the interior face
enters the integral. -/
noncomputable def AlignedStrainBudget.ofCanonicalDerivativeRate
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 ≤ nu) {s : ℝ} (hs : 0 < s) (hsT : s < T)
    (hint : IntervalIntegrable (openPeriodicCanonicalVorticityDerivativeRate solution) volume s T) :
    AlignedStrainBudget solution where
  start := s
  start_pos := hs
  start_lt := hsT
  budget := canonicalBudget solution
  budget_measurable := by
    unfold canonicalBudget
    exact measurable_const.add
      ((measurable_const.mul (canonicalDerivativeRate_measurable solution)).mul measurable_const)
  budget_continuousOn := by
    unfold canonicalBudget
    exact continuousOn_const.add
      ((continuousOn_const.mul ((canonicalDerivativeRate_continuousOn solution).mono
        (Ioo_subset_Ioo_left hs.le))).mul continuousOn_const)
  budget_integrable := by
    unfold canonicalBudget
    exact intervalIntegrable_const.add ((hint.const_mul _).mul_const _)
  dominates := fun x t ht =>
    alignedStrain_le_canonicalBudget solution hnu x ⟨lt_trans hs ht.1, ht.2⟩

/-- [proved-derived; formal-checked] The canonical derivative route factors through the aligned
strain receiver, and needs only tail integrability. -/
noncomputable def compatibleOpenPeriodicExtension_of_canonicalDerivativeRate_tail
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) {s : ℝ} (hs : 0 < s) (hsT : s < T)
    (hint : IntervalIntegrable (openPeriodicCanonicalVorticityDerivativeRate solution) volume s T) :
    CompatibleOpenPeriodicExtension solution :=
  AlignedStrainBudget.compatibleOpenPeriodicExtension
    (AlignedStrainBudget.ofCanonicalDerivativeRate solution hnu.le hs hsT hint) hnu

/-! ## The universal budget as a receiver of the official finish line -/

/-- [project-postulate] Every positive-viscosity official periodic solution admits an aligned strain
budget on some terminal tail.  This is the signed, receiver-relative replacement of the unsigned
terminal Prop `CriticalVorticityTerminalControl`. -/
def AlignedStrainTerminalControl : Prop :=
  ∀ {T nu : ℝ} {initial : InitialVelocity}
    {velocity : VelocityField} {pressure : PressureField},
    0 < nu →
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure) →
      Nonempty (AlignedStrainBudget solution)

/-- [proved-derived; formal-checked] The aligned strain control returns the critical vorticity
control. -/
theorem criticalVorticityTerminalControl_of_alignedStrain
    (h : AlignedStrainTerminalControl) : CriticalVorticityTerminalControl := by
  intro T nu initial velocity pressure hnu _ solution
  obtain ⟨B⟩ := h hnu solution
  exact B.intervalIntegrable_criticalVorticityRate hnu.le

/-- [proved-derived; formal-checked, conditional] The aligned strain control is sufficient for
the literal official periodic existence receiver. -/
theorem statementB_of_alignedStrainTerminalControl (h : AlignedStrainTerminalControl) :
    StatementB :=
  statementB_of_criticalVorticityTerminalControl (criticalVorticityTerminalControl_of_alignedStrain h)

section Audit

#print axioms laplacian_norm_sq
#print axioms vorticitySquare_law
#print axioms AlignedStrainBudget.norm_vorticity_le
#print axioms AlignedStrainBudget.intervalIntegrable_criticalVorticityRate
#print axioms exteriorConstant_eq
#print axioms alignedStrain_le_canonicalBudget
#print axioms compatibleOpenPeriodicExtension_of_canonicalDerivativeRate_tail
#print axioms criticalVorticityTerminalControl_of_alignedStrain
#print axioms statementB_of_alignedStrainTerminalControl

end Audit

end Soma.Holonics.Millennium.NavierStokesAlignedStrainBudget
