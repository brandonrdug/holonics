import ElementaryHolonics.Millennium.NavierStokesEleventhMomentFromSmoothness
import ElementaryHolonics.Millennium.NavierStokesWordJetIsIteratedDerivative

/-!
# The eleventh moment is bounded on every compact time interval

The slice's spatial iterated derivative is the joint iterated derivative on the open space-time
slab composed with the spatial inclusion, so it is bounded on the compact set
`unitCube × [s, τ]` by continuity.  Parseval for the coordinate word jets of order seven turns
that bound into a bound on `Σ_q λ_q^7 ‖û_q‖²`, hence on the eleventh moment, uniformly on
`[s, τ]`.  With the previous owner, the coherence-defect tail control reduces to the defect
bound alone, and the official problem follows from it.
-/

open Set Filter Topology MeasureTheory
open scoped Finset ContDiff
open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesPeriodicFlux
open Soma.Holonics.Millennium.NavierStokesH3Production
open Soma.Holonics.Millennium.NavierStokesCoordinateH1Production
open Soma.Holonics.Millennium.NavierStokesSmoothSliceWeightedH3
open Soma.Holonics.Millennium.NavierStokesSmoothSliceWeightedAllOrders
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesModalRiccati
open Soma.Holonics.Millennium.NavierStokesHalfRadiusReach
open Soma.Holonics.Millennium.NavierStokesMomentSwap
open Soma.Holonics.Millennium.NavierStokesMomentGap
open Soma.Holonics.Millennium.NavierStokesMomentClosure
open Soma.Holonics.Millennium.NavierStokesIncoherentSource
open Soma.Holonics.Millennium.NavierStokesIncoherentClosure
open Soma.Holonics.Millennium.NavierStokesVelocityMassEnergy
open Soma.Holonics.Millennium.NavierStokesEleventhMomentFromSmoothness
open Soma.Holonics.Millennium.NavierStokesWordJetIsIteratedDerivative

namespace Soma.Holonics.Millennium.NavierStokesEleventhMomentCompactBound

variable {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
  {pressure : PressureField}
  (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)

/-! ## The slice derivative is the joint derivative on the open slab -/

/-- The open space-time slab. -/
def slab (T : ℝ) : Set (Space × ℝ) := univ ×ˢ Ioo 0 T

theorem isOpen_slab (T : ℝ) : IsOpen (slab T) := isOpen_univ.prod isOpen_Ioo

include solution in
theorem contDiffOn_slab : ContDiffOn ℝ ∞ (Function.uncurry velocity) (slab T) := by
  apply solution.velocitySmooth.mono
  rintro ⟨y, s⟩ ⟨_, hs⟩
  exact ⟨mem_univ y, hs.1.le, hs.2⟩

/-- The inclusion of a spatial slice. -/
noncomputable def spatialInl : Space →L[ℝ] Space × ℝ := ContinuousLinearMap.inl ℝ Space ℝ

theorem norm_spatialInl_le : ‖spatialInl‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    simp [spatialInl, Prod.norm_def]

include solution in
/-- For `σ ∈ (0, T)`, the slice's iterated derivative is the joint iterated derivative composed
with the spatial inclusion. -/
theorem iteratedFDeriv_slice_eq (n : ℕ) {σ : ℝ} (hσ : σ ∈ Ioo 0 T) (x : Space) :
    iteratedFDeriv ℝ n (fun y => velocity y σ) x =
      (iteratedFDeriv ℝ n (Function.uncurry velocity) (x, σ)).compContinuousLinearMap
        (fun _ => spatialInl) := by
  set S : Set (Space × ℝ) := {p | p + ((0 : Space), σ) ∈ slab T} with hS
  have hs' : IsOpen S := (isOpen_slab T).preimage (continuous_id.add continuous_const)
  have hF' : ContDiffOn ℝ ∞ (fun p => Function.uncurry velocity (p + ((0 : Space), σ))) S :=
    (contDiffOn_slab solution).comp (contDiff_id.add contDiff_const).contDiffOn fun p hp => hp
  have hpre : spatialInl ⁻¹' S = univ := by
    ext y
    simp [spatialInl, hS, slab, hσ.1, hσ.2]
  have hslice : (fun y => velocity y σ) =
      (fun p => Function.uncurry velocity (p + ((0 : Space), σ))) ∘ spatialInl := by
    funext y
    simp [spatialInl, Function.uncurry]
  have hmem : spatialInl x ∈ S := by
    have : x ∈ spatialInl ⁻¹' S := by rw [hpre]; exact mem_univ x
    exact this
  have h1 := spatialInl.iteratedFDerivWithin_comp_right hF' hs'.uniqueDiffOn
    (by rw [hpre]; exact uniqueDiffOn_univ) hmem (i := n) (WithTop.coe_le_coe.mpr le_top)
  rw [hpre, iteratedFDerivWithin_univ] at h1
  rw [hslice, h1]
  congr 1
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hs'.uniqueDiffOn
    ((hF'.contDiffAt (hs'.mem_nhds hmem)).of_le (WithTop.coe_le_coe.mpr le_top)) hmem, iteratedFDeriv_comp_add_right]
  congr 1
  simp [spatialInl]

include solution in
theorem norm_iteratedFDeriv_slice_le (n : ℕ) {σ : ℝ} (hσ : σ ∈ Ioo 0 T) (x : Space) :
    ‖iteratedFDeriv ℝ n (fun y => velocity y σ) x‖ ≤
      ‖iteratedFDeriv ℝ n (Function.uncurry velocity) (x, σ)‖ := by
  rw [iteratedFDeriv_slice_eq solution n hσ x]
  calc ‖(iteratedFDeriv ℝ n (Function.uncurry velocity) (x, σ)).compContinuousLinearMap
        (fun _ => spatialInl)‖
      ≤ ‖iteratedFDeriv ℝ n (Function.uncurry velocity) (x, σ)‖ * ∏ _i : Fin n, ‖spatialInl‖ :=
        ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
    _ ≤ ‖iteratedFDeriv ℝ n (Function.uncurry velocity) (x, σ)‖ * 1 := by
        gcongr
        exact Finset.prod_le_one (fun _ _ => norm_nonneg _) fun _ _ => norm_spatialInl_le
    _ = ‖iteratedFDeriv ℝ n (Function.uncurry velocity) (x, σ)‖ := mul_one _

/-! ## The compact bound -/

theorem isCompact_unitCube : IsCompact unitCube :=
  (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr isCompact_Icc

include solution in
theorem exists_bound_iteratedFDeriv (n : ℕ) {s τ : ℝ} (hs : 0 < s) (hτ : τ < T) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ σ ∈ Icc s τ, ∀ x ∈ unitCube,
      ‖iteratedFDeriv ℝ n (fun y => velocity y σ) x‖ ≤ M := by
  have hcont : ContinuousOn (iteratedFDeriv ℝ n (Function.uncurry velocity)) (slab T) := by
    have h := (contDiffOn_slab solution).continuousOn_iteratedFDerivWithin (m := n)
      (WithTop.coe_le_coe.mpr le_top) (isOpen_slab T).uniqueDiffOn
    refine h.congr fun p hp => ?_
    exact (iteratedFDerivWithin_eq_iteratedFDeriv (isOpen_slab T).uniqueDiffOn
      (((contDiffOn_slab solution).contDiffAt ((isOpen_slab T).mem_nhds hp)).of_le (WithTop.coe_le_coe.mpr le_top)) hp).symm
  have hK : IsCompact (unitCube ×ˢ Icc s τ) := isCompact_unitCube.prod isCompact_Icc
  have hKsub : unitCube ×ˢ Icc s τ ⊆ slab T := by
    rintro ⟨x, σ⟩ ⟨_, hσ⟩
    exact ⟨mem_univ x, by linarith [hσ.1], by linarith [hσ.2]⟩
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (hcont.mono hKsub)
  refine ⟨max M 0, le_max_right _ _, fun σ hσ x hx => ?_⟩
  calc ‖iteratedFDeriv ℝ n (fun y => velocity y σ) x‖
      ≤ ‖iteratedFDeriv ℝ n (Function.uncurry velocity) (x, σ)‖ :=
        norm_iteratedFDeriv_slice_le solution n ⟨by linarith [hσ.1], by linarith [hσ.2]⟩ x
    _ ≤ M := hM (x, σ) ⟨hx, hσ⟩
    _ ≤ max M 0 := le_max_left _ _

/-! ## Parseval turns the bound into the eleventh moment -/

include solution in
theorem moment_eleven_le_of_bound {σ : ℝ} (hσ : σ ∈ Ioo 0 T) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ x ∈ unitCube, ‖iteratedFDeriv ℝ 7 (fun y => velocity y σ) x‖ ≤ M) :
    moment (velocity := velocity) 11 σ ≤
      (2 * Real.pi) ^ 2 / (2 * Real.pi) ^ 14 *
        (3 * (3 ^ 7 * (M ^ 2 * volume.real unitCube))) := by
  set t : Ioo 0 T := ⟨σ, hσ⟩ with ht
  have hu := openPeriodicSolutionOn_velocitySlice_contDiff solution hσ
  have hper := solution.velocityPeriodic σ ⟨hσ.1.le, hσ.2⟩
  have h1 : moment (velocity := velocity) 11 σ ≤ (2 * Real.pi) ^ 2 / (2 * Real.pi) ^ 14 *
      ∑' q, torusStokesEigenvalue q ^ 7 * velPop solution t q := by
    unfold moment
    rw [← tsum_mul_left]
    exact Summable.tsum_le_tsum (fun q => by
        rw [← eleventhMoment_eq]
        exact eleventhMoment_le_stokes solution t q)
      (summable_eleventhMoment solution t)
      ((summable_stokes_pow_mul_velPop solution t 7).mul_left _)
  have hjet : ∀ word : Fin 7 → Fin 3, ∀ c : Fin 3,
      ∑' q, ‖smoothSliceFourierL2 (spatialCoordinateWordJet (fun y => velocity y σ) 7 word)
        (spatialCoordinateWordJet_contDiff _ hu 7 word)
        (spatialCoordinateWordJet_isOnePeriodic _ hper 7 word) c q‖ ^ 2 ≤
        M ^ 2 * volume.real unitCube := by
    intro word c
    rw [tsum_sq_smoothSliceFourierL2_eq_integral_unitCube]
    have hvol : volume unitCube < ⊤ := isCompact_unitCube.measure_lt_top
    have hpt : ∀ x ∈ unitCube,
        ‖(spatialCoordinateWordJet (fun y => velocity y σ) 7 word x c) ^ 2‖ ≤ M ^ 2 := by
      intro x hx
      rw [norm_pow]
      have h1 : ‖spatialCoordinateWordJet (fun y => velocity y σ) 7 word x c‖ ≤
          ‖spatialCoordinateWordJet (fun y => velocity y σ) 7 word x‖ := PiLp.norm_apply_le _ c
      have h2 := norm_spatialCoordinateWordJet_le _ hu 7 word x
      have h3 := hbound x hx
      exact pow_le_pow_left₀ (norm_nonneg _) (h1.trans (h2.trans h3)) 2
    calc ∫ x in unitCube, (spatialCoordinateWordJet (fun y => velocity y σ) 7 word x c) ^ 2
        ≤ ‖∫ x in unitCube, (spatialCoordinateWordJet (fun y => velocity y σ) 7 word x c) ^ 2‖ :=
          le_abs_self _
      _ ≤ M ^ 2 * volume.real unitCube := norm_setIntegral_le_of_norm_le_const hvol hpt
  have h2 : ∑' q, torusStokesEigenvalue q ^ 7 * velPop solution t q ≤
      3 * (3 ^ 7 * (M ^ 2 * volume.real unitCube)) := by
    have hsplit : (fun q => torusStokesEigenvalue q ^ 7 * velPop solution t q) =
        fun q => ∑ c : Fin 3, ∑ word : Fin 7 → Fin 3,
          ‖smoothSliceFourierL2 (spatialCoordinateWordJet (fun y => velocity y σ) 7 word)
            (spatialCoordinateWordJet_contDiff _ hu 7 word)
            (spatialCoordinateWordJet_isOnePeriodic _ hper 7 word) c q‖ ^ 2 := by
      funext q
      unfold velPop
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      rw [velocityMode_eq_smoothSliceFourierL2,
        sum_norm_sq_smoothSliceFourierL2_spatialCoordinateWordJet _ hu hper c 7 q]
    have hsumm : ∀ c ∈ (Finset.univ : Finset (Fin 3)), ∀ word ∈ (Finset.univ : Finset (Fin 7 → Fin 3)),
        Summable fun q => ‖smoothSliceFourierL2 (spatialCoordinateWordJet (fun y => velocity y σ) 7 word)
            (spatialCoordinateWordJet_contDiff _ hu 7 word)
            (spatialCoordinateWordJet_isOnePeriodic _ hper 7 word) c q‖ ^ 2 :=
      fun c _ word _ => (hasSum_sq_smoothSliceFourierL2 _ _ _ c).summable
    rw [hsplit, Summable.tsum_finsetSum (fun c hc => summable_sum (hsumm c hc))]
    calc ∑ c : Fin 3, ∑' q, ∑ word : Fin 7 → Fin 3, ‖smoothSliceFourierL2 _ _ _ c q‖ ^ 2
        = ∑ c : Fin 3, ∑ word : Fin 7 → Fin 3, ∑' q, ‖smoothSliceFourierL2 _ _ _ c q‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro c hc
          exact Summable.tsum_finsetSum (hsumm c hc)
      _ ≤ ∑ c : Fin 3, ∑ _word : Fin 7 → Fin 3, M ^ 2 * volume.real unitCube := by
          gcongr with c _ word _
          exact hjet word c
      _ = 3 * (3 ^ 7 * (M ^ 2 * volume.real unitCube)) := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
          norm_num
  calc moment (velocity := velocity) 11 σ ≤ _ := h1
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 (by positivity)

/-! ## The closure: the official problem from the defect bound alone -/

include solution in
/-- **The eleventh moment is bounded on every compact time interval.** -/
theorem exists_compact_bound {s τ : ℝ} (hs : 0 < s) (hτ : τ < T) :
    ∃ B : ℝ, ∀ σ ∈ Icc s τ, moment (velocity := velocity) 11 σ ≤ B := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_iteratedFDeriv solution 7 hs hτ
  refine ⟨(2 * Real.pi) ^ 2 / (2 * Real.pi) ^ 14 *
    (3 * (3 ^ 7 * (M ^ 2 * volume.real unitCube))), fun σ hσ => ?_⟩
  exact moment_eleven_le_of_bound solution ⟨by linarith [hσ.1], by linarith [hσ.2]⟩ hM0
    (hM σ hσ)

/-- **Coherence-defect control, defect only.**  Along a terminal tail `[s, T)` every nonzero
receiver has coherence defect at most `κ`. -/
def CoherenceDefectOnly : Prop :=
  ∀ {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField},
    0 < nu →
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure) →
      ∃ (s κ : ℝ), 0 < s ∧ s < T ∧ 0 ≤ κ ∧
        ∀ σ (hσ : σ ∈ Ioo 0 T), s ≤ σ →
          ∀ k : SpatialFrequency, k ≠ 0 → CoherenceDefectAt solution ⟨σ, hσ⟩ κ k

theorem coherenceDefectTailControl'_of_only (h : CoherenceDefectOnly) :
    CoherenceDefectTailControl' := by
  intro T nu initial velocity pressure hnu solution
  obtain ⟨s, κ, hs0, hsT, hκ, hdef⟩ := h hnu solution
  exact ⟨s, κ, hs0, hsT, hκ, hdef, fun τ hτ => exists_compact_bound solution hs0 hτ.2⟩

/-- **The official Navier–Stokes problem follows from the coherence-defect bound along a
terminal tail.** -/
theorem officialProblem_of_coherenceDefectOnly (h : CoherenceDefectOnly) :
    TheOfficialNavierStokesProblem :=
  officialProblem_of_defect (coherenceDefectTailControl'_of_only h)

end Soma.Holonics.Millennium.NavierStokesEleventhMomentCompactBound
