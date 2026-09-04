import ElementaryHolonics.Millennium.NavierStokesSixthYoung
import ElementaryHolonics.Millennium.NavierStokesFourthMomentRiccati

/-!
# The fourth-moment Riccati with the Young drive

The modal equation's source is the curl of the advection.  Summing the modal Riccati with weights
`|k|_∞⁴` over a finite family of nonzero modes, Cauchy--Schwarz on the cross term, and the
weight-six Young on the advection give

```text
M₄' ≤ −2 ν (2π)² M₆ + 2 √(3 M₄) · √( 3³ (2π)² · 3 · [ 2⁵ (3/(2π)²) 52 W₄² + 2⁵ (Σ' ℓ¹(û))² W₆ ] ).
```

The interpolation `W₄² ≤ W₂ W₆` and the velocity mass `Σ' ℓ¹(û) ≤ ℓ¹(û(0)) + √(52·3/(2π)²) √W₂`
put the whole drive under `K(t) · W₆` with

```text
K(t) = 3⁵ · 2⁵ · [ (2π)² (ℓ¹(û(0)) + √(52·3/(2π)²) √W₂)² + 3 · 52 · W₂ ],
```

and one arithmetic-geometric step returns the closure form

```text
M₄' ≤ −2 ν (2π)² M₆(F) + ν (2π)² W₆ + (3 K(t) / (ν (2π)²)) · M₄(F).
```

Every constant is a product expansion: `3⁵` the five coordinate comparisons, `2⁵` the doublings of
the cube weight, `52 = 2 · 26` the lattice weight, `(2π)²` the circle constraint squared.  The
dissipation acts at weight six; the drive is weight six times `K(t)`, which carries only the
second moment and the zero mode.  Nothing above the sixth moment enters.
-/

noncomputable section

open Set Filter Topology MeasureTheory
open scoped Finset

namespace Soma.Holonics.Millennium.NavierStokesYoungRiccati

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPeriodicEnergy
open Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCancellation
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionRemainderBound
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionFullStrain
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionFiniteBandBridge
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionPhysicalBridge
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionBaseEnergy
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionSourceModulus
open Soma.Holonics.Millennium.NavierStokesCoordinateJacobianFourierReconstruction
open Soma.Holonics.Millennium.NavierStokesH2StorageDissipationPayment
open Soma.Holonics.Millennium.NavierStokesAlignedStrainBudget
open Soma.Holonics.Millennium.NavierStokesOpenFourierMildIdentity
open Soma.Holonics.Millennium.NavierStokesOpenAdvectionCarrierIntegration
open Soma.Holonics.Millennium.NavierStokesOpenAdvectionConvolutionBridge
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesShellStepCost
open Soma.Holonics.Millennium.NavierStokesModalRiccati
open Soma.Holonics.Millennium.NavierStokesHalfRadiusReach
open Soma.Holonics.Millennium.NavierStokesWeightedTailEnergy
open Soma.Holonics.Millennium.NavierStokesIncoherentBandMass
open Soma.Holonics.Millennium.NavierStokesMomentSwap
open Soma.Holonics.Millennium.NavierStokesMomentGap
open Soma.Holonics.Millennium.NavierStokesFourthMomentRiccati
open Soma.Holonics.Millennium.NavierStokesWeightedYoung
open Soma.Holonics.Millennium.NavierStokesMomentInterpolation
open Soma.Holonics.Millennium.NavierStokesSixthYoung
open Soma.Holonics.Millennium.NavierStokesModalGronwall
open Soma.Holonics.Millennium.NavierStokesH2VorticityShellDissipationBridge

variable {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
  {pressure : PressureField}
  (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
  (t : Ioo 0 T)

/-! ## The velocity mass in moments -/

/-- The complete velocity `ℓ¹` mass is paid by the zero mode and the second moment. -/
theorem tsum_l1Pop_le (hsum : Summable (eleventhMoment (velocity := velocity) t.1)) :
    ∑' p, l1Pop solution t p ≤
      l1Pop solution t 0 + Real.sqrt (52 * (3 / (2 * Real.pi) ^ 2)) *
        Real.sqrt (moment (velocity := velocity) 2 t.1) := by
  refine Real.tsum_le_of_sum_le (fun p ↦ l1Pop_nonneg solution t p) ?_
  intro G
  have hsplit : ∑ p ∈ G, l1Pop solution t p ≤ l1Pop solution t 0 + ∑ p ∈ G.erase 0, l1Pop solution t p := by
    by_cases h : (0 : SpatialFrequency) ∈ G
    · rw [← Finset.add_sum_erase G _ h]
    · rw [Finset.erase_eq_of_notMem h]
      linarith [l1Pop_nonneg solution t 0]
  refine hsplit.trans (add_le_add le_rfl ?_)
  have hG1 : ∀ p ∈ G.erase 0, 1 ≤ frequencySup p :=
    fun p hp ↦ one_le_frequencySup_of_ne_zero (Finset.ne_of_mem_erase hp)
  refine (sum_l1_le solution t (G.erase 0) hG1).trans ?_
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  apply Real.sqrt_le_sqrt
  exact (summable_momentPop (w := 2) (by norm_num) (by norm_num) t.1 hsum).sum_le_tsum _
    (fun p _ ↦ momentPop_nonneg 2 t.1 p)

/-! ## The raw modal Riccati and the source in the sixth moment -/

theorem frequencySquared_le_three_sup_sq (k : SpatialFrequency) :
    frequencySquared k ≤ 3 * ((frequencySup k : ℕ) : ℝ) ^ 2 := by
  unfold frequencySquared
  have hc : ∀ c : Fin 3, (k c : ℝ) ^ 2 ≤ ((frequencySup k : ℕ) : ℝ) ^ 2 := by
    intro c
    have h1 : (k c).natAbs ≤ frequencySup k :=
      Finset.le_sup (f := fun c ↦ (k c).natAbs) (Finset.mem_univ c)
    have h2 : ((k c).natAbs : ℝ) ≤ ((frequencySup k : ℕ) : ℝ) := by exact_mod_cast h1
    have h3 : (k c : ℝ) ^ 2 = ((k c).natAbs : ℝ) ^ 2 := by
      rw [Nat.cast_natAbs, Int.cast_abs, sq_abs]
    rw [h3]
    exact pow_le_pow_left₀ (by positivity) h2 2
  rw [Fin.sum_univ_three]
  linarith [hc 0, hc 1, hc 2]

/-- The raw modal Riccati: the cross term is the amplitude times the source's `ℓ¹` norm. -/
theorem modalEnergy_riccati_raw {k : SpatialFrequency} (hk : 1 ≤ frequencySup k) :
    ∃ D : ℝ, HasDerivAt (modalEnergy (velocity := velocity) k) D t.1 ∧
      D ≤ -2 * nu * torusStokesEigenvalue k * modalEnergy (velocity := velocity) k t.1 +
        2 * complexVectorL1 (vorticityModeCurve (velocity := velocity) k t.1) *
          complexVectorL1 (vorticityNonlinearMode solution t k) := by
  have hpos : 0 < torusStokesEigenvalue k := by
    apply torusStokesEigenvalue_pos_of_not_mem (radius := 0)
    rw [mem_frequencyCube_iff_frequencySup_le]
    omega
  have hsq : 0 < Real.sqrt (torusStokesEigenvalue k) := Real.sqrt_pos.mpr hpos
  set B := complexVectorL1 (vorticityNonlinearMode solution t k) / (3 ^ 2 * Real.sqrt (torusStokesEigenvalue k))
    with hB
  have hBeq : 3 ^ 2 * Real.sqrt (torusStokesEigenvalue k) * B =
      complexVectorL1 (vorticityNonlinearMode solution t k) := by
    rw [hB]
    field_simp
  obtain ⟨D, hD, hle⟩ := modalEnergy_riccati_of solution t k (le_of_eq hBeq.symm)
  refine ⟨D, hD, ?_⟩
  rw [hBeq] at hle
  exact hle

/-- The weighted source squared is paid by the sixth moment of the advection. -/
theorem sup_pow_four_l1_nonlinear_sq_le (k : SpatialFrequency) :
    ((frequencySup k : ℕ) : ℝ) ^ 4 * complexVectorL1 (vorticityNonlinearMode solution t k) ^ 2 ≤
      3 ^ 3 * (2 * Real.pi) ^ 2 * ((frequencySup k : ℕ) : ℝ) ^ 6 *
        ∑ output : Fin 3, ‖openActualAdvectionMode solution t k output‖ ^ 2 := by
  unfold vorticityNonlinearMode
  have hneg : complexVectorL1 (-frequencyCurlMultiplier k (openAdvectionMode solution t k)) =
      complexVectorL1 (frequencyCurlMultiplier k (openAdvectionMode solution t k)) := by
    simp [complexVectorL1]
  rw [hneg]
  have hcurl := complexVectorL1_frequencyCurlMultiplier_sq_le k (openAdvectionMode solution t k)
  have hlam : torusStokesEigenvalue k ≤ (2 * Real.pi) ^ 2 * (3 * ((frequencySup k : ℕ) : ℝ) ^ 2) := by
    unfold torusStokesEigenvalue
    exact mul_le_mul_of_nonneg_left (frequencySquared_le_three_sup_sq k) (by positivity)
  rw [openAdvectionMode_eq_openActualAdvectionMode] at hcurl ⊢
  have hS : 0 ≤ ∑ component : Fin 3, ‖openActualAdvectionMode solution t k component‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hw : (0 : ℝ) ≤ ((frequencySup k : ℕ) : ℝ) ^ 4 := by positivity
  calc ((frequencySup k : ℕ) : ℝ) ^ 4 * complexVectorL1 (frequencyCurlMultiplier k (openActualAdvectionMode solution t k)) ^ 2
      ≤ ((frequencySup k : ℕ) : ℝ) ^ 4 * (9 * torusStokesEigenvalue k *
          ∑ component : Fin 3, ‖openActualAdvectionMode solution t k component‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hcurl hw
    _ ≤ ((frequencySup k : ℕ) : ℝ) ^ 4 * (9 * ((2 * Real.pi) ^ 2 * (3 * ((frequencySup k : ℕ) : ℝ) ^ 2)) *
          ∑ component : Fin 3, ‖openActualAdvectionMode solution t k component‖ ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ hw
        apply mul_le_mul_of_nonneg_right _ hS
        exact mul_le_mul_of_nonneg_left hlam (by norm_num)
    _ = 3 ^ 3 * (2 * Real.pi) ^ 2 * ((frequencySup k : ℕ) : ℝ) ^ 6 *
          ∑ output : Fin 3, ‖openActualAdvectionMode solution t k output‖ ^ 2 := by ring

/-- The complete source population of a finite family, in moments. -/
def sourceBound (τ : ℝ) : ℝ :=
  3 ^ 3 * (2 * Real.pi) ^ 2 * 3 *
    (2 ^ 5 * (3 / (2 * Real.pi) ^ 2) * 52 * moment (velocity := velocity) 4 τ ^ 2 +
      2 ^ 5 * (∑' p, l1Pop solution t p) ^ 2 * moment (velocity := velocity) 6 τ)

theorem sum_sup_pow_four_l1_nonlinear_sq_le (F : Finset SpatialFrequency)
    (hsum : Summable (eleventhMoment (velocity := velocity) t.1)) :
    ∑ k ∈ F, ((frequencySup k : ℕ) : ℝ) ^ 4 * complexVectorL1 (vorticityNonlinearMode solution t k) ^ 2 ≤
      sourceBound (velocity := velocity) solution t t.1 := by
  refine (Finset.sum_le_sum fun k _ ↦ sup_pow_four_l1_nonlinear_sq_le solution t k).trans ?_
  unfold sourceBound
  have hswap : ∑ k ∈ F, 3 ^ 3 * (2 * Real.pi) ^ 2 * ((frequencySup k : ℕ) : ℝ) ^ 6 *
      ∑ output : Fin 3, ‖openActualAdvectionMode solution t k output‖ ^ 2 =
      3 ^ 3 * (2 * Real.pi) ^ 2 * ∑ output : Fin 3,
        ∑ k ∈ F, ((frequencySup k : ℕ) : ℝ) ^ 6 * ‖openActualAdvectionMode solution t k output‖ ^ 2 := by
    rw [Finset.sum_comm, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro output _
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ ↦ by ring
  rw [hswap]
  have hout : ∀ output ∈ (Finset.univ : Finset (Fin 3)),
      ∑ k ∈ F, ((frequencySup k : ℕ) : ℝ) ^ 6 * ‖openActualAdvectionMode solution t k output‖ ^ 2 ≤
        2 ^ 5 * (3 / (2 * Real.pi) ^ 2) * 52 * moment (velocity := velocity) 4 t.1 ^ 2 +
          2 ^ 5 * (∑' p, l1Pop solution t p) ^ 2 * moment (velocity := velocity) 6 t.1 :=
    fun output _ ↦ sum_pow_six_norm_adv_sq_le solution t F output hsum
  have := Finset.sum_le_sum hout
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
  have hpos : (0 : ℝ) ≤ 3 ^ 3 * (2 * Real.pi) ^ 2 := by positivity
  calc 3 ^ 3 * (2 * Real.pi) ^ 2 * ∑ output : Fin 3,
        ∑ k ∈ F, ((frequencySup k : ℕ) : ℝ) ^ 6 * ‖openActualAdvectionMode solution t k output‖ ^ 2
      ≤ 3 ^ 3 * (2 * Real.pi) ^ 2 * ((3 : ℕ) * (2 ^ 5 * (3 / (2 * Real.pi) ^ 2) * 52 *
          moment (velocity := velocity) 4 t.1 ^ 2 +
          2 ^ 5 * (∑' p, l1Pop solution t p) ^ 2 * moment (velocity := velocity) 6 t.1)) :=
        mul_le_mul_of_nonneg_left this hpos
    _ = _ := by push_cast; ring

/-! ## The family Riccati with the Young drive -/

/-- **The fourth-moment Riccati with the Young drive.** -/
theorem momentEnergy_riccati_young (hnu : 0 < nu) {F : Finset SpatialFrequency}
    (hF : ∀ k ∈ F, 1 ≤ frequencySup k)
    (hsum : Summable (eleventhMoment (velocity := velocity) t.1)) :
    ∃ D : ℝ, HasDerivAt (momentEnergy (velocity := velocity) 4 F) D t.1 ∧
      D ≤ -2 * nu * (2 * Real.pi) ^ 2 * momentEnergy (velocity := velocity) 6 F t.1 +
        2 * Real.sqrt (3 * momentEnergy (velocity := velocity) 4 F t.1) *
          Real.sqrt (sourceBound (velocity := velocity) solution t t.1) := by
  have hmode : ∀ k ∈ F, ∃ D : ℝ,
      HasDerivAt (modalEnergy (velocity := velocity) k) D t.1 ∧
        D ≤ -2 * nu * torusStokesEigenvalue k * modalEnergy (velocity := velocity) k t.1 +
          2 * complexVectorL1 (vorticityModeCurve (velocity := velocity) k t.1) *
            complexVectorL1 (vorticityNonlinearMode solution t k) :=
    fun k hk ↦ modalEnergy_riccati_raw solution t (hF k hk)
  choose! D hD using hmode
  refine ⟨∑ k ∈ F, ((frequencySup k : ℕ) : ℝ) ^ 4 * D k, ?_, ?_⟩
  · unfold momentEnergy
    have hfun : (fun τ ↦ ∑ k ∈ F,
        ((frequencySup k : ℕ) : ℝ) ^ 4 * modalEnergy (velocity := velocity) k τ) =
        ∑ k ∈ F, fun τ ↦ ((frequencySup k : ℕ) : ℝ) ^ 4 *
          modalEnergy (velocity := velocity) k τ := by
      funext τ
      simp [Finset.sum_apply]
    rw [hfun]
    exact HasDerivAt.sum fun k hk ↦ (hD k hk).1.const_mul _
  · -- split into dissipation and cross term
    have hterm : ∀ k ∈ F, ((frequencySup k : ℕ) : ℝ) ^ 4 * D k ≤
        -2 * nu * (2 * Real.pi) ^ 2 * (((frequencySup k : ℕ) : ℝ) ^ 6 * modalEnergy (velocity := velocity) k t.1) +
          2 * (((frequencySup k : ℕ) : ℝ) ^ 2 * complexVectorL1 (vorticityModeCurve (velocity := velocity) k t.1)) *
            (((frequencySup k : ℕ) : ℝ) ^ 2 * complexVectorL1 (vorticityNonlinearMode solution t k)) := by
      intro k hk
      have hw : (0 : ℝ) ≤ ((frequencySup k : ℕ) : ℝ) ^ 4 := by positivity
      have h1 := mul_le_mul_of_nonneg_left (hD k hk).2 hw
      have hlam : (2 * Real.pi) ^ 2 * ((frequencySup k : ℕ) : ℝ) ^ 2 ≤ torusStokesEigenvalue k :=
        torusStokesEigenvalue_ge k
      have hE := modalEnergy_nonneg (velocity := velocity) k t.1
      have h2 : ((frequencySup k : ℕ) : ℝ) ^ 4 * (-2 * nu * torusStokesEigenvalue k *
          modalEnergy (velocity := velocity) k t.1) ≤
          -2 * nu * (2 * Real.pi) ^ 2 * (((frequencySup k : ℕ) : ℝ) ^ 6 * modalEnergy (velocity := velocity) k t.1) := by
        have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlam hnu.le) (mul_nonneg hw hE)
        nlinarith [this]
      nlinarith [h1, h2]
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_add_distrib]
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq F
      (fun k ↦ ((frequencySup k : ℕ) : ℝ) ^ 2 * complexVectorL1 (vorticityModeCurve (velocity := velocity) k t.1))
      (fun k ↦ ((frequencySup k : ℕ) : ℝ) ^ 2 * complexVectorL1 (vorticityNonlinearMode solution t k))
    have hleft : ∑ k ∈ F, (((frequencySup k : ℕ) : ℝ) ^ 2 *
        complexVectorL1 (vorticityModeCurve (velocity := velocity) k t.1)) ^ 2 ≤
        3 * momentEnergy (velocity := velocity) 4 F t.1 := by
      unfold momentEnergy
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro k _
      have := complexVectorL1_sq_le_three_mul_modalEnergy (velocity := velocity) k t.1
      have hw : (0 : ℝ) ≤ ((frequencySup k : ℕ) : ℝ) ^ 4 := by positivity
      calc (((frequencySup k : ℕ) : ℝ) ^ 2 * complexVectorL1 (vorticityModeCurve (velocity := velocity) k t.1)) ^ 2
          = ((frequencySup k : ℕ) : ℝ) ^ 4 * complexVectorL1 (vorticityModeCurve (velocity := velocity) k t.1) ^ 2 := by ring
        _ ≤ ((frequencySup k : ℕ) : ℝ) ^ 4 * (3 * modalEnergy (velocity := velocity) k t.1) :=
            mul_le_mul_of_nonneg_left this hw
        _ = 3 * (((frequencySup k : ℕ) : ℝ) ^ 4 * modalEnergy (velocity := velocity) k t.1) := by ring
    have hright : ∑ k ∈ F, (((frequencySup k : ℕ) : ℝ) ^ 2 *
        complexVectorL1 (vorticityNonlinearMode solution t k)) ^ 2 ≤
        sourceBound (velocity := velocity) solution t t.1 := by
      refine le_trans (le_of_eq ?_) (sum_sup_pow_four_l1_nonlinear_sq_le solution t F hsum)
      apply Finset.sum_congr rfl
      intro k _
      ring
    have hcross : ∑ k ∈ F, 2 * (((frequencySup k : ℕ) : ℝ) ^ 2 *
        complexVectorL1 (vorticityModeCurve (velocity := velocity) k t.1)) *
          (((frequencySup k : ℕ) : ℝ) ^ 2 * complexVectorL1 (vorticityNonlinearMode solution t k)) ≤
        2 * Real.sqrt (3 * momentEnergy (velocity := velocity) 4 F t.1) *
          Real.sqrt (sourceBound (velocity := velocity) solution t t.1) := by
      have hsum0 : 0 ≤ ∑ k ∈ F, (((frequencySup k : ℕ) : ℝ) ^ 2 *
          complexVectorL1 (vorticityModeCurve (velocity := velocity) k t.1)) *
            (((frequencySup k : ℕ) : ℝ) ^ 2 * complexVectorL1 (vorticityNonlinearMode solution t k)) :=
        Finset.sum_nonneg fun k _ ↦ mul_nonneg (mul_nonneg (by positivity) (complexVectorL1_nonneg _))
          (mul_nonneg (by positivity) (complexVectorL1_nonneg _))
      have hM0 : 0 ≤ 3 * momentEnergy (velocity := velocity) 4 F t.1 := by
        unfold momentEnergy
        exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun k _ ↦
          mul_nonneg (by positivity) (modalEnergy_nonneg k t.1))
      have hS0 : 0 ≤ sourceBound (velocity := velocity) solution t t.1 := by
        unfold sourceBound
        have h4 := moment_nonneg (velocity := velocity) 4 t.1
        have h6 := moment_nonneg (velocity := velocity) 6 t.1
        positivity
      have hsq : (∑ k ∈ F, (((frequencySup k : ℕ) : ℝ) ^ 2 *
          complexVectorL1 (vorticityModeCurve (velocity := velocity) k t.1)) *
            (((frequencySup k : ℕ) : ℝ) ^ 2 * complexVectorL1 (vorticityNonlinearMode solution t k))) ^ 2 ≤
          (3 * momentEnergy (velocity := velocity) 4 F t.1) * sourceBound (velocity := velocity) solution t t.1 :=
        hcs.trans (mul_le_mul hleft hright (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _) hM0)
      have hle := Real.sqrt_le_sqrt hsq
      rw [Real.sqrt_sq hsum0, Real.sqrt_mul hM0] at hle
      calc ∑ k ∈ F, 2 * (((frequencySup k : ℕ) : ℝ) ^ 2 *
            complexVectorL1 (vorticityModeCurve (velocity := velocity) k t.1)) *
              (((frequencySup k : ℕ) : ℝ) ^ 2 * complexVectorL1 (vorticityNonlinearMode solution t k))
          = 2 * ∑ k ∈ F, (((frequencySup k : ℕ) : ℝ) ^ 2 *
              complexVectorL1 (vorticityModeCurve (velocity := velocity) k t.1)) *
                (((frequencySup k : ℕ) : ℝ) ^ 2 * complexVectorL1 (vorticityNonlinearMode solution t k)) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k _
            ring
        _ ≤ 2 * (Real.sqrt (3 * momentEnergy (velocity := velocity) 4 F t.1) *
              Real.sqrt (sourceBound (velocity := velocity) solution t t.1)) :=
            mul_le_mul_of_nonneg_left hle (by norm_num)
        _ = _ := by ring
    have hdiss : ∑ k ∈ F, -2 * nu * (2 * Real.pi) ^ 2 *
        (((frequencySup k : ℕ) : ℝ) ^ 6 * modalEnergy (velocity := velocity) k t.1) =
        -2 * nu * (2 * Real.pi) ^ 2 * momentEnergy (velocity := velocity) 6 F t.1 := by
      unfold momentEnergy
      rw [Finset.mul_sum]
    rw [hdiss]
    linarith [hcross]

section Audit

#print axioms tsum_l1Pop_le
#print axioms modalEnergy_riccati_raw
#print axioms sum_sup_pow_four_l1_nonlinear_sq_le
#print axioms momentEnergy_riccati_young

end Audit

end Soma.Holonics.Millennium.NavierStokesYoungRiccati
