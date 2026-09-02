import ElementaryHolonics.Millennium.NavierStokesIncoherentSource

/-!
# The incoherent closure: Statement B on incoherent feeds with bounded velocity mass

On incoherent receivers the weight-two Riccati closes with a linear drive whose coefficient carries
only the velocity mass `V` and the viscosity:

```text
M₂(F)' ≤ −2 ν (2π)² M₄(F) + (3/2) ν (2π)² W₄ + (3 c V / (ν (2π)²)) M₂(F) + (18 c V / (ν (2π)²)) W₂,
c = 3³ (2π)² · 3 · 2³,
```

by the two interpolations `W₂² ≤ W₀ W₄` and `W₀² ≤ 3 (2π)² V W₂`.  On the cube families the drive at
weight four is absorbed by the dissipation, the forcing is `W₁₁/(N+1)⁷`, and `N → ∞` returns on every
`[s, τ] ⊂ (0, T)`

```text
W₂(τ) ≤ W₂(s) · exp( 21 c V₀ (τ − s) / (ν (2π)²) ).
```

Then the closure drive is bounded along the terminal tail, `ClosureDriveControl` holds, and
`StatementB` follows.  The premises: incoherence at every nonzero receiver, velocity mass at most
`V₀`, and interior finiteness of the eleventh moment.
-/

noncomputable section

open Set Filter Topology MeasureTheory
open scoped Finset

namespace Soma.Holonics.Millennium.NavierStokesIncoherentClosure

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
open Soma.Holonics.Millennium.NavierStokesModalRiccati
open Soma.Holonics.Millennium.NavierStokesHalfRadiusReach
open Soma.Holonics.Millennium.NavierStokesShellStepCost
open Soma.Holonics.Millennium.NavierStokesMomentSwap
open Soma.Holonics.Millennium.NavierStokesMomentGap
open Soma.Holonics.Millennium.NavierStokesYoungFeed
open Soma.Holonics.Millennium.NavierStokesYoungTsum
open Soma.Holonics.Millennium.NavierStokesWeightedTailEnergy
open Soma.Holonics.Millennium.NavierStokesIncoherentBandMass
open Soma.Holonics.Millennium.NavierStokesOpenAdvectionCarrierIntegration
open Soma.Holonics.Millennium.NavierStokesOpenAdvectionConvolutionBridge
open Soma.Holonics.Millennium.NavierStokesFourthMomentRiccati
open Soma.Holonics.Millennium.NavierStokesWeightedYoung
open Soma.Holonics.Millennium.NavierStokesMomentInterpolation
open Soma.Holonics.Millennium.NavierStokesSixthYoung
open Soma.Holonics.Millennium.NavierStokesYoungRiccati
open Soma.Holonics.Millennium.NavierStokesOpenFourierModeEvolution
open Soma.Holonics.Millennium.NavierStokesModeLagrange
open Soma.Holonics.Millennium.NavierStokesTailRelevance
open Soma.Holonics.Millennium.NavierStokesTailBoundedControl
open Soma.Holonics.Millennium.NavierStokesDyadicVorticityFluxConvolutionBridge
open Soma.Holonics.Millennium.NavierStokesOpenFourierMildIdentity
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesModalGronwall
open Soma.Holonics.Millennium.NavierStokesTailGronwall
open Soma.Holonics.Millennium.NavierStokesFrequencyReach
open Soma.Holonics.Millennium.NavierStokesH2VorticityShellDissipationBridge
open Soma.Holonics.Millennium.NavierStokesYoungClosure
open Soma.Holonics.Millennium.NavierStokesMomentClosure
open Soma.Holonics.Millennium.NavierStokesIncoherentSource

variable {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
  {pressure : PressureField}
  (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
  (t : Ioo 0 T)

/-! ## Interpolation -/

theorem momentPop_add_two_eq_sqrt_mul (w : ℕ) (τ : ℝ) (q : SpatialFrequency) :
    momentPop (velocity := velocity) (w + 2) τ q =
      Real.sqrt (momentPop (velocity := velocity) w τ q) *
        Real.sqrt (momentPop (velocity := velocity) (w + 4) τ q) := by
  rw [← Real.sqrt_mul (momentPop_nonneg _ _ _)]
  have h : momentPop (velocity := velocity) w τ q * momentPop (velocity := velocity) (w + 4) τ q =
      momentPop (velocity := velocity) (w + 2) τ q ^ 2 := by
    unfold momentPop; ring
  rw [h, Real.sqrt_sq (momentPop_nonneg _ _ _)]

/-- **Interpolation with step two.** -/
theorem moment_add_two_sq_le (w : ℕ) (τ : ℝ)
    (h0 : Summable (momentPop (velocity := velocity) w τ))
    (h4 : Summable (momentPop (velocity := velocity) (w + 4) τ)) :
    moment (velocity := velocity) (w + 2) τ ^ 2 ≤
      moment (velocity := velocity) w τ * moment (velocity := velocity) (w + 4) τ := by
  have hP : 0 ≤ moment (velocity := velocity) w τ * moment (velocity := velocity) (w + 4) τ :=
    mul_nonneg (moment_nonneg _ _) (moment_nonneg _ _)
  have hle : moment (velocity := velocity) (w + 2) τ ≤
      Real.sqrt (moment (velocity := velocity) w τ * moment (velocity := velocity) (w + 4) τ) := by
    refine Real.tsum_le_of_sum_le (momentPop_nonneg _ _) fun F ↦ ?_
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq F
      (fun q ↦ Real.sqrt (momentPop (velocity := velocity) w τ q))
      (fun q ↦ Real.sqrt (momentPop (velocity := velocity) (w + 4) τ q))
    have hsq : ∀ q, Real.sqrt (momentPop (velocity := velocity) w τ q) ^ 2 =
        momentPop (velocity := velocity) w τ q := fun q ↦ Real.sq_sqrt (momentPop_nonneg _ _ _)
    have hsq4 : ∀ q, Real.sqrt (momentPop (velocity := velocity) (w + 4) τ q) ^ 2 =
        momentPop (velocity := velocity) (w + 4) τ q := fun q ↦ Real.sq_sqrt (momentPop_nonneg _ _ _)
    simp only [hsq, hsq4] at hcs
    have h1 : ∑ q ∈ F, momentPop (velocity := velocity) w τ q ≤ moment (velocity := velocity) w τ :=
      h0.sum_le_tsum F fun q _ ↦ momentPop_nonneg _ _ _
    have h2 : ∑ q ∈ F, momentPop (velocity := velocity) (w + 4) τ q ≤
        moment (velocity := velocity) (w + 4) τ :=
      h4.sum_le_tsum F fun q _ ↦ momentPop_nonneg _ _ _
    rw [Finset.sum_congr rfl fun q _ ↦ momentPop_add_two_eq_sqrt_mul (velocity := velocity) w τ q]
    apply Real.le_sqrt_of_sq_le
    exact hcs.trans (mul_le_mul h1 h2 (Finset.sum_nonneg fun q _ ↦ momentPop_nonneg _ _ _)
      (moment_nonneg _ _))
  calc moment (velocity := velocity) (w + 2) τ ^ 2
      ≤ Real.sqrt (moment (velocity := velocity) w τ * moment (velocity := velocity) (w + 4) τ) ^ 2 :=
        pow_le_pow_left₀ (moment_nonneg _ _) hle 2
    _ = _ := Real.sq_sqrt hP

include solution in
theorem moment_two_sq_le (hsum : Summable (eleventhMoment (velocity := velocity) t.1)) :
    moment (velocity := velocity) 2 t.1 ^ 2 ≤
      moment (velocity := velocity) 0 t.1 * moment (velocity := velocity) 4 t.1 := by
  have := moment_add_two_sq_le (velocity := velocity) 0 t.1 (summable_momentPop_zero solution t hsum)
    (summable_momentPop (w := 4) (by norm_num) (by norm_num) t.1 hsum)
  simpa using this

/-- **The enstrophy squared is paid by the velocity mass and the second moment.** -/
theorem moment_zero_sq_le (hsum : Summable (eleventhMoment (velocity := velocity) t.1)) :
    moment (velocity := velocity) 0 t.1 ^ 2 ≤
      3 * (2 * Real.pi) ^ 2 * velocityMass solution t * moment (velocity := velocity) 2 t.1 := by
  have hV := velocityMass_nonneg solution t
  have hW2 := moment_nonneg (velocity := velocity) 2 t.1
  have hP : 0 ≤ 3 * (2 * Real.pi) ^ 2 * velocityMass solution t * moment (velocity := velocity) 2 t.1 := by
    positivity
  have hle : moment (velocity := velocity) 0 t.1 ≤
      Real.sqrt (3 * (2 * Real.pi) ^ 2 * velocityMass solution t * moment (velocity := velocity) 2 t.1) := by
    refine Real.tsum_le_of_sum_le (momentPop_nonneg _ _) fun F ↦ ?_
    have hab : ∀ q, momentPop (velocity := velocity) 0 t.1 q =
        Real.sqrt (velPop solution t q) *
          (Real.sqrt (velPop solution t q) * ((2 * Real.pi) ^ 2 * frequencySquared q)) := by
      intro q
      rw [momentPop_zero_weight, modalEnergy_eq_velPop solution t q, ← mul_assoc,
        Real.mul_self_sqrt (velPop_nonneg _ _ _)]
      ring
    have hb : ∀ q, (Real.sqrt (velPop solution t q) * ((2 * Real.pi) ^ 2 * frequencySquared q)) ^ 2 ≤
        3 * (2 * Real.pi) ^ 2 * momentPop (velocity := velocity) 2 t.1 q := by
      intro q
      rw [mul_pow, Real.sq_sqrt (velPop_nonneg _ _ _)]
      unfold momentPop
      rw [modalEnergy_eq_velPop solution t q]
      have h3 := frequencySquared_le_three_sup_sq q
      have hv := velPop_nonneg solution t q
      have hfs : 0 ≤ frequencySquared q :=
        (sq_nonneg _).trans (frequencySup_sq_le_frequencySquared q)
      have hc : (0 : ℝ) ≤ (2 * Real.pi) ^ 4 * velPop solution t q * frequencySquared q :=
        mul_nonneg (mul_nonneg (by positivity) hv) hfs
      have key := mul_le_mul_of_nonneg_left h3 hc
      calc velPop solution t q * ((2 * Real.pi) ^ 2 * frequencySquared q) ^ 2
          = (2 * Real.pi) ^ 4 * velPop solution t q * frequencySquared q * frequencySquared q := by ring
        _ ≤ (2 * Real.pi) ^ 4 * velPop solution t q * frequencySquared q *
            (3 * ((frequencySup q : ℕ) : ℝ) ^ 2) := key
        _ = _ := by ring
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq F (fun q ↦ Real.sqrt (velPop solution t q))
      (fun q ↦ Real.sqrt (velPop solution t q) * ((2 * Real.pi) ^ 2 * frequencySquared q))
    have hsq : ∀ q, Real.sqrt (velPop solution t q) ^ 2 = velPop solution t q :=
      fun q ↦ Real.sq_sqrt (velPop_nonneg _ _ _)
    simp only [hsq] at hcs
    have hA : ∑ q ∈ F, velPop solution t q ≤ velocityMass solution t :=
      (summable_velPop solution t).sum_le_tsum F fun q _ ↦ velPop_nonneg _ _ _
    have hB : ∑ q ∈ F, (Real.sqrt (velPop solution t q) * ((2 * Real.pi) ^ 2 * frequencySquared q)) ^ 2 ≤
        3 * (2 * Real.pi) ^ 2 * moment (velocity := velocity) 2 t.1 := by
      calc ∑ q ∈ F, (Real.sqrt (velPop solution t q) * ((2 * Real.pi) ^ 2 * frequencySquared q)) ^ 2
          ≤ ∑ q ∈ F, 3 * (2 * Real.pi) ^ 2 * momentPop (velocity := velocity) 2 t.1 q :=
            Finset.sum_le_sum fun q _ ↦ hb q
        _ = 3 * (2 * Real.pi) ^ 2 * ∑ q ∈ F, momentPop (velocity := velocity) 2 t.1 q := by
            rw [Finset.mul_sum]
        _ ≤ _ := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact (summable_momentPop (w := 2) (by norm_num) (by norm_num) t.1 hsum).sum_le_tsum F
              fun q _ ↦ momentPop_nonneg _ _ _
    rw [Finset.sum_congr rfl fun q _ ↦ hab q]
    apply Real.le_sqrt_of_sq_le
    calc (∑ q ∈ F, Real.sqrt (velPop solution t q) *
          (Real.sqrt (velPop solution t q) * ((2 * Real.pi) ^ 2 * frequencySquared q))) ^ 2
        ≤ (∑ q ∈ F, velPop solution t q) *
          ∑ q ∈ F, (Real.sqrt (velPop solution t q) * ((2 * Real.pi) ^ 2 * frequencySquared q)) ^ 2 := hcs
      _ ≤ velocityMass solution t * (3 * (2 * Real.pi) ^ 2 * moment (velocity := velocity) 2 t.1) :=
          mul_le_mul hA hB (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _) hV
      _ = _ := by ring
  calc moment (velocity := velocity) 0 t.1 ^ 2
      ≤ Real.sqrt (3 * (2 * Real.pi) ^ 2 * velocityMass solution t *
          moment (velocity := velocity) 2 t.1) ^ 2 := pow_le_pow_left₀ (moment_nonneg _ _) hle 2
    _ = _ := Real.sq_sqrt hP

/-! ## Square roots -/

theorem sqrt_add_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  have hsx := Real.sq_sqrt hx
  have hsy := Real.sq_sqrt hy
  have h0x := Real.sqrt_nonneg x
  have h0y := Real.sqrt_nonneg y
  calc Real.sqrt (x + y) ≤ Real.sqrt ((Real.sqrt x + Real.sqrt y) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith [mul_nonneg h0x h0y])
    _ = Real.sqrt x + Real.sqrt y := Real.sqrt_sq (add_nonneg h0x h0y)

/-! ## The weight-two source and Riccati on incoherent receivers -/

/-- The incoherent constant `3³ (2π)² · 3 · 2³`. -/
def incoherentConstant : ℝ := 3 ^ 3 * (2 * Real.pi) ^ 2 * 3 * 2 ^ 3

theorem incoherentConstant_nonneg : 0 ≤ incoherentConstant := by
  unfold incoherentConstant; positivity

theorem sum_sup_sq_l1_nonlinear_sq_le_of_incoherent (F : Finset SpatialFrequency)
    (hsum : Summable (eleventhMoment (velocity := velocity) t.1))
    (hinc : ∀ k ∈ F, IncoherentAt solution t k) :
    ∑ k ∈ F, ((frequencySup k : ℕ) : ℝ) ^ 2 *
        complexVectorL1 (vorticityNonlinearMode solution t k) ^ 2 ≤
      incoherentConstant * (velocityMass solution t * moment (velocity := velocity) 4 t.1 +
        moment (velocity := velocity) 0 t.1 * moment (velocity := velocity) 2 t.1 /
          (2 * Real.pi) ^ 2) := by
  calc ∑ k ∈ F, ((frequencySup k : ℕ) : ℝ) ^ 2 *
        complexVectorL1 (vorticityNonlinearMode solution t k) ^ 2
      ≤ ∑ k ∈ F, 3 ^ 3 * (2 * Real.pi) ^ 2 * ((frequencySup k : ℕ) : ℝ) ^ (2 + 2) *
          ∑ output : Fin 3, ‖openActualAdvectionMode solution t k output‖ ^ 2 :=
        Finset.sum_le_sum fun k _ ↦ sup_pow_l1_nonlinear_sq_le solution t 2 k
    _ = 3 ^ 3 * (2 * Real.pi) ^ 2 * ∑ k ∈ F, ((frequencySup k : ℕ) : ℝ) ^ 4 *
          ∑ output : Fin 3, ‖openActualAdvectionMode solution t k output‖ ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ ↦ by ring
    _ ≤ 3 ^ 3 * (2 * Real.pi) ^ 2 * (3 * 2 ^ 3 *
          (velocityMass solution t * moment (velocity := velocity) 4 t.1 +
            moment (velocity := velocity) 0 t.1 * moment (velocity := velocity) 2 t.1 /
              (2 * Real.pi) ^ 2)) :=
        mul_le_mul_of_nonneg_left (sum_pow_four_adv_sq_le_of_incoherent solution t F hsum hinc)
          (by positivity)
    _ = _ := by unfold incoherentConstant; ring

/-- **The weight-two Riccati on incoherent receivers.** -/
theorem momentEnergy_riccati_incoherent (hnu : 0 < nu) {F : Finset SpatialFrequency}
    (hF : ∀ k ∈ F, 1 ≤ frequencySup k) (hsum : Summable (eleventhMoment (velocity := velocity) t.1))
    (hinc : ∀ k ∈ F, IncoherentAt solution t k) :
    ∃ D : ℝ, HasDerivAt (momentEnergy (velocity := velocity) 2 F) D t.1 ∧
      D ≤ -2 * nu * (2 * Real.pi) ^ 2 * momentEnergy (velocity := velocity) 4 F t.1 +
        3 / 2 * (nu * (2 * Real.pi) ^ 2) * moment (velocity := velocity) 4 t.1 +
        3 * incoherentConstant * velocityMass solution t / (nu * (2 * Real.pi) ^ 2) *
          momentEnergy (velocity := velocity) 2 F t.1 +
        18 * incoherentConstant * velocityMass solution t / (nu * (2 * Real.pi) ^ 2) *
          moment (velocity := velocity) 2 t.1 := by
  obtain ⟨D, hD, hle⟩ := momentEnergy_riccati_gen solution t 2 hnu hF
  simp only [Nat.reduceAdd] at hle
  refine ⟨D, hD, hle.trans ?_⟩
  have hSle := sum_sup_sq_l1_nonlinear_sq_le_of_incoherent solution t F hsum hinc
  have hM2W2 : momentEnergy (velocity := velocity) 2 F t.1 ≤ moment (velocity := velocity) 2 t.1 :=
    (summable_momentPop (w := 2) (by norm_num) (by norm_num) t.1 hsum).sum_le_tsum F
      fun q _ ↦ momentPop_nonneg _ _ _
  have hint1 := moment_two_sq_le solution t hsum
  have hint0 := moment_zero_sq_le solution t hsum
  set c : ℝ := incoherentConstant with hc
  set V : ℝ := velocityMass solution t with hV
  set M2 : ℝ := momentEnergy (velocity := velocity) 2 F t.1 with hM2
  set M4 : ℝ := momentEnergy (velocity := velocity) 4 F t.1 with hM4
  set W0 : ℝ := moment (velocity := velocity) 0 t.1 with hW0
  set W2 : ℝ := moment (velocity := velocity) 2 t.1 with hW2
  set W4 : ℝ := moment (velocity := velocity) 4 t.1 with hW4
  set S : ℝ := ∑ k ∈ F, ((frequencySup k : ℕ) : ℝ) ^ 2 *
    complexVectorL1 (vorticityNonlinearMode solution t k) ^ 2 with hS
  have hPpos : 0 < nu * (2 * Real.pi) ^ 2 := by positivity
  have hc0 : 0 ≤ c := incoherentConstant_nonneg
  have hV0 : 0 ≤ V := velocityMass_nonneg solution t
  have hM20 : 0 ≤ M2 := momentEnergy_nonneg 2 F t.1
  have hM40 : 0 ≤ M4 := momentEnergy_nonneg 4 F t.1
  have hW00 : 0 ≤ W0 := moment_nonneg _ _
  have hW20 : 0 ≤ W2 := moment_nonneg _ _
  have hW40 : 0 ≤ W4 := moment_nonneg _ _
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun k _ ↦ mul_nonneg (by positivity) (sq_nonneg _)
  have hSle' : S ≤ c * V * W4 + c * W0 * W2 / (2 * Real.pi) ^ 2 := by
    calc S ≤ c * (V * W4 + W0 * W2 / (2 * Real.pi) ^ 2) := hSle
      _ = _ := by ring
  have hS1 : 0 ≤ c * V * W4 := by positivity
  have hS2 : 0 ≤ c * W0 * W2 / (2 * Real.pi) ^ 2 := by positivity
  have hsqrtS : Real.sqrt S ≤ Real.sqrt (c * V * W4) + Real.sqrt (c * W0 * W2 / (2 * Real.pi) ^ 2) :=
    (Real.sqrt_le_sqrt hSle').trans (sqrt_add_le hS1 hS2)
  have hT1 : 2 * Real.sqrt (3 * M2) * Real.sqrt (c * V * W4) ≤
      nu * (2 * Real.pi) ^ 2 * W4 + 3 * c * V / (nu * (2 * Real.pi) ^ 2) * M2 := by
    have hprod : Real.sqrt (3 * M2) * Real.sqrt (c * V * W4) =
        Real.sqrt (nu * (2 * Real.pi) ^ 2 * W4) *
          Real.sqrt (3 * c * V * M2 / (nu * (2 * Real.pi) ^ 2)) := by
      rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul (by positivity)]
      congr 1
      field_simp
      try ring
    calc 2 * Real.sqrt (3 * M2) * Real.sqrt (c * V * W4)
        = 2 * Real.sqrt (nu * (2 * Real.pi) ^ 2 * W4) *
            Real.sqrt (3 * c * V * M2 / (nu * (2 * Real.pi) ^ 2)) := by
          rw [mul_assoc, hprod, ← mul_assoc]
      _ ≤ nu * (2 * Real.pi) ^ 2 * W4 + 3 * c * V * M2 / (nu * (2 * Real.pi) ^ 2) :=
          two_mul_sqrt_mul_sqrt_le (by positivity) (by positivity)
      _ = _ := by ring
  have hT2 : 2 * Real.sqrt (3 * M2) * Real.sqrt (c * W0 * W2 / (2 * Real.pi) ^ 2) ≤
      nu * (2 * Real.pi) ^ 2 * W4 / 2 + 18 * c * V / (nu * (2 * Real.pi) ^ 2) * W2 := by
    have hrad : 3 * M2 * (c * W0 * W2 / (2 * Real.pi) ^ 2) ≤ 9 * c * V * W2 * W4 := by
      have e1 : 3 * M2 * (c * W0 * W2 / (2 * Real.pi) ^ 2) ≤
          3 * W2 * (c * W0 * W2 / (2 * Real.pi) ^ 2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hM2W2 (by norm_num)) hS2
      have e2 : 3 * W2 * (c * W0 * W2 / (2 * Real.pi) ^ 2) =
          3 * c * W0 / (2 * Real.pi) ^ 2 * W2 ^ 2 := by ring
      have e3 : 3 * c * W0 / (2 * Real.pi) ^ 2 * W2 ^ 2 ≤
          3 * c * W0 / (2 * Real.pi) ^ 2 * (W0 * W4) :=
        mul_le_mul_of_nonneg_left hint1 (by positivity)
      have e4 : 3 * c * W0 / (2 * Real.pi) ^ 2 * (W0 * W4) =
          3 * c * W4 / (2 * Real.pi) ^ 2 * W0 ^ 2 := by ring
      have e5 : 3 * c * W4 / (2 * Real.pi) ^ 2 * W0 ^ 2 ≤
          3 * c * W4 / (2 * Real.pi) ^ 2 * (3 * (2 * Real.pi) ^ 2 * V * W2) :=
        mul_le_mul_of_nonneg_left hint0 (by positivity)
      have e6 : 3 * c * W4 / (2 * Real.pi) ^ 2 * (3 * (2 * Real.pi) ^ 2 * V * W2) =
          9 * c * V * W2 * W4 := by
        field_simp
        try ring
      linarith [e1, e2, e3, e4, e5, e6]
    have hprod : Real.sqrt (3 * M2) * Real.sqrt (c * W0 * W2 / (2 * Real.pi) ^ 2) =
        Real.sqrt (3 * M2 * (c * W0 * W2 / (2 * Real.pi) ^ 2)) :=
      (Real.sqrt_mul (by positivity) _).symm
    have hprod2 : Real.sqrt (9 * c * V * W2 * W4) =
        Real.sqrt (nu * (2 * Real.pi) ^ 2 * W4 / 2) *
          Real.sqrt (18 * c * V * W2 / (nu * (2 * Real.pi) ^ 2)) := by
      rw [← Real.sqrt_mul (by positivity)]
      congr 1
      field_simp
      try ring
    calc 2 * Real.sqrt (3 * M2) * Real.sqrt (c * W0 * W2 / (2 * Real.pi) ^ 2)
        = 2 * Real.sqrt (3 * M2 * (c * W0 * W2 / (2 * Real.pi) ^ 2)) := by rw [mul_assoc, hprod]
      _ ≤ 2 * Real.sqrt (9 * c * V * W2 * W4) :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hrad) (by norm_num)
      _ = 2 * Real.sqrt (nu * (2 * Real.pi) ^ 2 * W4 / 2) *
            Real.sqrt (18 * c * V * W2 / (nu * (2 * Real.pi) ^ 2)) := by rw [hprod2, ← mul_assoc]
      _ ≤ nu * (2 * Real.pi) ^ 2 * W4 / 2 + 18 * c * V * W2 / (nu * (2 * Real.pi) ^ 2) :=
          two_mul_sqrt_mul_sqrt_le (by positivity) (by positivity)
      _ = _ := by ring
  have hmain : 2 * Real.sqrt (3 * M2) * Real.sqrt S ≤
      2 * Real.sqrt (3 * M2) * Real.sqrt (c * V * W4) +
        2 * Real.sqrt (3 * M2) * Real.sqrt (c * W0 * W2 / (2 * Real.pi) ^ 2) := by
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left hsqrtS (by positivity)
  linarith [hT1, hT2, hmain]

/-! ## The cube family -/

/-- **The moment beyond the cube family is paid by the eleventh moment over `(N+1)^d`.** -/
theorem moment_le_cubeFamily {w d : ℕ} (hw : 1 ≤ w) (hwd : w + d = 11) (N : ℕ) (τ : ℝ)
    (hsum : Summable (eleventhMoment (velocity := velocity) τ)) :
    moment (velocity := velocity) w τ ≤ momentEnergy (velocity := velocity) w (cubeFamily N) τ +
      moment (velocity := velocity) 11 τ / ((N : ℝ) + 1) ^ d := by
  have hpt : ∀ q, momentPop (velocity := velocity) w τ q ≤
      (if q ∈ cubeFamily N then momentPop (velocity := velocity) w τ q else 0) +
        momentPop (velocity := velocity) 11 τ q / ((N : ℝ) + 1) ^ d := by
    intro q
    by_cases hq : q ∈ cubeFamily N
    · rw [if_pos hq]
      have h11 := momentPop_nonneg (velocity := velocity) 11 τ q
      have : 0 ≤ momentPop (velocity := velocity) 11 τ q / ((N : ℝ) + 1) ^ d := by positivity
      linarith
    · rw [if_neg hq, zero_add]
      by_cases h0 : q = 0
      · subst h0
        rw [momentPop_zero w hw, momentPop_zero 11 (by norm_num)]
        simp
      · have hN : N + 1 ≤ frequencySup q := by
          by_contra hlt
          push Not at hlt
          exact hq (Finset.mem_erase.mpr
            ⟨h0, (mem_frequencyCube_iff_frequencySup_le N q).mpr (by omega)⟩)
        unfold momentPop
        have hN' : ((N : ℝ) + 1) ≤ ((frequencySup q : ℕ) : ℝ) := by exact_mod_cast hN
        have hE := modalEnergy_nonneg (velocity := velocity) q τ
        rw [le_div_iff₀ (by positivity)]
        have hd : ((N : ℝ) + 1) ^ d ≤ ((frequencySup q : ℕ) : ℝ) ^ d :=
          pow_le_pow_left₀ (by positivity) hN' d
        calc ((frequencySup q : ℕ) : ℝ) ^ w * modalEnergy (velocity := velocity) q τ *
              ((N : ℝ) + 1) ^ d
            ≤ ((frequencySup q : ℕ) : ℝ) ^ w * modalEnergy (velocity := velocity) q τ *
              ((frequencySup q : ℕ) : ℝ) ^ d :=
              mul_le_mul_of_nonneg_left hd (mul_nonneg (by positivity) hE)
          _ = _ := by rw [← hwd, pow_add]; ring
  have hsumw := summable_momentPop (velocity := velocity) hw (by omega) τ hsum
  have hsum11 :=
    summable_momentPop (velocity := velocity) (by norm_num : 1 ≤ 11) (by norm_num) τ hsum
  have hsumA : Summable fun q ↦
      (if q ∈ cubeFamily N then momentPop (velocity := velocity) w τ q else 0) :=
    summable_of_ne_finset_zero (s := cubeFamily N) fun q hq ↦ if_neg hq
  have hsumB : Summable fun q ↦ momentPop (velocity := velocity) 11 τ q / ((N : ℝ) + 1) ^ d :=
    hsum11.div_const _
  calc moment (velocity := velocity) w τ = ∑' q, momentPop (velocity := velocity) w τ q := rfl
    _ ≤ ∑' q, ((if q ∈ cubeFamily N then momentPop (velocity := velocity) w τ q else 0) +
          momentPop (velocity := velocity) 11 τ q / ((N : ℝ) + 1) ^ d) :=
        hsumw.tsum_le_tsum hpt (hsumA.add hsumB)
    _ = (∑' q, (if q ∈ cubeFamily N then momentPop (velocity := velocity) w τ q else 0)) +
          ∑' q, momentPop (velocity := velocity) 11 τ q / ((N : ℝ) + 1) ^ d :=
        hsumA.tsum_add hsumB
    _ = _ := by
        rw [tsum_eq_sum (s := cubeFamily N) (fun q hq ↦ if_neg hq), tsum_div_const,
          momentEnergy_eq_sum]
        congr 1
        exact Finset.sum_congr rfl fun q hq ↦ if_pos hq

/-- **The cube-family Riccati on incoherent receivers with vanishing forcing.** -/
theorem momentEnergy_cubeFamily_riccati_incoherent (hnu : 0 < nu) (N : ℕ)
    (hsum : Summable (eleventhMoment (velocity := velocity) t.1))
    (hinc : ∀ k : SpatialFrequency, k ≠ 0 → IncoherentAt solution t k) {V₀ : ℝ}
    (hV : velocityMass solution t ≤ V₀) :
    ∃ D : ℝ, HasDerivAt (momentEnergy (velocity := velocity) 2 (cubeFamily N)) D t.1 ∧
      D ≤ 21 * incoherentConstant * V₀ / (nu * (2 * Real.pi) ^ 2) *
          momentEnergy (velocity := velocity) 2 (cubeFamily N) t.1 +
        (3 / 2 * (nu * (2 * Real.pi) ^ 2) +
          18 * incoherentConstant * V₀ / (nu * (2 * Real.pi) ^ 2)) *
          (moment (velocity := velocity) 11 t.1 / ((N : ℝ) + 1) ^ 7) := by
  obtain ⟨D, hD, hle⟩ := momentEnergy_riccati_incoherent solution t hnu
    (fun k hk ↦ one_le_frequencySup_of_mem_cubeFamily hk) hsum
    (fun k hk ↦ hinc k (Finset.ne_of_mem_erase hk))
  refine ⟨D, hD, hle.trans ?_⟩
  have hW4 := moment_le_cubeFamily (velocity := velocity) (w := 4) (d := 7) (by norm_num) (by norm_num)
    N t.1 hsum
  have hW2 := moment_le_cubeFamily (velocity := velocity) (w := 2) (d := 9) (by norm_num) (by norm_num)
    N t.1 hsum
  set c : ℝ := incoherentConstant with hc
  set V : ℝ := velocityMass solution t with hV'
  set M2 : ℝ := momentEnergy (velocity := velocity) 2 (cubeFamily N) t.1 with hM2
  set M4 : ℝ := momentEnergy (velocity := velocity) 4 (cubeFamily N) t.1 with hM4
  set W2 : ℝ := moment (velocity := velocity) 2 t.1 with hW2'
  set W4 : ℝ := moment (velocity := velocity) 4 t.1 with hW4'
  set R7 : ℝ := moment (velocity := velocity) 11 t.1 / ((N : ℝ) + 1) ^ 7 with hR7
  set R9 : ℝ := moment (velocity := velocity) 11 t.1 / ((N : ℝ) + 1) ^ 9 with hR9
  have hPpos : 0 < nu * (2 * Real.pi) ^ 2 := by positivity
  have hc0 : 0 ≤ c := incoherentConstant_nonneg
  have hV0 : 0 ≤ V := velocityMass_nonneg solution t
  have hV₀0 : 0 ≤ V₀ := hV0.trans hV
  have hM20 : 0 ≤ M2 := momentEnergy_nonneg _ _ _
  have hM40 : 0 ≤ M4 := momentEnergy_nonneg _ _ _
  have hW20 : 0 ≤ W2 := moment_nonneg _ _
  have hW40 : 0 ≤ W4 := moment_nonneg _ _
  have hW11 : 0 ≤ moment (velocity := velocity) 11 t.1 := moment_nonneg _ _
  have hR : R9 ≤ R7 := by
    rw [hR7, hR9]
    apply div_le_div_of_nonneg_left hW11 (by positivity)
    exact pow_le_pow_right₀ (by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]) (by norm_num)
  have h1 : 3 / 2 * (nu * (2 * Real.pi) ^ 2) * W4 ≤ 3 / 2 * (nu * (2 * Real.pi) ^ 2) * (M4 + R7) :=
    mul_le_mul_of_nonneg_left hW4 (by positivity)
  have h2 : 3 * c * V / (nu * (2 * Real.pi) ^ 2) * M2 ≤ 3 * c * V₀ / (nu * (2 * Real.pi) ^ 2) * M2 :=
    mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hV (by positivity)) hPpos.le) hM20
  have h3 : 18 * c * V / (nu * (2 * Real.pi) ^ 2) * W2 ≤ 18 * c * V₀ / (nu * (2 * Real.pi) ^ 2) * W2 :=
    mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hV (by positivity)) hPpos.le) hW20
  have h4 : 18 * c * V₀ / (nu * (2 * Real.pi) ^ 2) * W2 ≤
      18 * c * V₀ / (nu * (2 * Real.pi) ^ 2) * (M2 + R9) :=
    mul_le_mul_of_nonneg_left hW2 (by positivity)
  have h5 : 18 * c * V₀ / (nu * (2 * Real.pi) ^ 2) * R9 ≤
      18 * c * V₀ / (nu * (2 * Real.pi) ^ 2) * R7 :=
    mul_le_mul_of_nonneg_left hR (by positivity)
  have h6 : 0 ≤ nu * (2 * Real.pi) ^ 2 * M4 := mul_nonneg hPpos.le hM40
  simp only [div_eq_mul_inv] at h1 h2 h3 h4 h5 ⊢
  linarith [h1, h2, h3, h4, h5, h6]

/-- **Grönwall on the cube family under incoherence.** -/
theorem momentEnergy_cubeFamily_le_incoherent (hnu : 0 < nu) (N : ℕ) {s τ : ℝ} (hs : s ∈ Ioo 0 T)
    (hτ : τ ∈ Ioo 0 T) (hsτ : s ≤ τ) {V₀ B : ℝ} (hV₀ : 0 ≤ V₀) (hB : 0 ≤ B)
    (hσ : ∀ σ (hσ : σ ∈ Ioo 0 T), σ ∈ Icc s τ →
      Summable (eleventhMoment (velocity := velocity) σ) ∧
        velocityMass solution ⟨σ, hσ⟩ ≤ V₀ ∧
        (∀ k : SpatialFrequency, k ≠ 0 → IncoherentAt solution ⟨σ, hσ⟩ k) ∧
        moment (velocity := velocity) 11 σ ≤ B) :
    momentEnergy (velocity := velocity) 2 (cubeFamily N) τ ≤
      (momentEnergy (velocity := velocity) 2 (cubeFamily N) s +
        (3 / 2 * (nu * (2 * Real.pi) ^ 2) +
          18 * incoherentConstant * V₀ / (nu * (2 * Real.pi) ^ 2)) * B / ((N : ℝ) + 1) ^ 7 *
          (τ - s)) *
        Real.exp (21 * incoherentConstant * V₀ / (nu * (2 * Real.pi) ^ 2) * (τ - s)) := by
  have hc0 := incoherentConstant_nonneg
  refine le_exp_of_hasDerivAt_le (by positivity) (by positivity) hsτ ?_
  intro σ hσI
  have hσT : σ ∈ Ioo 0 T := ⟨hs.1.trans_le hσI.1, hσI.2.trans_lt hτ.2⟩
  obtain ⟨hsum, hV, hinc, h11⟩ := hσ σ hσT hσI
  obtain ⟨D, hD, hle⟩ :=
    momentEnergy_cubeFamily_riccati_incoherent solution ⟨σ, hσT⟩ hnu N hsum hinc hV
  dsimp only at hD hle
  refine ⟨D, hD, hle.trans ?_⟩
  have hA : 0 ≤ 3 / 2 * (nu * (2 * Real.pi) ^ 2) +
      18 * incoherentConstant * V₀ / (nu * (2 * Real.pi) ^ 2) := by positivity
  have hR : moment (velocity := velocity) 11 σ / ((N : ℝ) + 1) ^ 7 ≤ B / ((N : ℝ) + 1) ^ 7 :=
    div_le_div_of_nonneg_right h11 (by positivity)
  calc _ ≤ 21 * incoherentConstant * V₀ / (nu * (2 * Real.pi) ^ 2) *
        momentEnergy (velocity := velocity) 2 (cubeFamily N) σ +
        (3 / 2 * (nu * (2 * Real.pi) ^ 2) +
          18 * incoherentConstant * V₀ / (nu * (2 * Real.pi) ^ 2)) * (B / ((N : ℝ) + 1) ^ 7) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hR hA)
    _ = _ := by ring

/-- **The passage from the cube families to the moment.** -/
theorem moment_le_of_cubeFamily_le {w d : ℕ} (hw : 1 ≤ w) (hd : d ≠ 0) {s τ : ℝ} (hsτ : s ≤ τ)
    (hsums : Summable (momentPop (velocity := velocity) w s)) {b C : ℝ} (_hb : 0 ≤ b) (hC : 0 ≤ C)
    (h : ∀ N : ℕ, momentEnergy (velocity := velocity) w (cubeFamily N) τ ≤
      (momentEnergy (velocity := velocity) w (cubeFamily N) s + C / ((N : ℝ) + 1) ^ d * (τ - s)) *
        Real.exp (b * (τ - s))) :
    moment (velocity := velocity) w τ ≤ moment (velocity := velocity) w s * Real.exp (b * (τ - s)) := by
  refine Real.tsum_le_of_sum_le (momentPop_nonneg w τ) fun G ↦ ?_
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ k ∈ G, frequencySup k ≤ N :=
    ⟨G.sup frequencySup, fun k hk ↦ Finset.le_sup (f := frequencySup) hk⟩
  refine le_of_forall_pos_lt_add fun ε hε ↦ ?_
  have hts : 0 ≤ τ - s := sub_nonneg.mpr hsτ
  set K : ℝ := C * (τ - s) * Real.exp (b * (τ - s)) with hK
  have hK0 : 0 ≤ K := mul_nonneg (mul_nonneg hC hts) (Real.exp_pos _).le
  obtain ⟨M, hM⟩ := exists_nat_gt (K / ε)
  set N' : ℕ := max N M with hN'
  have hGsub : G ⊆ insert 0 (cubeFamily N') := by
    intro k hk
    rw [Finset.mem_insert]
    by_cases h0 : k = 0
    · exact Or.inl h0
    · right
      exact Finset.mem_erase.mpr ⟨h0, (mem_frequencyCube_iff_frequencySup_le N' k).mpr
        ((hN k hk).trans (le_max_left N M))⟩
  have hexp0 : 0 ≤ Real.exp (b * (τ - s)) := (Real.exp_pos _).le
  have hMs : momentEnergy (velocity := velocity) w (cubeFamily N') s ≤
      moment (velocity := velocity) w s :=
    hsums.sum_le_tsum _ fun k _ ↦ momentPop_nonneg w s k
  have hposd : (0 : ℝ) < ((N' : ℝ) + 1) ^ d := by positivity
  have hKε : K / ((N' : ℝ) + 1) ^ d < ε := by
    rw [div_lt_iff₀ hposd]
    have hKM : K < ε * M := by
      rw [div_lt_iff₀ hε] at hM
      linarith
    have hMN : (M : ℝ) ≤ (N' : ℝ) := by exact_mod_cast le_max_right N M
    have hN1 : (N' : ℝ) + 1 ≤ ((N' : ℝ) + 1) ^ d :=
      le_self_pow₀ (by linarith [(Nat.cast_nonneg N' : (0 : ℝ) ≤ N')]) hd
    have : (M : ℝ) ≤ ((N' : ℝ) + 1) ^ d := by linarith
    calc K < ε * M := hKM
      _ ≤ ε * ((N' : ℝ) + 1) ^ d := mul_le_mul_of_nonneg_left this hε.le
  calc ∑ k ∈ G, momentPop (velocity := velocity) w τ k
      ≤ ∑ k ∈ insert 0 (cubeFamily N'), momentPop (velocity := velocity) w τ k :=
        Finset.sum_le_sum_of_subset_of_nonneg hGsub fun k _ _ ↦ momentPop_nonneg w τ k
    _ = momentEnergy (velocity := velocity) w (cubeFamily N') τ := by
        rw [Finset.sum_insert (by simp [cubeFamily]), momentPop_zero w hw, zero_add]
        rfl
    _ ≤ (momentEnergy (velocity := velocity) w (cubeFamily N') s +
          C / ((N' : ℝ) + 1) ^ d * (τ - s)) * Real.exp (b * (τ - s)) := h N'
    _ ≤ (moment (velocity := velocity) w s + C / ((N' : ℝ) + 1) ^ d * (τ - s)) *
          Real.exp (b * (τ - s)) :=
        mul_le_mul_of_nonneg_right (add_le_add hMs le_rfl) hexp0
    _ = moment (velocity := velocity) w s * Real.exp (b * (τ - s)) + K / ((N' : ℝ) + 1) ^ d := by
        rw [hK]; ring
    _ < moment (velocity := velocity) w s * Real.exp (b * (τ - s)) + ε := by linarith

/-- **The second moment along a terminal tail on incoherent feeds.** -/
theorem moment_two_le (hnu : 0 < nu) {s τ : ℝ} (hs : s ∈ Ioo 0 T) (hτ : τ ∈ Ioo 0 T) (hsτ : s ≤ τ)
    {V₀ B : ℝ} (hV₀ : 0 ≤ V₀) (hB : 0 ≤ B)
    (hσ : ∀ σ (hσ : σ ∈ Ioo 0 T), σ ∈ Icc s τ →
      Summable (eleventhMoment (velocity := velocity) σ) ∧
        velocityMass solution ⟨σ, hσ⟩ ≤ V₀ ∧
        (∀ k : SpatialFrequency, k ≠ 0 → IncoherentAt solution ⟨σ, hσ⟩ k) ∧
        moment (velocity := velocity) 11 σ ≤ B) :
    moment (velocity := velocity) 2 τ ≤ moment (velocity := velocity) 2 s *
      Real.exp (21 * incoherentConstant * V₀ / (nu * (2 * Real.pi) ^ 2) * (τ - s)) := by
  obtain ⟨hsums, -, -, -⟩ := hσ s hs ⟨le_rfl, hsτ⟩
  have hc0 := incoherentConstant_nonneg
  refine moment_le_of_cubeFamily_le (velocity := velocity) (w := 2) (d := 7) (by norm_num)
    (by norm_num) hsτ (summable_momentPop (w := 2) (by norm_num) (by norm_num) s hsums)
    (b := 21 * incoherentConstant * V₀ / (nu * (2 * Real.pi) ^ 2))
    (C := (3 / 2 * (nu * (2 * Real.pi) ^ 2) +
      18 * incoherentConstant * V₀ / (nu * (2 * Real.pi) ^ 2)) * B)
    (by positivity) (by positivity) fun N ↦ ?_
  exact momentEnergy_cubeFamily_le_incoherent solution hnu N hs hτ hsτ hV₀ hB hσ

/-! ## The closure statement -/

/-- **Incoherence control.**  Along a terminal tail `[s, T)`: the eleventh moment is finite, the
velocity mass is at most `V₀`, every nonzero receiver is incoherent, and the eleventh moment is
bounded on every compact `[s, τ]`, `τ < T`. -/
def IncoherentControl : Prop :=
  ∀ {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField},
    0 < nu →
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure) →
      ∃ (s V₀ : ℝ), 0 < s ∧ s < T ∧ 0 ≤ V₀ ∧
        (∀ σ (hσ : σ ∈ Ioo 0 T), s ≤ σ →
          Summable (eleventhMoment (velocity := velocity) σ) ∧
            velocityMass solution ⟨σ, hσ⟩ ≤ V₀ ∧
            ∀ k : SpatialFrequency, k ≠ 0 → IncoherentAt solution ⟨σ, hσ⟩ k) ∧
        (∀ τ ∈ Ioo s T, ∃ B : ℝ, ∀ σ ∈ Icc s τ, moment (velocity := velocity) 11 σ ≤ B)

theorem l1Pop_zero_le_sqrt {V₀ : ℝ} (hV : velocityMass solution t ≤ V₀) :
    l1Pop solution t 0 ≤ Real.sqrt (3 * V₀) := by
  apply Real.le_sqrt_of_sq_le
  have h1 : l1Pop solution t 0 ^ 2 ≤ 3 * velPop solution t 0 := by
    unfold l1Pop complexVectorL1 velPop
    rw [Fin.sum_univ_three]
    nlinarith [sq_nonneg (‖openPeriodicVelocityFourierMode solution t 0 0‖ -
        ‖openPeriodicVelocityFourierMode solution t 0 1‖),
      sq_nonneg (‖openPeriodicVelocityFourierMode solution t 0 0‖ -
        ‖openPeriodicVelocityFourierMode solution t 0 2‖),
      sq_nonneg (‖openPeriodicVelocityFourierMode solution t 0 1‖ -
        ‖openPeriodicVelocityFourierMode solution t 0 2‖)]
  have h2 := velPop_le_velocityMass solution t 0
  linarith

/-- The closure bound in the velocity mass and a bound on the second moment. -/
def closureBound (V₀ W : ℝ) : ℝ :=
  3 ^ 3 * (2 * Real.pi) ^ 2 * 3 * 2 ^ 5 *
    (3 / (2 * Real.pi) ^ 2 * 52 * W +
      (Real.sqrt (3 * V₀) + Real.sqrt (52 * (3 / (2 * Real.pi) ^ 2)) * Real.sqrt W) ^ 2)

theorem closureBound_nonneg {V₀ W : ℝ} (_hV₀ : 0 ≤ V₀) (hW : 0 ≤ W) : 0 ≤ closureBound V₀ W := by
  unfold closureBound; positivity

theorem closureDrive_le_closureBound (hnu : 0 < nu) {V₀ W : ℝ} (_hW0 : 0 ≤ W)
    (hV : velocityMass solution t ≤ V₀) (hW : moment (velocity := velocity) 2 t.1 ≤ W) :
    closureDrive solution t ≤ 3 * closureBound V₀ W / (nu * (2 * Real.pi) ^ 2) := by
  unfold closureDrive closureCoefficient closureBound
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add (mul_le_mul_of_nonneg_left hW (by positivity))
  apply pow_le_pow_left₀ (add_nonneg (l1Pop_nonneg _ _ _)
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))
  exact add_le_add (l1Pop_zero_le_sqrt solution t hV)
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hW) (Real.sqrt_nonneg _))

/-- **Incoherence control returns closure-drive control.** -/
theorem closureDrive_of_incoherent (h : IncoherentControl) : ClosureDriveControl := by
  intro T nu initial velocity pressure hnu solution
  obtain ⟨s, V₀, hs0, hsT, hV₀, htail, hcompact⟩ := h hnu solution
  have hs : s ∈ Ioo 0 T := ⟨hs0, hsT⟩
  have hc0 := incoherentConstant_nonneg
  set b : ℝ := 21 * incoherentConstant * V₀ / (nu * (2 * Real.pi) ^ 2) with hb
  have hb0 : 0 ≤ b := by positivity
  set Wstar : ℝ := moment (velocity := velocity) 2 s * Real.exp (b * (T - s)) with hWstar
  have hW2s := moment_nonneg (velocity := velocity) 2 s
  have hWstar0 : 0 ≤ Wstar := mul_nonneg hW2s (Real.exp_pos _).le
  have hW2 : ∀ σ (hσ : σ ∈ Ioo 0 T), s ≤ σ → moment (velocity := velocity) 2 σ ≤ Wstar := by
    intro σ hσ hsσ
    have hexp : Real.exp (b * (σ - s)) ≤ Real.exp (b * (T - s)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith [hσ.2]) hb0)
    rcases eq_or_lt_of_le hsσ with hEq | hlt
    · rw [← hEq]
      have h1 : (1 : ℝ) ≤ Real.exp (b * (T - s)) :=
        Real.one_le_exp (mul_nonneg hb0 (by linarith [hsT]))
      exact le_mul_of_one_le_right hW2s h1
    · obtain ⟨B, hB⟩ := hcompact σ ⟨hlt, hσ.2⟩
      obtain ⟨B', hB'0, hB'⟩ : ∃ B' : ℝ, 0 ≤ B' ∧
          ∀ ρ ∈ Icc s σ, moment (velocity := velocity) 11 ρ ≤ B' :=
        ⟨max B 0, le_max_right _ _, fun ρ hρ ↦ (hB ρ hρ).trans (le_max_left _ _)⟩
      have hσ' : ∀ ρ (hρ : ρ ∈ Ioo 0 T), ρ ∈ Icc s σ →
          Summable (eleventhMoment (velocity := velocity) ρ) ∧
            velocityMass solution ⟨ρ, hρ⟩ ≤ V₀ ∧
            (∀ k : SpatialFrequency, k ≠ 0 → IncoherentAt solution ⟨ρ, hρ⟩ k) ∧
            moment (velocity := velocity) 11 ρ ≤ B' :=
        fun ρ hρT hρI ↦ ⟨(htail ρ hρT hρI.1).1, (htail ρ hρT hρI.1).2.1,
          (htail ρ hρT hρI.1).2.2, hB' ρ hρI⟩
      calc moment (velocity := velocity) 2 σ
          ≤ moment (velocity := velocity) 2 s * Real.exp (b * (σ - s)) :=
            moment_two_le solution hnu hs hσ hsσ hV₀ hB'0 hσ'
        _ ≤ Wstar := mul_le_mul_of_nonneg_left hexp hW2s
  refine ⟨s, 3 * closureBound V₀ Wstar / (nu * (2 * Real.pi) ^ 2), hs0, hsT, ?_, ?_, hcompact⟩
  · have := closureBound_nonneg hV₀ hWstar0
    positivity
  · intro σ hσ hsσ
    exact ⟨(htail σ hσ hsσ).1, closureDrive_le_closureBound solution ⟨σ, hσ⟩ hnu hWstar0
      (htail σ hσ hsσ).2.1 (hW2 σ hσ hsσ)⟩

/-- **Incoherence control returns Statement B.** -/
theorem statementB_of_incoherence (h : IncoherentControl) : StatementB :=
  statementB_of_closureDrive (closureDrive_of_incoherent h)

theorem officialProblem_of_incoherence (h : IncoherentControl) :
    TheOfficialNavierStokesProblem :=
  officialProblem_of_closureDrive (closureDrive_of_incoherent h)

section Audit

#print axioms moment_two_sq_le
#print axioms moment_zero_sq_le
#print axioms momentEnergy_riccati_incoherent
#print axioms moment_two_le
#print axioms statementB_of_incoherence

end Audit

end Soma.Holonics.Millennium.NavierStokesIncoherentClosure
