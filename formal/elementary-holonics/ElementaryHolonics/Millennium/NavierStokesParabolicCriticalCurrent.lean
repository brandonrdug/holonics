import ElementaryHolonics.Millennium.NavierStokesParabolicVorticityCurrent
import ElementaryHolonics.Millennium.NavierStokesCriticalVorticityRate

/-!
# The BKM current is invariant under the exact parabolic cover

**[proved-derived]** The complete parabolic solution carrier and its vorticity weight are now
composed with the genuine torus `L∞` receiver used by the repository's BKM continuation theorem.
For a positive natural cover degree `n`, the source is observed on lifespan `n² T` and its
parabolic image on lifespan `T`.  The pointwise critical rate carries weight `n²`; chronological
change of variables carries the inverse weight, so the complete accumulated critical current is
unchanged.

This is the scale-critical local-to-global law for the actual continuation receiver.  It does not
assert that the accumulated current is finite; it proves exactly that finiteness or divergence is
preserved by the admitted cover passage.
-/

noncomputable section

open MeasureTheory Real Set
open scoped Interval

namespace Soma.Holonics.Millennium.NavierStokesParabolicCriticalCurrent

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesCriticalVorticityRate
open Soma.Holonics.Millennium.NavierStokesVorticity
open Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy
open Soma.Holonics.Millennium.NavierStokesParabolicRebase
open Soma.Holonics.Millennium.NavierStokesParabolicVorticityCurrent

/-- The source global solution restricted to the chronology seen before an `n²` time fold. -/
def sourceOpenAtParabolicCover
    {nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : PeriodicSolution nu initial force velocity pressure)
    (cover : ℕ) (hcover : 0 < cover) {T : ℝ} (hT : 0 < T) :
    OpenPeriodicSolutionOn ((cover : ℝ) ^ 2 * T)
      nu initial force velocity pressure :=
  Soma.Holonics.Millennium.NavierStokesOpenLifespan.PeriodicSolution.toOpenPeriodicSolutionOn
    solution (mul_pos (sq_pos_of_ne_zero (Nat.cast_ne_zero.mpr hcover.ne')) hT)

/-- The returned global solution restricted to the receiver chronology after the cover. -/
def returnedOpenAtParabolicCover
    {nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : PeriodicSolution nu initial force velocity pressure)
    (cover : ℕ) (hcover : 0 < cover) {T : ℝ} (hT : 0 < T) :
    OpenPeriodicSolutionOn T nu
      (parabolicInitialVelocity (cover : ℝ) initial)
      (parabolicForce (cover : ℝ) force)
      (parabolicVelocity (cover : ℝ) velocity)
      (parabolicPressure (cover : ℝ) pressure) :=
  Soma.Holonics.Millennium.NavierStokesOpenLifespan.PeriodicSolution.toOpenPeriodicSolutionOn
    (Soma.Holonics.Millennium.NavierStokesParabolicRebase.PeriodicSolution.parabolicNat
      solution cover hcover) hT

/-- The genuine critical vorticity rate carries exactly the quadratic parabolic weight.  Both
inequality directions use the complete pointwise characterization of the torus norm; the reverse
direction explicitly reconstructs a source representative through the inverse spatial chart. -/
theorem criticalVorticityRate_returnedOpenAtParabolicCover
    {nu T : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : PeriodicSolution nu initial force velocity pressure)
    (cover : ℕ) (hcover : 0 < cover) (hT : 0 < T)
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    criticalVorticityRate
        (returnedOpenAtParabolicCover solution cover hcover hT) t =
      (cover : ℝ) ^ 2 *
        criticalVorticityRate
          (sourceOpenAtParabolicCover solution cover hcover hT)
          ((cover : ℝ) ^ 2 * t) := by
  let scale : ℝ := cover
  have hscale : 0 < scale := by
    change (0 : ℝ) < (cover : ℝ)
    exact_mod_cast hcover
  have hscaleSq : 0 < scale ^ 2 := sq_pos_of_pos hscale
  have hsourceTime :
      scale ^ 2 * t ∈ Ioo 0 (scale ^ 2 * T) :=
    ⟨mul_pos hscaleSq ht.1, mul_lt_mul_of_pos_left ht.2 hscaleSq⟩
  have hsourcePoint : ∀ y : Space,
      ‖vorticityField velocity y (scale ^ 2 * t)‖ ≤
        criticalVorticityRate
          (sourceOpenAtParabolicCover solution cover hcover hT) (scale ^ 2 * t) :=
    (criticalVorticityRate_le_iff
      (sourceOpenAtParabolicCover solution cover hcover hT) hsourceTime).mp le_rfl
  have hreturnedPoint : ∀ x : Space,
      ‖vorticityField (parabolicVelocity scale velocity) x t‖ ≤
        criticalVorticityRate
          (returnedOpenAtParabolicCover solution cover hcover hT) t :=
    (criticalVorticityRate_le_iff
      (returnedOpenAtParabolicCover solution cover hcover hT) ht).mp le_rfl
  apply le_antisymm
  · apply (criticalVorticityRate_le_iff
      (returnedOpenAtParabolicCover solution cover hcover hT) ht).mpr
    intro x
    rw [vorticityField_parabolicVelocity, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg scale)]
    exact mul_le_mul_of_nonneg_left (hsourcePoint (scale • x)) (sq_nonneg scale)
  · have hsourceBound :
        criticalVorticityRate
            (sourceOpenAtParabolicCover solution cover hcover hT) (scale ^ 2 * t) ≤
          criticalVorticityRate
              (returnedOpenAtParabolicCover solution cover hcover hT) t /
            scale ^ 2 := by
      apply (criticalVorticityRate_le_iff
        (sourceOpenAtParabolicCover solution cover hcover hT) hsourceTime).mpr
      intro y
      rw [le_div_iff₀ hscaleSq]
      have hpoint := hreturnedPoint (scale⁻¹ • y)
      rw [vorticityField_parabolicVelocity, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (sq_nonneg scale)] at hpoint
      have hreturn : scale • (scale⁻¹ • y) = y := by
        rw [← mul_smul, mul_inv_cancel₀ hscale.ne', one_smul]
      rw [hreturn] at hpoint
      simpa [mul_comm] using hpoint
    have hmul := (le_div_iff₀ hscaleSq).mp hsourceBound
    simpa [mul_comm] using hmul

/-- The same rate law holds on the totalized real chronology.  Outside the respective open
lifespans both receivers are definitionally zero; positivity of the cover identifies the two
open-time occurrences exactly. -/
theorem criticalVorticityRate_returnedOpenAtParabolicCover_allTime
    {nu T : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : PeriodicSolution nu initial force velocity pressure)
    (cover : ℕ) (hcover : 0 < cover) (hT : 0 < T) (t : ℝ) :
    criticalVorticityRate
        (returnedOpenAtParabolicCover solution cover hcover hT) t =
      (cover : ℝ) ^ 2 *
        criticalVorticityRate
          (sourceOpenAtParabolicCover solution cover hcover hT)
          ((cover : ℝ) ^ 2 * t) := by
  by_cases ht : t ∈ Ioo 0 T
  · exact criticalVorticityRate_returnedOpenAtParabolicCover
      solution cover hcover hT ht
  · have hcoverReal : (0 : ℝ) < cover := by exact_mod_cast hcover
    have hcoverSq : (0 : ℝ) < (cover : ℝ) ^ 2 := sq_pos_of_pos hcoverReal
    have hsourceNot :
        (cover : ℝ) ^ 2 * t ∉ Ioo 0 ((cover : ℝ) ^ 2 * T) := by
      intro hsource
      apply ht
      exact ⟨
        (mul_lt_mul_iff_right₀ hcoverSq).mp (by simpa using hsource.1),
        (mul_lt_mul_iff_right₀ hcoverSq).mp hsource.2⟩
    simp [criticalVorticityRate, ht, hsourceNot]

/-- The accumulated BKM current is exactly invariant under the complete parabolic cover.  The
quadratic vorticity weight is cancelled by the inverse quadratic chronology aperture; no estimate,
limit, or rounding enters this identity. -/
theorem integral_criticalVorticityRate_parabolicCover
    {nu T : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : PeriodicSolution nu initial force velocity pressure)
    (cover : ℕ) (hcover : 0 < cover) (hT : 0 < T) :
    (∫ t in 0..T,
        criticalVorticityRate
          (returnedOpenAtParabolicCover solution cover hcover hT) t) =
      ∫ s in 0..((cover : ℝ) ^ 2 * T),
        criticalVorticityRate
          (sourceOpenAtParabolicCover solution cover hcover hT) s := by
  calc
    (∫ t in 0..T,
        criticalVorticityRate
          (returnedOpenAtParabolicCover solution cover hcover hT) t) =
        ∫ t in 0..T, (cover : ℝ) ^ 2 *
          criticalVorticityRate
            (sourceOpenAtParabolicCover solution cover hcover hT)
            ((cover : ℝ) ^ 2 * t) := by
              apply intervalIntegral.integral_congr
              intro t _
              exact criticalVorticityRate_returnedOpenAtParabolicCover_allTime
                solution cover hcover hT t
    _ = (cover : ℝ) ^ 2 *
        (∫ t in 0..T,
          criticalVorticityRate
            (sourceOpenAtParabolicCover solution cover hcover hT)
            ((cover : ℝ) ^ 2 * t)) := by
              rw [intervalIntegral.integral_const_mul]
    _ = ∫ s in (cover : ℝ) ^ 2 * 0..(cover : ℝ) ^ 2 * T,
        criticalVorticityRate
          (sourceOpenAtParabolicCover solution cover hcover hT) s := by
            simpa only [smul_eq_mul] using
              (intervalIntegral.smul_integral_comp_mul_left
                (f := criticalVorticityRate
                  (sourceOpenAtParabolicCover solution cover hcover hT))
                (a := 0) (b := T) ((cover : ℝ) ^ 2))
    _ = ∫ s in 0..((cover : ℝ) ^ 2 * T),
        criticalVorticityRate
          (sourceOpenAtParabolicCover solution cover hcover hT) s := by simp

/-- Terminal critical-current finiteness is preserved and reflected by the parabolic cover.  This
is the exact insufficiency result for scale repetition: an admitted cover can neither create nor
remove the BKM obstruction. -/
theorem intervalIntegrable_criticalVorticityRate_parabolicCover_iff
    {nu T : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : PeriodicSolution nu initial force velocity pressure)
    (cover : ℕ) (hcover : 0 < cover) (hT : 0 < T) :
    IntervalIntegrable
        (criticalVorticityRate
          (returnedOpenAtParabolicCover solution cover hcover hT)) volume 0 T ↔
      IntervalIntegrable
        (criticalVorticityRate
          (sourceOpenAtParabolicCover solution cover hcover hT)) volume
        0 ((cover : ℝ) ^ 2 * T) := by
  let c : ℝ := (cover : ℝ) ^ 2
  let sourceRate : ℝ → ℝ :=
    criticalVorticityRate
      (sourceOpenAtParabolicCover solution cover hcover hT)
  let returnedRate : ℝ → ℝ :=
    criticalVorticityRate
      (returnedOpenAtParabolicCover solution cover hcover hT)
  have hcoverReal : (0 : ℝ) < cover := by exact_mod_cast hcover
  have hc : c ≠ 0 := (sq_pos_of_pos hcoverReal).ne'
  have hreturned :
      IntervalIntegrable returnedRate volume 0 T ↔
        IntervalIntegrable (fun t ↦ c * sourceRate (c * t)) volume 0 T := by
    apply intervalIntegrable_congr
    intro t _
    exact criticalVorticityRate_returnedOpenAtParabolicCover_allTime
      solution cover hcover hT t
  have hcoefficient :
      IntervalIntegrable (fun t ↦ c * sourceRate (c * t)) volume 0 T ↔
        IntervalIntegrable (fun t ↦ sourceRate (c * t)) volume 0 T := by
    constructor
    · intro h
      simpa [hc, mul_assoc] using h.const_mul c⁻¹
    · intro h
      exact h.const_mul c
  have hchronology :
      IntervalIntegrable (fun t ↦ sourceRate (c * t)) volume 0 T ↔
        IntervalIntegrable sourceRate volume 0 (c * T) := by
    simpa [hc] using
      (IntervalIntegrable.comp_mul_left_iff
        (f := sourceRate) (a := 0) (b := c * T) hc)
  exact hreturned.trans (hcoefficient.trans hchronology)

section Audit

#print axioms criticalVorticityRate_returnedOpenAtParabolicCover
#print axioms criticalVorticityRate_returnedOpenAtParabolicCover_allTime
#print axioms integral_criticalVorticityRate_parabolicCover
#print axioms intervalIntegrable_criticalVorticityRate_parabolicCover_iff

end Audit

end Soma.Holonics.Millennium.NavierStokesParabolicCriticalCurrent
