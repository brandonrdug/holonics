import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Order.Basic

/-!
# A finite physical clock for a moving frame

This module records the elementary clock used by the moving-frame construction.  For positive
`B` and `k`,

```text
t(s) = t₀ + (B / k) (1 - exp (-k s))
```

has positive derivative, approaches the finite endpoint `t₀ + B / k`, and leaves the exact
remaining-time law `(t₀ + B / k) - t(s) = (B / k) exp (-k s)`.  The exponential scale ratio is
recorded separately.  No PDE, continuation theorem, or interpretation of a reciprocal Stokes
clock is imported here.

The final theorem is scoped to an actual path and receiver: continuity of that path at the finite
physical endpoint rules out an `atTop` norm along any clock tending to that endpoint.
-/

noncomputable section

open Filter
open scoped Topology

namespace Soma.Holonics.Millennium.NavierStokesRescalingClock

/-! ## Clock and endpoint -/

/-- The finite physical time selected by the moving-frame parameter `s`. -/
def physicalClock (t₀ B k s : ℝ) : ℝ :=
  t₀ + (B / k) * (1 - Real.exp (-k * s))

/-- The finite physical endpoint of `physicalClock`. -/
def physicalClockEndpoint (t₀ B k : ℝ) : ℝ := t₀ + B / k

/-- The exact positive remaining-time expression associated with the clock. -/
def physicalClockRemaining (B k s : ℝ) : ℝ := (B / k) * Real.exp (-k * s)

theorem physicalClock_hasDerivAt
    {t₀ B k s : ℝ} (hk : 0 < k) :
    HasDerivAt (physicalClock t₀ B k) (B * Real.exp (-k * s)) s := by
  have hinner : HasDerivAt (fun x : ℝ => -k * x) (-k) s :=
    hasDerivAt_const_mul (-k)
  have hexp : HasDerivAt (fun x : ℝ => Real.exp (-k * x))
      ((-k) * Real.exp (-k * s)) s :=
    by
      simpa only [Function.comp_def, mul_comm] using
        (Real.hasDerivAt_exp (-k * s)).comp s hinner
  have hbracket : HasDerivAt (fun x : ℝ => 1 - Real.exp (-k * x))
      (0 - ((-k) * Real.exp (-k * s))) s :=
    (hasDerivAt_const (x := s) (c := (1 : ℝ))).sub hexp
  have hscaled := (hbracket.const_mul (B / k)).const_add t₀
  change HasDerivAt (fun x : ℝ => t₀ + (B / k) * (1 - Real.exp (-k * x)))
    (B * Real.exp (-k * s)) s
  have hderiv : B / k * (0 - ((-k) * Real.exp (-k * s))) =
      B * Real.exp (-k * s) := by
    calc
      B / k * (0 - ((-k) * Real.exp (-k * s))) =
          B / k * (k * Real.exp (-k * s)) := by ring_nf
      _ = B * Real.exp (-k * s) := by
        field_simp [ne_of_gt hk]
  rw [← hderiv]
  exact hscaled

theorem physicalClock_deriv
    {t₀ B k s : ℝ} (hk : 0 < k) :
    deriv (physicalClock t₀ B k) s = B * Real.exp (-k * s) :=
  (physicalClock_hasDerivAt hk).deriv

theorem physicalClock_deriv_pos
    {t₀ B k s : ℝ} (hB : 0 < B) (hk : 0 < k) :
    0 < deriv (physicalClock t₀ B k) s := by
  rw [physicalClock_deriv hk]
  exact mul_pos hB (Real.exp_pos _)

theorem physicalClock_ge_initial
    {t₀ B k s : ℝ} (hB : 0 < B) (hk : 0 < k) (hs : 0 ≤ s) :
    t₀ ≤ physicalClock t₀ B k s := by
  have hks : 0 ≤ k * s := mul_nonneg hk.le hs
  have hexp : Real.exp (-k * s) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  unfold physicalClock
  have hscale : 0 ≤ (B / k) * (1 - Real.exp (-k * s)) := by
    exact mul_nonneg (div_nonneg hB.le hk.le) (sub_nonneg.mpr hexp)
  linarith

theorem physicalClock_gt_initial
    {t₀ B k s : ℝ} (hB : 0 < B) (hk : 0 < k) (hs : 0 < s) :
    t₀ < physicalClock t₀ B k s := by
  have hks : 0 < k * s := mul_pos hk hs
  have hexp : Real.exp (-k * s) < 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  unfold physicalClock
  have hscale : 0 < (B / k) * (1 - Real.exp (-k * s)) := by
    exact mul_pos (div_pos hB hk) (sub_pos.mpr hexp)
  linarith

theorem physicalClock_endpoint_sub_eq_remaining
    {t₀ B k s : ℝ} :
    physicalClockEndpoint t₀ B k - physicalClock t₀ B k s =
      physicalClockRemaining B k s := by
  unfold physicalClockEndpoint physicalClock physicalClockRemaining
  ring_nf

theorem physicalClock_eq_endpoint_sub_remaining
    {t₀ B k s : ℝ} :
    physicalClock t₀ B k s =
      physicalClockEndpoint t₀ B k - physicalClockRemaining B k s := by
  unfold physicalClockEndpoint physicalClock physicalClockRemaining
  ring_nf

theorem physicalClock_remaining_pos
    {B k s : ℝ} (hB : 0 < B) (hk : 0 < k) :
    0 < physicalClockRemaining B k s := by
  unfold physicalClockRemaining
  exact mul_pos (div_pos hB hk) (Real.exp_pos _)

theorem physicalClock_lt_endpoint
    {t₀ B k s : ℝ} (hB : 0 < B) (hk : 0 < k) :
    physicalClock t₀ B k s < physicalClockEndpoint t₀ B k := by
  rw [← sub_pos, physicalClock_endpoint_sub_eq_remaining]
  exact physicalClock_remaining_pos hB hk

theorem physicalClock_mem_Ico
    {t₀ B k s : ℝ} (hB : 0 < B) (hk : 0 < k) (hs : 0 ≤ s) :
    physicalClock t₀ B k s ∈ Set.Ico t₀ (physicalClockEndpoint t₀ B k) :=
  ⟨physicalClock_ge_initial hB hk hs, physicalClock_lt_endpoint hB hk⟩

theorem physicalClock_tendsto_endpoint
    {t₀ B k : ℝ} (hk : 0 < k) :
    Tendsto (physicalClock t₀ B k) atTop (𝓝 (physicalClockEndpoint t₀ B k)) := by
  have hexp : Tendsto (fun s : ℝ => Real.exp (-k * s)) atTop (𝓝 0) := by
    convert (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop hk)) using 1 <;>
      simp only [Function.comp_def, id_eq] <;> ring_nf
  unfold physicalClock physicalClockEndpoint
  convert (tendsto_const_nhds.add
    ((tendsto_const_nhds.sub hexp).const_mul (B / k))) using 1 <;> ring_nf

theorem physicalClock_remaining_tendsto_zero
    {B k : ℝ} (hk : 0 < k) :
    Tendsto (fun s : ℝ => physicalClockRemaining B k s) atTop (𝓝 0) := by
  have hexp : Tendsto (fun s : ℝ => Real.exp (-k * s)) atTop (𝓝 0) := by
    convert (Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop hk)) using 1 <;>
      simp only [Function.comp_def, id_eq] <;> ring_nf
  unfold physicalClockRemaining
  simpa using (hexp.const_mul (B / k))

/-! ## Exponential scale ratio -/

/-- The amplitude/length ratio in the normalized scale chart. -/
def amplitudeLengthRatio (k s : ℝ) : ℝ := Real.exp (k * s)

theorem amplitudeLengthRatio_pos {k s : ℝ} : 0 < amplitudeLengthRatio k s :=
  Real.exp_pos _

theorem amplitudeLengthRatio_tendsto_atTop
    {k : ℝ} (hk : 0 < k) :
    Tendsto (amplitudeLengthRatio k) atTop atTop := by
  unfold amplitudeLengthRatio
  exact Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hk)

/-! ## Finite-endpoint obstruction for a physical receiver -/

/-- A continuous receiver on a state path cannot have its norm diverge along a clock tending to a
finite endpoint.  The state space is deliberately arbitrary: it may include space, time, a moving
centre, scale variables, or any other declared reconstruction coordinates. -/
theorem continuousReceiver_pullback_norm_not_tendsto_atTop
    {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E]
    {xstar : X} {state : ℝ → X} {receiver : X → E}
    (hstate : Tendsto state atTop (𝓝 xstar))
    (hreceiver : ContinuousAt receiver xstar) :
    ¬ Tendsto (fun s => ‖receiver (state s)‖) atTop atTop := by
  intro hnorm
  exact (not_tendsto_atTop_of_tendsto_nhds
    ((hreceiver.tendsto.comp hstate).norm)) hnorm

/-- A continuous receiver path at a finite endpoint cannot have its norm diverge along a clock
tending to that endpoint.  The clock and path are actual inputs, so this is not a certificate
that assumes a singularity or a particular PDE reconstruction. -/
theorem continuousPath_pullback_norm_not_tendsto_atTop
    {E : Type*} [NormedAddCommGroup E]
    {T : ℝ} {clock : ℝ → ℝ} {path : ℝ → E}
    (hclock : Tendsto clock atTop (𝓝 T))
    (hpath : ContinuousAt path T) :
    ¬ Tendsto (fun s => ‖path (clock s)‖) atTop atTop := by
  intro hnorm
  exact (not_tendsto_atTop_of_tendsto_nhds ((hpath.tendsto.comp hclock).norm)) hnorm

/-- If a vanishing real scale leaves a uniformly nonzero scaled receiver along a state path,
continuity of the receiver at the finite endpoint is impossible.  The lower bound is an actual
receiver observation; no blowup or PDE conclusion is encoded by this interface. -/
theorem scaledReceiver_eventually_nonzero_implies_not_continuousAt
    {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {xstar : X} {state : ℝ → X} {q : ℝ → ℝ} {receiver : X → E} {δ : ℝ}
    (hq : Tendsto q atTop (𝓝 0))
    (hstate : Tendsto state atTop (𝓝 xstar))
    (hδ : 0 < δ)
    (hlower : ∀ᶠ s in atTop, δ ≤ ‖q s • receiver (state s)‖) :
    ¬ ContinuousAt receiver xstar := by
  intro hreceiver
  have hpath : Tendsto (fun s => receiver (state s)) atTop (𝓝 (receiver xstar)) :=
    hreceiver.tendsto.comp hstate
  have hscaled : Tendsto (fun s => q s • receiver (state s)) atTop (𝓝 0) :=
    hq.zero_smul hpath
  have hnorm : Tendsto (fun s => ‖q s • receiver (state s)‖) atTop (𝓝 0) :=
    by simpa using hscaled.norm
  have hfalse : ∀ᶠ s : ℝ in atTop, False := by
    filter_upwards [hlower, hnorm.eventually (Iio_mem_nhds hδ)] with s hlarge hsmall
    exact (not_lt_of_ge hlarge) hsmall
  rcases hfalse.exists with ⟨s, hs⟩
  exact hs

#print axioms physicalClock_hasDerivAt
#print axioms physicalClock_ge_initial
#print axioms physicalClock_gt_initial
#print axioms physicalClock_mem_Ico
#print axioms physicalClock_tendsto_endpoint
#print axioms amplitudeLengthRatio_tendsto_atTop
#print axioms continuousReceiver_pullback_norm_not_tendsto_atTop
#print axioms continuousPath_pullback_norm_not_tendsto_atTop
#print axioms scaledReceiver_eventually_nonzero_implies_not_continuousAt

end Soma.Holonics.Millennium.NavierStokesRescalingClock
