import Mathlib
import HolonicsResearch.Fluid.NavierStokesLaminarClass

/-!
# The laminar class with unendingly many modes

`Fluid/NavierStokesLaminarClass` proves the a priori estimate of Lei and Lin for a comb system on
a `Fintype` of modes: the fluid's truncation. The equation itself has a mode at every nonzero
lattice vector. This module proves the same estimate for a countable family of modes, for any
solution in the class, so the statement is about the equation in Fourier variables on the torus
and not only about its truncations.

[from training] Lei and Lin (2011) proved the bound, and existence with it, for the equation on
`ℝ³`. Beale, Kato and Majda (1984): a smooth solution continues for as long as the time integral
of the maximum of its vorticity is finite.

[definition] The two readings of a configuration `a : ι → E` over all modes:

* `critical w a = ∑' k, ‖a k‖ / w k` (`X`, the scale-critical norm);
* `dissipation w a = ∑' k, w k * ‖a k‖` (`Y`, the norm the damping pays in);

with their finite windows `criticalOn S w a` and `dissipationOn S w a` over a `Finset S`. On a
`Fintype` they are the built file's `criticalNorm` and `dissipationNorm`
(`critical_eq_criticalNorm`, `dissipation_eq_dissipationNorm`).

[definition] A **solution in the class** on `[0, T]` (`ClassSolution w ν c T u N`): positive
weights, a positive viscosity, a coherence constant `c ≥ 0`, and

* (law) each mode obeys `d/dt u_k = -(ν * w_k ^ 2) • u_k + N_k`, as a derivative within `[0, T]`
  at every `t` of `[0, T]`;
* (class) at every `t` of `[0, T]` the two series are summable, and `t ↦ X t`, `t ↦ Y t` are
  continuous on `[0, T]`;
* (feed) over every finite window `S`, `∑ k ∈ S, ‖N_k‖ / w_k ≤ c * (X * Y)`.

The feed clause is the summed bound. It follows from the comb's triad bound
`‖N_k‖ ≤ c * w_k * ∑' (p, q) ∈ fibre k, ‖u_p‖ * ‖u_q‖` over pairwise disjoint fibres
(`feed_window_le_of_triads`, `ClassSolution.of_triads`), and it gives the series form
`∑' k, ‖N_k‖ / w_k ≤ c * (X * Y)` (`ClassSolution.summable_feed`, `ClassSolution.tsum_feed_le`).

[proved-derived; formal-checked] The algebra over all modes:

* `summable_norm_of_class`: the amplitudes are summable when both readings are;
* `tsum_norm_sq_le`: `(∑' k, ‖a k‖) ^ 2 ≤ X * Y` (Cauchy-Schwarz, through the finite windows);
* `feed_window_le_of_triads`: the triad bound gives the feed clause, because a pair of modes
  feeds at most one mode.

[proved-derived; formal-checked] The balance, for a solution in the class and
`0 ≤ t₁ ≤ t₂ ≤ T`:

* `ClassSolution.window_balance`: over a finite window `S`,
  `X_S t₂ + ν * ∫ t₁..t₂, Y_S ≤ X_S t₁ + c * ∫ t₁..t₂, X * Y`;
* `ClassSolution.balance`: over all modes (`Countable ι`),
  `X t₂ + ν * ∫ t₁..t₂, Y ≤ X t₁ + c * ∫ t₁..t₂, X * Y`;
* `ClassSolution.frequently_slope_lt`: so the upper right slope of `X` at `x` is at most
  `-(ν - c * X x) * Y x`, the inequality of Lei and Lin without a derivative of `X`.

[proved-derived; formal-checked] **The laminar class is kept.** If `c * X 0 < ν` then for every
`t` of `[0, T]`:

* `ClassSolution.critical_le_initial`: `X t ≤ X 0`;
* `ClassSolution.dissipation_integral_le_drop`: `(ν - c * X 0) * ∫ 0..t, Y ≤ X 0 - X t`;
* `ClassSolution.integral_dissipation_le`: `∫ 0..t, Y ≤ X 0 / (ν - c * X 0)`, a bound in which
  the horizon `T` does not appear.

[proved-derived; formal-checked] The continuation form, with no smallness:

* `ClassSolution.critical_le_mul_exp`: `X t ≤ X 0 * exp (c * ∫ 0..t, Y)`;
* `ClassSolution.critical_le_of_integral_le`: so `∫ 0..t, Y ≤ M` gives `X t ≤ X 0 * exp (c * M)`.

[interpretation] For the fluid `Y = ∑ |k| |û_k|` bounds the maximum of the gradient,
`‖∇u‖_∞ ≤ ∑ |k| |û_k|`, hence of the vorticity. Its time integral is the quantity of Beale, Kato
and Majda's criterion (the tree's rows `ns.bkm-*`). `ClassSolution.integral_dissipation_le` says
that a smooth solution below Reynolds one keeps the budget that criterion asks for, with a bound
fixed by the opening state, for as long as it exists.

[proved-derived; formal-checked] The joins.

* `ClassSolution.of_combSystem`: a comb system on a `Fintype` (the built file's object) is a
  solution in the class on every `[0, T]`, so the hypotheses here are met by every truncation.
* The Fourier instance (`fibre`, `feedAll`, `norm_feedAll_le`, `FourierSolution`,
  `FourierSolution.classSolution`): modes with injective nonzero wave vectors `κ k`, weights
  `‖κ k‖`, incompressible amplitudes, and the feed
  `N_k = -i P_k ∑' (p, q) : κ p + κ q = κ k, (κ q · a_p) a_q` with `‖P_k‖ ≤ 1`, summed over all
  triads. The triad bound holds with `c = 1`, so a solution of this law in the class is a
  `ClassSolution` with `c = 1`. With `X 0 < ν` it keeps `X t ≤ X 0`
  (`FourierSolution.critical_le_initial`), `(ν - X 0) * ∫ 0..t, Y ≤ X 0 - X t`
  (`FourierSolution.dissipation_integral_le_drop`) and the gradient's budget
  `∫ 0..t, Y ≤ X 0 / (ν - X 0)` (`FourierSolution.integral_dissipation_le`); with no smallness,
  `X t ≤ X 0 * exp (∫ 0..t, Y)` (`FourierSolution.critical_le_mul_exp`).
* The torus (`LatticeMode`, `latticeWave`, `latticeWave_injective`, `latticeWave_ne_zero`,
  `torus_critical_le_initial`, `torus_integral_dissipation_le`): the nonzero integer vectors of
  `n → ℤ` are one such family of modes, each its own wave vector, so the two statements hold for
  the law on all of them.

Complex amplitudes read their real structure (`ClassSolution.critical_le_initial_complex`,
`ClassSolution.dissipation_integral_le_drop_complex`,
`ClassSolution.integral_dissipation_le_complex`, `ClassSolution.critical_le_mul_exp_complex`).

## What this does not state

Nothing here is the Clay statement. The module constructs no solution: a solution in the class is
a hypothesis, and so are the continuity of `X` and `Y` in time and the summability of the two
series (a smooth solution on the torus has them; that is not proved here). It takes no limit of
truncations. It says nothing at or above the threshold `c * X 0 = ν`, where the count's bound
does not decide. The reading of `Y` as a bound on the gradient's maximum, and the criterion of
Beale, Kato and Majda, are cited and not formalized. The Fourier instance takes the family of
wave vectors, the projections and the incompressibility at every time as hypotheses; it does not
build the torus, the Fourier transform of a field, or Leray's projection on all modes.
-/

noncomputable section

namespace Holonics.Fluid.LaminarAllModes

open Set Filter Topology MeasureTheory
open scoped RealInnerProductSpace
open Holonics.Fluid.LaminarClass

/-! ## The two readings over all modes -/

section Readings

variable {ι : Type*} {E : Type*} [NormedAddCommGroup E]

/-- [definition] The scale-critical norm over all modes, `X = ∑' k, ‖a k‖ / w k`. -/
def critical (w : ι → ℝ) (a : ι → E) : ℝ := ∑' k, ‖a k‖ / w k

/-- [definition] The norm the damping pays in, over all modes, `Y = ∑' k, w k * ‖a k‖`. -/
def dissipation (w : ι → ℝ) (a : ι → E) : ℝ := ∑' k, w k * ‖a k‖

/-- [definition] The critical norm's finite window. -/
def criticalOn (S : Finset ι) (w : ι → ℝ) (a : ι → E) : ℝ := ∑ k ∈ S, ‖a k‖ / w k

/-- [definition] The dissipation norm's finite window. -/
def dissipationOn (S : Finset ι) (w : ι → ℝ) (a : ι → E) : ℝ := ∑ k ∈ S, w k * ‖a k‖

theorem critical_nonneg {w : ι → ℝ} (hw : ∀ k, 0 ≤ w k) (a : ι → E) : 0 ≤ critical w a :=
  tsum_nonneg fun k => div_nonneg (norm_nonneg _) (hw k)

theorem dissipation_nonneg {w : ι → ℝ} (hw : ∀ k, 0 ≤ w k) (a : ι → E) :
    0 ≤ dissipation w a :=
  tsum_nonneg fun k => mul_nonneg (hw k) (norm_nonneg _)

theorem criticalOn_nonneg {w : ι → ℝ} (hw : ∀ k, 0 ≤ w k) (S : Finset ι) (a : ι → E) :
    0 ≤ criticalOn S w a :=
  Finset.sum_nonneg fun k _ => div_nonneg (norm_nonneg _) (hw k)

theorem dissipationOn_nonneg {w : ι → ℝ} (hw : ∀ k, 0 ≤ w k) (S : Finset ι) (a : ι → E) :
    0 ≤ dissipationOn S w a :=
  Finset.sum_nonneg fun k _ => mul_nonneg (hw k) (norm_nonneg _)

theorem criticalOn_le_critical {w : ι → ℝ} (hw : ∀ k, 0 ≤ w k) {a : ι → E}
    (hX : Summable fun k => ‖a k‖ / w k) (S : Finset ι) :
    criticalOn S w a ≤ critical w a :=
  hX.sum_le_tsum S fun k _ => div_nonneg (norm_nonneg _) (hw k)

theorem dissipationOn_le_dissipation {w : ι → ℝ} (hw : ∀ k, 0 ≤ w k) {a : ι → E}
    (hY : Summable fun k => w k * ‖a k‖) (S : Finset ι) :
    dissipationOn S w a ≤ dissipation w a :=
  hY.sum_le_tsum S fun k _ => mul_nonneg (hw k) (norm_nonneg _)

/-- A summable real family's finite sums tend to its sum along the finite sets. -/
theorem tendsto_finset_sum {f : ι → ℝ} (hf : Summable f) :
    Tendsto (fun S : Finset ι => ∑ k ∈ S, f k) atTop (𝓝 (∑' k, f k)) :=
  hf.hasSum

/-- On a `Fintype` the reading over all modes is the built file's `criticalNorm`. -/
theorem critical_eq_criticalNorm [Fintype ι] (w : ι → ℝ) (a : ι → E) :
    critical w a = criticalNorm w a :=
  tsum_fintype _

/-- On a `Fintype` the reading over all modes is the built file's `dissipationNorm`. -/
theorem dissipation_eq_dissipationNorm [Fintype ι] (w : ι → ℝ) (a : ι → E) :
    dissipation w a = dissipationNorm w a :=
  tsum_fintype _

/-- [proved-derived; formal-checked] In the class the amplitudes themselves are summable:
`‖a k‖ ≤ ‖a k‖ / w k + w k * ‖a k‖`, whichever side of one the weight is. -/
theorem summable_norm_of_class {w : ι → ℝ} (hw : ∀ k, 0 < w k) {a : ι → E}
    (hX : Summable fun k => ‖a k‖ / w k) (hY : Summable fun k => w k * ‖a k‖) :
    Summable fun k => ‖a k‖ := by
  refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_) (hX.add hY)
  have hwk := hw k
  have hn := norm_nonneg (a k)
  rcases le_total (w k) 1 with h1 | h1
  · have h2 : ‖a k‖ ≤ ‖a k‖ / w k := by
      rw [le_div_iff₀ hwk]
      nlinarith
    have h3 : 0 ≤ w k * ‖a k‖ := mul_nonneg hwk.le hn
    linarith
  · have h2 : ‖a k‖ ≤ w k * ‖a k‖ := by nlinarith
    have h3 : 0 ≤ ‖a k‖ / w k := div_nonneg hn hwk.le
    linarith

/-- [proved-derived; formal-checked] Cauchy-Schwarz between the two readings, over all modes:
`(∑' ‖a k‖) ^ 2 ≤ X * Y`. -/
theorem tsum_norm_sq_le {w : ι → ℝ} (hw : ∀ k, 0 < w k) {a : ι → E}
    (hX : Summable fun k => ‖a k‖ / w k) (hY : Summable fun k => w k * ‖a k‖) :
    (∑' k, ‖a k‖) ^ 2 ≤ critical w a * dissipation w a := by
  have hw' : ∀ k, 0 ≤ w k := fun k => (hw k).le
  have hA := summable_norm_of_class hw hX hY
  have hlim : Tendsto (fun S : Finset ι => (∑ k ∈ S, ‖a k‖) ^ 2) atTop
      (𝓝 ((∑' k, ‖a k‖) ^ 2)) := (tendsto_finset_sum hA).pow 2
  refine le_of_tendsto' hlim fun S => ?_
  calc (∑ k ∈ S, ‖a k‖) ^ 2 ≤ (∑ k ∈ S, ‖a k‖ / w k) * ∑ k ∈ S, w k * ‖a k‖ := by
        refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul S
          (fun k _ => div_nonneg (norm_nonneg _) (hw' k))
          (fun k _ => mul_nonneg (hw' k) (norm_nonneg _)) (fun k _ => le_of_eq ?_)
        rw [← mul_assoc, div_mul_cancel₀ _ (hw k).ne', sq]
    _ ≤ critical w a * dissipation w a :=
        mul_le_mul (criticalOn_le_critical hw' hX S) (dissipationOn_le_dissipation hw' hY S)
          (dissipationOn_nonneg hw' S a) (critical_nonneg hw' a)

/-- [proved-derived; formal-checked] **The feed sum, all modes.** The comb's triad bound over
pairwise disjoint fibres gives the summed bound on every finite window:
`∑ k ∈ S, ‖n k‖ / w k ≤ c * (X * Y)`. -/
theorem feed_window_le_of_triads {w : ι → ℝ} (hw : ∀ k, 0 < w k) {c : ℝ} (hc : 0 ≤ c)
    {fibre : ι → Set (ι × ι)} (hfib : ∀ k k', k ≠ k' → Disjoint (fibre k) (fibre k'))
    {a n : ι → E} (hX : Summable fun k => ‖a k‖ / w k) (hY : Summable fun k => w k * ‖a k‖)
    (hn : ∀ k, ‖n k‖ ≤ c * w k * ∑' pq : fibre k, ‖a pq.1.1‖ * ‖a pq.1.2‖) (S : Finset ι) :
    ∑ k ∈ S, ‖n k‖ / w k ≤ c * (critical w a * dissipation w a) := by
  classical
  have hA := summable_norm_of_class hw hX hY
  have hprod : Summable fun pq : ι × ι => ‖a pq.1‖ * ‖a pq.2‖ :=
    hA.mul_of_nonneg hA (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  have hunion : ∑' pq : (⋃ k ∈ S, fibre k : Set (ι × ι)), ‖a pq.1.1‖ * ‖a pq.1.2‖
      = ∑ k ∈ S, ∑' pq : fibre k, ‖a pq.1.1‖ * ‖a pq.1.2‖ :=
    Summable.tsum_finset_bUnion_disjoint (f := fun pq : ι × ι => ‖a pq.1‖ * ‖a pq.2‖)
      (fun k _ k' _ hkk' => hfib k k' hkk') (fun k _ => hprod.subtype _)
  calc ∑ k ∈ S, ‖n k‖ / w k ≤ ∑ k ∈ S, c * ∑' pq : fibre k, ‖a pq.1.1‖ * ‖a pq.1.2‖ := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [div_le_iff₀ (hw k)]
        calc ‖n k‖ ≤ c * w k * ∑' pq : fibre k, ‖a pq.1.1‖ * ‖a pq.1.2‖ := hn k
          _ = c * (∑' pq : fibre k, ‖a pq.1.1‖ * ‖a pq.1.2‖) * w k := by ring
    _ = c * ∑' pq : (⋃ k ∈ S, fibre k : Set (ι × ι)), ‖a pq.1.1‖ * ‖a pq.1.2‖ := by
        rw [← Finset.mul_sum, hunion]
    _ ≤ c * ∑' pq : ι × ι, ‖a pq.1‖ * ‖a pq.2‖ :=
        mul_le_mul_of_nonneg_left
          (Summable.tsum_subtype_le (fun pq : ι × ι => ‖a pq.1‖ * ‖a pq.2‖) _
            (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)) hprod) hc
    _ = c * (∑' k, ‖a k‖) ^ 2 := by
        rw [sq, hA.tsum_mul_tsum hA hprod]
    _ ≤ c * (critical w a * dissipation w a) :=
        mul_le_mul_of_nonneg_left (tsum_norm_sq_le hw hX hY) hc

end Readings

/-! ## Calculus on `[0, T]` -/

section Calculus

theorem intervalIntegrable_of_continuousOn {g : ℝ → ℝ} {T a b : ℝ}
    (hg : ContinuousOn g (Icc 0 T)) (ha : a ∈ Icc (0 : ℝ) T) (hb : b ∈ Icc (0 : ℝ) T) :
    IntervalIntegrable g volume a b :=
  (hg.mono (uIcc_subset_Icc ha hb)).intervalIntegrable

/-- The primitive of a function continuous on `[0, T]` has that function as its right
derivative at every point of `[0, T)`. -/
theorem hasDerivWithinAt_primitive {g : ℝ → ℝ} {T a x : ℝ} (hg : ContinuousOn g (Icc 0 T))
    (ha : a ∈ Icc (0 : ℝ) T) (hx : x ∈ Ico (0 : ℝ) T) :
    HasDerivWithinAt (fun s => ∫ r in a..s, g r) (g x) (Ici x) x := by
  have hxI : x ∈ Icc (0 : ℝ) T := ⟨hx.1, hx.2.le⟩
  refine intervalIntegral.integral_hasDerivWithinAt_right
    (intervalIntegrable_of_continuousOn hg ha hxI) (s := Ici x) (t := Ioi x) ?_ ?_
  · exact (hg.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc x).filter_mono
      (nhdsWithin_le_iff.mpr (Icc_mem_nhdsGT_of_mem hx))
  · exact (hg x hxI).mono_of_mem_nhdsWithin (Icc_mem_nhdsGT_of_mem hx)

theorem continuousOn_primitive {g : ℝ → ℝ} {T a b : ℝ} (hg : ContinuousOn g (Icc 0 T))
    (ha : a ∈ Icc (0 : ℝ) T) (hb : b ∈ Icc (0 : ℝ) T) (hab : a ≤ b) :
    ContinuousOn (fun s => ∫ r in a..s, g r) (Icc a b) := by
  have hI : IntegrableOn g (uIcc a b) volume := by
    rw [uIcc_of_le hab]
    exact (hg.mono (Icc_subset_Icc ha.1 hb.2)).integrableOn_Icc
  have := intervalIntegral.continuousOn_primitive_interval hI
  rwa [uIcc_of_le hab] at this

theorem integral_le_mul_sub {g : ℝ → ℝ} {T a b r : ℝ} (hg : ContinuousOn g (Icc 0 T))
    (ha : a ∈ Icc (0 : ℝ) T) (hb : b ∈ Icc (0 : ℝ) T) (hab : a ≤ b)
    (hr : ∀ s ∈ Icc a b, g s ≤ r) : ∫ s in a..b, g s ≤ r * (b - a) := by
  have h1 := intervalIntegral.integral_mono_on hab
    (intervalIntegrable_of_continuousOn hg ha hb) (intervalIntegrable_const (c := r)) hr
  rw [intervalIntegral.integral_const, smul_eq_mul] at h1
  linarith [mul_comm r (b - a)]

end Calculus

/-! ## A solution in the class -/

section Class

variable {ι : Type*} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- [definition] A solution in the class on `[0, T]`: positive weights, a positive viscosity, a
coherence constant `c ≥ 0`, each mode damped at `ν * w k ^ 2` and fed by `N` on `[0, T]`, the
two readings summable at every time and continuous in time, and the feed bounded by
`c * (X * Y)` on every finite window. -/
structure ClassSolution (w : ι → ℝ) (ν c T : ℝ) (u N : ℝ → ι → E) : Prop where
  weight_pos : ∀ k, 0 < w k
  viscosity_pos : 0 < ν
  coherence_nonneg : 0 ≤ c
  evolves : ∀ k, ∀ t ∈ Icc (0 : ℝ) T,
    HasDerivWithinAt (fun s => u s k) (-(ν * w k ^ 2) • u t k + N t k) (Icc 0 T) t
  summable_critical : ∀ t ∈ Icc (0 : ℝ) T, Summable fun k => ‖u t k‖ / w k
  summable_dissipation : ∀ t ∈ Icc (0 : ℝ) T, Summable fun k => w k * ‖u t k‖
  continuousOn_critical : ContinuousOn (fun t => critical w (u t)) (Icc 0 T)
  continuousOn_dissipation : ContinuousOn (fun t => dissipation w (u t)) (Icc 0 T)
  feed_le : ∀ t ∈ Icc (0 : ℝ) T, ∀ S : Finset ι,
    ∑ k ∈ S, ‖N t k‖ / w k ≤ c * (critical w (u t) * dissipation w (u t))

variable {w : ι → ℝ} {ν c T : ℝ} {u N : ℝ → ι → E}

/-- [proved-derived; formal-checked] A solution in the class from the comb's triad bound over
pairwise disjoint fibres. -/
theorem ClassSolution.of_triads (hw : ∀ k, 0 < w k) (hν : 0 < ν) (hc : 0 ≤ c)
    (hu : ∀ k, ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt (fun s => u s k) (-(ν * w k ^ 2) • u t k + N t k) (Icc 0 T) t)
    (hX : ∀ t ∈ Icc (0 : ℝ) T, Summable fun k => ‖u t k‖ / w k)
    (hY : ∀ t ∈ Icc (0 : ℝ) T, Summable fun k => w k * ‖u t k‖)
    (hXc : ContinuousOn (fun t => critical w (u t)) (Icc 0 T))
    (hYc : ContinuousOn (fun t => dissipation w (u t)) (Icc 0 T))
    {fibre : ι → Set (ι × ι)} (hfib : ∀ k k', k ≠ k' → Disjoint (fibre k) (fibre k'))
    (hN : ∀ t ∈ Icc (0 : ℝ) T, ∀ k,
      ‖N t k‖ ≤ c * w k * ∑' pq : fibre k, ‖u t pq.1.1‖ * ‖u t pq.1.2‖) :
    ClassSolution w ν c T u N :=
  ⟨hw, hν, hc, hu, hX, hY, hXc, hYc,
    fun t ht S => feed_window_le_of_triads hw hc hfib (hX t ht) (hY t ht) (hN t ht) S⟩

/-- [proved-derived; formal-checked] The feed is summable in the critical norm. -/
theorem ClassSolution.summable_feed (h : ClassSolution w ν c T u N) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) : Summable fun k => ‖N t k‖ / w k :=
  summable_of_sum_le (fun k => div_nonneg (norm_nonneg _) (h.weight_pos k).le) (h.feed_le t ht)

/-- [proved-derived; formal-checked] **The feed sum, all modes**:
`∑' k, ‖N k‖ / w k ≤ c * (X * Y)`. -/
theorem ClassSolution.tsum_feed_le (h : ClassSolution w ν c T u N) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) :
    ∑' k, ‖N t k‖ / w k ≤ c * (critical w (u t) * dissipation w (u t)) :=
  Real.tsum_le_of_sum_le (fun k => div_nonneg (norm_nonneg _) (h.weight_pos k).le)
    (h.feed_le t ht)

theorem ClassSolution.continuousOn_mode (h : ClassSolution w ν c T u N) (k : ι) :
    ContinuousOn (fun s => u s k) (Icc 0 T) :=
  fun t ht => (h.evolves k t ht).continuousWithinAt

theorem ClassSolution.continuousOn_criticalOn (h : ClassSolution w ν c T u N) (S : Finset ι) :
    ContinuousOn (fun s => criticalOn S w (u s)) (Icc 0 T) := by
  unfold criticalOn
  exact continuousOn_finsetSum _ fun k _ => (h.continuousOn_mode k).norm.div_const _

theorem ClassSolution.continuousOn_dissipationOn (h : ClassSolution w ν c T u N)
    (S : Finset ι) : ContinuousOn (fun s => dissipationOn S w (u s)) (Icc 0 T) := by
  unfold dissipationOn
  exact continuousOn_finsetSum _ fun k _ => continuousOn_const.mul (h.continuousOn_mode k).norm

theorem ClassSolution.continuousOn_product (h : ClassSolution w ν c T u N) :
    ContinuousOn (fun s => critical w (u s) * dissipation w (u s)) (Icc 0 T) :=
  h.continuousOn_critical.mul h.continuousOn_dissipation

end Class

/-! ## The balance -/

section Main

variable {ι : Type*} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {w : ι → ℝ} {ν c T : ℝ} {u N : ℝ → ι → E}

/-- [definition] The right derivative of a finite window of the critical norm. -/
def slopeOn (S : Finset ι) (w : ι → ℝ) (ν : ℝ) (u N : ℝ → ι → E) (t : ℝ) : ℝ :=
  ∑ k ∈ S, normSlope (u t k) (-(ν * w k ^ 2) • u t k + N t k) / w k

theorem ClassSolution.hasDerivWithinAt_criticalOn (h : ClassSolution w ν c T u N)
    (S : Finset ι) {x : ℝ} (hx : x ∈ Ico (0 : ℝ) T) :
    HasDerivWithinAt (fun s => criticalOn S w (u s)) (slopeOn S w ν u N x) (Ici x) x := by
  unfold criticalOn slopeOn
  refine HasDerivWithinAt.fun_sum fun k _ => ?_
  exact (hasDerivWithinAt_norm_Ici
    ((h.evolves k x ⟨hx.1, hx.2.le⟩).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem hx))).div_const _

/-- [proved-derived; formal-checked] A window's slope: at most `-ν * Y_S + c * (X * Y)`. The
damping is the window's own, the feed is bounded through all modes. -/
theorem ClassSolution.slopeOn_le (h : ClassSolution w ν c T u N) (S : Finset ι) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) :
    slopeOn S w ν u N t ≤
      -(ν * dissipationOn S w (u t)) + c * (critical w (u t) * dissipation w (u t)) := by
  have hw := h.weight_pos
  have h1 : slopeOn S w ν u N t ≤
      ∑ k ∈ S, (-(ν * (w k * ‖u t k‖)) + ‖N t k‖ / w k) := by
    unfold slopeOn
    refine Finset.sum_le_sum fun k _ => ?_
    rw [div_le_iff₀ (hw k)]
    calc normSlope (u t k) (-(ν * w k ^ 2) • u t k + N t k)
        ≤ -(ν * w k ^ 2) * ‖u t k‖ + ‖N t k‖ := normSlope_damped_le _ _ _
      _ = (-(ν * (w k * ‖u t k‖)) + ‖N t k‖ / w k) * w k := by
          rw [add_mul, div_mul_cancel₀ _ (hw k).ne']
          ring
  have h2 : ∑ k ∈ S, (-(ν * (w k * ‖u t k‖)) + ‖N t k‖ / w k)
      = -(ν * dissipationOn S w (u t)) + ∑ k ∈ S, ‖N t k‖ / w k := by
    unfold dissipationOn
    rw [Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.mul_sum]
  have h3 := h.feed_le t ht S
  rw [h2] at h1
  linarith

/-- [proved-derived; formal-checked] **The balance on a finite window.** For `0 ≤ t₁ ≤ t₂ ≤ T`:
`X_S t₂ + ν * ∫ t₁..t₂, Y_S ≤ X_S t₁ + c * ∫ t₁..t₂, X * Y`. -/
theorem ClassSolution.window_balance (h : ClassSolution w ν c T u N) (S : Finset ι)
    {t₁ t₂ : ℝ} (h0 : 0 ≤ t₁) (h12 : t₁ ≤ t₂) (hT : t₂ ≤ T) :
    criticalOn S w (u t₂) + ν * ∫ s in t₁..t₂, dissipationOn S w (u s)
      ≤ criticalOn S w (u t₁)
        + c * ∫ s in t₁..t₂, critical w (u s) * dissipation w (u s) := by
  have ht₁ : t₁ ∈ Icc (0 : ℝ) T := ⟨h0, h12.trans hT⟩
  have ht₂ : t₂ ∈ Icc (0 : ℝ) T := ⟨h0.trans h12, hT⟩
  have hsub : Icc t₁ t₂ ⊆ Icc 0 T := Icc_subset_Icc h0 hT
  obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ, g = fun s =>
      ν * dissipationOn S w (u s) - c * (critical w (u s) * dissipation w (u s)) := ⟨_, rfl⟩
  have hgc : ContinuousOn g (Icc 0 T) := by
    rw [hg]
    exact (continuousOn_const.mul (h.continuousOn_dissipationOn S)).sub
      (continuousOn_const.mul h.continuousOn_product)
  have key := image_le_of_deriv_right_le_deriv_boundary
    (f := fun s => criticalOn S w (u s) + ∫ r in t₁..s, g r)
    (f' := fun x => slopeOn S w ν u N x + g x)
    (a := t₁) (b := t₂)
    (B := fun _ => criticalOn S w (u t₁)) (B' := fun _ => 0)
    (((h.continuousOn_criticalOn S).mono hsub).add (continuousOn_primitive hgc ht₁ ht₂ h12))
    (fun x hx => (h.hasDerivWithinAt_criticalOn S ⟨h0.trans hx.1, hx.2.trans_le hT⟩).add
      (hasDerivWithinAt_primitive hgc ht₁ ⟨h0.trans hx.1, hx.2.trans_le hT⟩))
    (by simp)
    continuousOn_const
    (fun x _ => hasDerivWithinAt_const _ _ _)
    (by
      intro x hx
      have hs := h.slopeOn_le S (hsub ⟨hx.1, hx.2.le⟩)
      show slopeOn S w ν u N x + g x ≤ 0
      rw [hg]
      linarith)
  have hfin : criticalOn S w (u t₂) + ∫ r in t₁..t₂, g r ≤ criticalOn S w (u t₁) :=
    key (right_mem_Icc.mpr h12)
  have hYS : IntervalIntegrable (fun s => dissipationOn S w (u s)) volume t₁ t₂ :=
    intervalIntegrable_of_continuousOn (h.continuousOn_dissipationOn S) ht₁ ht₂
  have hXY : IntervalIntegrable (fun s => critical w (u s) * dissipation w (u s)) volume t₁ t₂ :=
    intervalIntegrable_of_continuousOn h.continuousOn_product ht₁ ht₂
  have hsplit : ∫ r in t₁..t₂, g r = ν * (∫ s in t₁..t₂, dissipationOn S w (u s))
      - c * ∫ s in t₁..t₂, critical w (u s) * dissipation w (u s) := by
    rw [hg, intervalIntegral.integral_sub (hYS.const_mul ν) (hXY.const_mul c),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rw [hsplit] at hfin
  linarith

/-- [proved-derived; formal-checked] **The balance over all modes.** For `0 ≤ t₁ ≤ t₂ ≤ T`:
`X t₂ + ν * ∫ t₁..t₂, Y ≤ X t₁ + c * ∫ t₁..t₂, X * Y`. The windows pass to the whole family by
dominated convergence, the dominating series being `Y` itself. -/
theorem ClassSolution.balance [Countable ι] (h : ClassSolution w ν c T u N) {t₁ t₂ : ℝ}
    (h0 : 0 ≤ t₁) (h12 : t₁ ≤ t₂) (hT : t₂ ≤ T) :
    critical w (u t₂) + ν * ∫ s in t₁..t₂, dissipation w (u s)
      ≤ critical w (u t₁)
        + c * ∫ s in t₁..t₂, critical w (u s) * dissipation w (u s) := by
  have ht₁ : t₁ ∈ Icc (0 : ℝ) T := ⟨h0, h12.trans hT⟩
  have ht₂ : t₂ ∈ Icc (0 : ℝ) T := ⟨h0.trans h12, hT⟩
  have hw : ∀ k, 0 ≤ w k := fun k => (h.weight_pos k).le
  have hsub : Icc t₁ t₂ ⊆ Icc 0 T := Icc_subset_Icc h0 hT
  have hmem : ∀ s, s ∈ uIoc t₁ t₂ → s ∈ Icc (0 : ℝ) T := by
    intro s hs
    rw [uIoc_of_le h12] at hs
    exact ⟨h0.trans hs.1.le, hs.2.trans hT⟩
  have hX : Tendsto (fun S : Finset ι => criticalOn S w (u t₂)) atTop
      (𝓝 (critical w (u t₂))) := tendsto_finset_sum (h.summable_critical t₂ ht₂)
  have hY : HasSum (fun k => ∫ s in t₁..t₂, w k * ‖u s k‖)
      (∫ s in t₁..t₂, dissipation w (u s)) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun k s => w k * ‖u s k‖) ?_ ?_ ?_ ?_ ?_
    · intro k
      have hc : ContinuousOn (fun s => w k * ‖u s k‖) (Icc t₁ t₂) :=
        (continuousOn_const.mul (h.continuousOn_mode k).norm).mono hsub
      have hm := hc.aestronglyMeasurable (μ := volume) measurableSet_Icc
      rw [uIoc_of_le h12]
      exact hm.mono_measure (Measure.restrict_mono Ioc_subset_Icc_self le_rfl)
    · intro k
      exact Eventually.of_forall fun s _ => by
        rw [Real.norm_of_nonneg (mul_nonneg (hw k) (norm_nonneg _))]
    · exact Eventually.of_forall fun s hs => h.summable_dissipation s (hmem s hs)
    · exact intervalIntegrable_of_continuousOn h.continuousOn_dissipation ht₁ ht₂
    · exact Eventually.of_forall fun s hs => (h.summable_dissipation s (hmem s hs)).hasSum
  have hYt : Tendsto (fun S : Finset ι => ∫ s in t₁..t₂, dissipationOn S w (u s)) atTop
      (𝓝 (∫ s in t₁..t₂, dissipation w (u s))) := by
    have heq : (fun S : Finset ι => ∫ s in t₁..t₂, dissipationOn S w (u s))
        = fun S => ∑ k ∈ S, ∫ s in t₁..t₂, w k * ‖u s k‖ := by
      funext S
      unfold dissipationOn
      exact intervalIntegral.integral_finsetSum fun k _ =>
        intervalIntegrable_of_continuousOn
          (continuousOn_const.mul (h.continuousOn_mode k).norm) ht₁ ht₂
    rw [heq]
    exact hY
  refine le_of_tendsto' (hX.add (hYt.const_mul ν)) fun S => ?_
  have h1 := h.window_balance S h0 h12 hT
  have h2 := criticalOn_le_critical hw (h.summable_critical t₁ ht₁) S
  linarith

/-- [proved-derived; formal-checked] The inequality of Lei and Lin over all modes, without a
derivative of `X`: the upper right slope of `X` at `x` is at most `-(ν - c * X x) * Y x`. -/
theorem ClassSolution.frequently_slope_lt [Countable ι] (h : ClassSolution w ν c T u N)
    {x : ℝ} (hx : x ∈ Ico (0 : ℝ) T) {r : ℝ}
    (hr : -(ν - c * critical w (u x)) * dissipation w (u x) < r) :
    ∃ᶠ z in 𝓝[>] x, slope (fun s => critical w (u s)) x z < r := by
  have hxI : x ∈ Icc (0 : ℝ) T := ⟨hx.1, hx.2.le⟩
  obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ, g = fun s =>
      -(ν - c * critical w (u s)) * dissipation w (u s) := ⟨_, rfl⟩
  have hgc : ContinuousOn g (Icc 0 T) := by
    rw [hg]
    exact ((continuousOn_const.sub (continuousOn_const.mul h.continuousOn_critical)).neg).mul
      h.continuousOn_dissipation
  obtain ⟨r', hr1, hr2⟩ := exists_between hr
  have hgx : g x < r' := by rw [hg]; exact hr1
  have hnear : ∀ᶠ s in 𝓝[Icc 0 T] x, g s < r' := (hgc x hxI).eventually (Iio_mem_nhds hgx)
  have hnear' : {s | g s < r'} ∈ 𝓝[>] x :=
    nhdsWithin_le_iff.mpr (Icc_mem_nhdsGT_of_mem hx) hnear
  obtain ⟨b, hb, hbsub⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp hnear'
  have hev : ∀ᶠ z in 𝓝[>] x, slope (fun s => critical w (u s)) x z < r := by
    filter_upwards [Ioo_mem_nhdsGT (lt_min hb hx.2)] with z hz
    have hxz : x < z := hz.1
    have hzb : z < b := hz.2.trans_le (min_le_left _ _)
    have hzT : z < T := hz.2.trans_le (min_le_right _ _)
    have hzI : z ∈ Icc (0 : ℝ) T := ⟨hx.1.trans hxz.le, hzT.le⟩
    have hbal := h.balance hx.1 hxz.le hzT.le
    have hYint := intervalIntegrable_of_continuousOn h.continuousOn_dissipation hxI hzI
    have hXYint := intervalIntegrable_of_continuousOn h.continuousOn_product hxI hzI
    have hgint : ∫ s in x..z, g s = c * (∫ s in x..z, critical w (u s) * dissipation w (u s))
        - ν * ∫ s in x..z, dissipation w (u s) := by
      have h1 : ∫ s in x..z, g s = ∫ s in x..z,
          (c * (critical w (u s) * dissipation w (u s)) - ν * dissipation w (u s)) := by
        refine intervalIntegral.integral_congr fun s _ => ?_
        simp only [hg]
        ring
      rw [h1, intervalIntegral.integral_sub (hXYint.const_mul c) (hYint.const_mul ν),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    have hle : ∫ s in x..z, g s ≤ r' * (z - x) := by
      refine integral_le_mul_sub hgc hxI hzI hxz.le fun s hs => ?_
      rcases eq_or_lt_of_le hs.1 with hsx | hsx
      · rw [← hsx]; exact hgx.le
      · exact (hbsub ⟨hsx, hs.2.trans hzb.le⟩ : g s < r').le
    have hpos : 0 < z - x := sub_pos.mpr hxz
    rw [slope_def_field, div_lt_iff₀ hpos]
    have h3 : r' * (z - x) < r * (z - x) := mul_lt_mul_of_pos_right hr2 hpos
    linarith
  exact hev.frequently

/-- [proved-derived; formal-checked] **The laminar class is kept, over all modes.** If
`c * X 0 < ν` then the critical norm never passes its opening value on `[0, T]`. -/
theorem ClassSolution.critical_le_initial [Countable ι] (h : ClassSolution w ν c T u N)
    (h0 : c * critical w (u 0) < ν) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    critical w (u t) ≤ critical w (u 0) := by
  have hc := h.coherence_nonneg
  have hd : 0 < ν - c * critical w (u 0) := sub_pos.mpr h0
  have ht0 : 0 ≤ t := ht.1
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  -- a fence of slope `ε`, low enough to stay inside the class up to the time `t`
  obtain ⟨ε, hε, hεδ, hεd⟩ : ∃ ε : ℝ, 0 < ε ∧ ε * t ≤ δ ∧
      c * (ε * t) ≤ ν - c * critical w (u 0) := by
    have hc1 : 0 < c + 1 := by linarith
    have ht1 : 0 < t + 1 := by linarith
    have hm_pos : 0 < min δ ((ν - c * critical w (u 0)) / (c + 1)) :=
      lt_min hδ (div_pos hd hc1)
    have hmδ : min δ ((ν - c * critical w (u 0)) / (c + 1)) ≤ δ := min_le_left _ _
    have hmd : min δ ((ν - c * critical w (u 0)) / (c + 1))
        ≤ (ν - c * critical w (u 0)) / (c + 1) := min_le_right _ _
    generalize min δ ((ν - c * critical w (u 0)) / (c + 1)) = m at hm_pos hmδ hmd
    have hmt : m / (t + 1) * t ≤ m := by
      rw [div_mul_eq_mul_div, div_le_iff₀ ht1]
      nlinarith
    have hcd : c * ((ν - c * critical w (u 0)) / (c + 1))
        ≤ ν - c * critical w (u 0) := by
      rw [mul_div_assoc', div_le_iff₀ hc1]
      nlinarith
    refine ⟨m / (t + 1), div_pos hm_pos ht1, hmt.trans hmδ, ?_⟩
    calc c * (m / (t + 1) * t) ≤ c * m := mul_le_mul_of_nonneg_left hmt hc
      _ ≤ c * ((ν - c * critical w (u 0)) / (c + 1)) := mul_le_mul_of_nonneg_left hmd hc
      _ ≤ ν - c * critical w (u 0) := hcd
  have hB' : ∀ x : ℝ,
      HasDerivWithinAt (fun s => critical w (u 0) + ε * s) ε (Ici x) x := by
    intro x
    have := ((hasDerivAt_id' x).const_mul ε).const_add (critical w (u 0))
    simpa using this.hasDerivWithinAt
  have key := image_le_of_liminf_slope_right_lt_deriv_boundary'
    (f := fun s => critical w (u s))
    (f' := fun x => -(ν - c * critical w (u x)) * dissipation w (u x)) (a := 0) (b := t)
    (B := fun s => critical w (u 0) + ε * s) (B' := fun _ => ε)
    (h.continuousOn_critical.mono (Icc_subset_Icc le_rfl ht.2))
    (fun x hx r hr => h.frequently_slope_lt ⟨hx.1, hx.2.trans_le ht.2⟩ hr)
    (by simp)
    (by fun_prop)
    (fun x _ => hB' x)
    (by
      intro x hx hxe
      have hxe' : critical w (u x) = critical w (u 0) + ε * x := hxe
      have hY : 0 ≤ dissipation w (u x) :=
        dissipation_nonneg (fun k => (h.weight_pos k).le) _
      have hxt : c * (ε * x) ≤ c * (ε * t) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hx.2.le hε.le) hc
      have hcX : 0 ≤ ν - c * critical w (u x) := by
        rw [hxe', mul_add]
        linarith
      have hle : -(ν - c * critical w (u x)) * dissipation w (u x) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hcX) hY
      show -(ν - c * critical w (u x)) * dissipation w (u x) < ε
      linarith)
  have hkey : critical w (u t) ≤ critical w (u 0) + ε * t := key (right_mem_Icc.mpr ht0)
  linarith

/-- [proved-derived; formal-checked] **The laminar class pays its dissipation, over all modes.**
If `c * X 0 < ν` then `X t + (ν - c * X 0) * ∫ s in 0..t, Y s ≤ X 0` on `[0, T]`. -/
theorem ClassSolution.critical_add_dissipation_le [Countable ι]
    (h : ClassSolution w ν c T u N) (h0 : c * critical w (u 0) < ν) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) :
    critical w (u t) + (ν - c * critical w (u 0)) *
      ∫ s in (0 : ℝ)..t, dissipation w (u s) ≤ critical w (u 0) := by
  have hbal := h.balance le_rfl ht.1 ht.2
  have h0I : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, ht.1.trans ht.2⟩
  have hYint := intervalIntegrable_of_continuousOn h.continuousOn_dissipation h0I ht
  have hXYint := intervalIntegrable_of_continuousOn h.continuousOn_product h0I ht
  have hmono : ∫ s in (0 : ℝ)..t, critical w (u s) * dissipation w (u s)
      ≤ ∫ s in (0 : ℝ)..t, critical w (u 0) * dissipation w (u s) := by
    refine intervalIntegral.integral_mono_on ht.1 hXYint (hYint.const_mul _) fun s hs => ?_
    exact mul_le_mul_of_nonneg_right (h.critical_le_initial h0 ⟨hs.1, hs.2.trans ht.2⟩)
      (dissipation_nonneg (fun k => (h.weight_pos k).le) _)
  rw [intervalIntegral.integral_const_mul] at hmono
  have h1 := mul_le_mul_of_nonneg_left hmono h.coherence_nonneg
  have h2 : (ν - c * critical w (u 0)) * ∫ s in (0 : ℝ)..t, dissipation w (u s)
      = ν * (∫ s in (0 : ℝ)..t, dissipation w (u s))
        - c * (critical w (u 0) * ∫ s in (0 : ℝ)..t, dissipation w (u s)) := by ring
  rw [h2]
  linarith

/-- [proved-derived; formal-checked] The dissipation paid up to `t` is at most the drop of the
critical norm: `(ν - c * X 0) * ∫ s in 0..t, Y s ≤ X 0 - X t`. -/
theorem ClassSolution.dissipation_integral_le_drop [Countable ι]
    (h : ClassSolution w ν c T u N) (h0 : c * critical w (u 0) < ν) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) :
    (ν - c * critical w (u 0)) * ∫ s in (0 : ℝ)..t, dissipation w (u s)
      ≤ critical w (u 0) - critical w (u t) := by
  linarith [h.critical_add_dissipation_le h0 ht]

/-- [proved-derived; formal-checked] **The gradient's budget.** If `c * X 0 < ν` then
`∫ s in 0..t, Y s ≤ X 0 / (ν - c * X 0)` for every `t` of `[0, T]`: a bound fixed by the opening
state, in which the horizon does not appear. -/
theorem ClassSolution.integral_dissipation_le [Countable ι] (h : ClassSolution w ν c T u N)
    (h0 : c * critical w (u 0) < ν) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    ∫ s in (0 : ℝ)..t, dissipation w (u s)
      ≤ critical w (u 0) / (ν - c * critical w (u 0)) := by
  have hd : 0 < ν - c * critical w (u 0) := sub_pos.mpr h0
  have h1 := h.dissipation_integral_le_drop h0 ht
  have h2 : 0 ≤ critical w (u t) := critical_nonneg (fun k => (h.weight_pos k).le) _
  rw [le_div_iff₀ hd]
  linarith

/-- [proved-derived; formal-checked] For `0 < c` the class is `X 0 < ν / c`. -/
theorem ClassSolution.critical_le_initial_of_lt_div [Countable ι]
    (h : ClassSolution w ν c T u N) (hc : 0 < c) (h0 : critical w (u 0) < ν / c) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) : critical w (u t) ≤ critical w (u 0) := by
  refine h.critical_le_initial ?_ ht
  rw [lt_div_iff₀ hc] at h0
  linarith

/-- [proved-derived; formal-checked] **The continuation form, with no smallness.** On `[0, T]`,
`X t ≤ X 0 * exp (c * ∫ s in 0..t, Y s)`: the critical norm cannot leave every bound while the
dissipation norm stays integrable. -/
theorem ClassSolution.critical_le_mul_exp [Countable ι] (h : ClassSolution w ν c T u N)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    critical w (u t)
      ≤ critical w (u 0) * Real.exp (c * ∫ s in (0 : ℝ)..t, dissipation w (u s)) := by
  have hc := h.coherence_nonneg
  have hν := h.viscosity_pos
  have hw : ∀ k, 0 ≤ w k := fun k => (h.weight_pos k).le
  have hX0 : 0 ≤ critical w (u 0) := critical_nonneg hw _
  have h0I : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, ht.1.trans ht.2⟩
  have hYc := h.continuousOn_dissipation
  -- a fence for every `ε > 0`
  have hfence : ∀ ε : ℝ, 0 < ε → critical w (u t) ≤ (critical w (u 0) + ε) *
      Real.exp (c * (∫ s in (0 : ℝ)..t, dissipation w (u s)) + ε * t) := by
    intro ε hε
    have hprim : ContinuousOn (fun x => ∫ s in (0 : ℝ)..x, dissipation w (u s)) (Icc 0 t) :=
      continuousOn_primitive hYc h0I ht ht.1
    have key := image_le_of_liminf_slope_right_lt_deriv_boundary'
      (f := fun s => critical w (u s))
      (f' := fun x => -(ν - c * critical w (u x)) * dissipation w (u x)) (a := 0) (b := t)
      (B := fun x => (critical w (u 0) + ε) *
        Real.exp (c * (∫ s in (0 : ℝ)..x, dissipation w (u s)) + ε * x))
      (B' := fun x => (critical w (u 0) + ε) *
        (Real.exp (c * (∫ s in (0 : ℝ)..x, dissipation w (u s)) + ε * x) *
          (c * dissipation w (u x) + ε * 1)))
      (h.continuousOn_critical.mono (Icc_subset_Icc le_rfl ht.2))
      (fun x hx r hr => h.frequently_slope_lt ⟨hx.1, hx.2.trans_le ht.2⟩ hr)
      (by simp; linarith)
      (continuousOn_const.mul (Real.continuous_exp.comp_continuousOn
        ((continuousOn_const.mul hprim).add (continuousOn_const.mul continuousOn_id))))
      (fun x hx => by
        have hxT : x ∈ Ico (0 : ℝ) T := ⟨hx.1, hx.2.trans_le ht.2⟩
        have h1 := (hasDerivWithinAt_primitive hYc h0I hxT).const_mul c
        have h2 := (hasDerivWithinAt_id x (Ici x)).const_mul ε
        exact ((h1.add h2).exp).const_mul (critical w (u 0) + ε))
      (by
        intro x hx hxe
        have hY : 0 ≤ dissipation w (u x) := dissipation_nonneg hw _
        have he : 0 < Real.exp (c * (∫ s in (0 : ℝ)..x, dissipation w (u s)) + ε * x) :=
          Real.exp_pos _
        have hxe' : critical w (u x) = (critical w (u 0) + ε) *
            Real.exp (c * (∫ s in (0 : ℝ)..x, dissipation w (u s)) + ε * x) := hxe
        show -(ν - c * critical w (u x)) * dissipation w (u x) <
          (critical w (u 0) + ε) *
            (Real.exp (c * (∫ s in (0 : ℝ)..x, dissipation w (u s)) + ε * x) *
              (c * dissipation w (u x) + ε * 1))
        rw [hxe']
        generalize Real.exp (c * (∫ s in (0 : ℝ)..x, dissipation w (u s)) + ε * x) = e at he
        generalize dissipation w (u x) = y at hY
        generalize critical w (u 0) = X₀ at hX0
        have hP : 0 < (X₀ + ε) * e := mul_pos (by linarith) he
        have h1 : 0 ≤ ν * y := mul_nonneg hν.le hY
        have h2 : 0 < (X₀ + ε) * e * ε := mul_pos hP hε
        nlinarith)
    exact key (right_mem_Icc.mpr ht.1)
  -- let the fence down
  have hcont : Tendsto (fun ε : ℝ => (critical w (u 0) + ε) *
      Real.exp (c * (∫ s in (0 : ℝ)..t, dissipation w (u s)) + ε * t)) (𝓝[>] 0)
      (𝓝 ((critical w (u 0) + 0) *
        Real.exp (c * (∫ s in (0 : ℝ)..t, dissipation w (u s)) + 0 * t))) :=
    (Continuous.tendsto (by fun_prop) 0).mono_left nhdsWithin_le_nhds
  have hlim := ge_of_tendsto hcont
    (eventually_mem_nhdsWithin.mono fun ε hε => hfence ε hε)
  simpa using hlim

/-- [proved-derived; formal-checked] The continuation criterion: a bound on `∫ Y` bounds `X`. -/
theorem ClassSolution.critical_le_of_integral_le [Countable ι]
    (h : ClassSolution w ν c T u N) {t M : ℝ} (ht : t ∈ Icc (0 : ℝ) T)
    (hM : ∫ s in (0 : ℝ)..t, dissipation w (u s) ≤ M) :
    critical w (u t) ≤ critical w (u 0) * Real.exp (c * M) := by
  refine (h.critical_le_mul_exp ht).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (critical_nonneg (fun k => (h.weight_pos k).le) _)
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hM h.coherence_nonneg)

end Main

/-! ## Every truncation is a solution in the class -/

section Truncation

variable {ι : Type*} [Fintype ι] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {w : ι → ℝ} {ν c : ℝ} {Tf : ι → Finset (ι × ι)} {u N : ℝ → ι → E}

/-- [proved-derived; formal-checked] A comb system on a `Fintype` of modes is a solution in the
class on every `[0, T]`. -/
theorem ClassSolution.of_combSystem (h : CombSystem w ν c Tf u N) (T : ℝ) :
    ClassSolution w ν c T u N where
  weight_pos := h.weight_pos
  viscosity_pos := h.viscosity_pos
  coherence_nonneg := h.coherence_nonneg
  evolves := fun k t ht => (h.evolves k t ht.1).mono Icc_subset_Ici_self
  summable_critical := fun _ _ => (hasSum_fintype _).summable
  summable_dissipation := fun _ _ => (hasSum_fintype _).summable
  continuousOn_critical :=
    (h.continuousOn_critical.mono Icc_subset_Ici_self).congr
      fun t _ => critical_eq_criticalNorm w (u t)
  continuousOn_dissipation :=
    (h.continuousOn_dissipation.mono Icc_subset_Ici_self).congr
      fun t _ => dissipation_eq_dissipationNorm w (u t)
  feed_le := fun t ht S => by
    rw [critical_eq_criticalNorm, dissipation_eq_dissipationNorm]
    refine le_trans ?_ (feed_sum_le_critical_mul_dissipation h.weight_pos h.coherence_nonneg
      h.fibres_disjoint (u t) (N t) (h.feed_le t ht.1))
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      fun k _ _ => div_nonneg (norm_nonneg _) (h.weight_pos k).le

end Truncation

/-! ## Complex amplitudes -/

section ComplexAmplitudes

variable {ι : Type*} [Countable ι] {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  {w : ι → ℝ} {ν c T : ℝ} {u N : ℝ → ι → F}

/-- [proved-derived; formal-checked] The laminar class over all modes on a complex amplitude
space, whose norm is read through the real inner product `Re ⟪x, y⟫`. -/
theorem ClassSolution.critical_le_initial_complex (h : ClassSolution w ν c T u N)
    (h0 : c * critical w (u 0) < ν) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    critical w (u t) ≤ critical w (u 0) := by
  let _ : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  exact ClassSolution.critical_le_initial h h0 ht

/-- [proved-derived; formal-checked] The dissipation paid on a complex amplitude space. -/
theorem ClassSolution.dissipation_integral_le_drop_complex (h : ClassSolution w ν c T u N)
    (h0 : c * critical w (u 0) < ν) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    (ν - c * critical w (u 0)) * ∫ s in (0 : ℝ)..t, dissipation w (u s)
      ≤ critical w (u 0) - critical w (u t) := by
  let _ : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  exact ClassSolution.dissipation_integral_le_drop h h0 ht

/-- [proved-derived; formal-checked] The gradient's budget on a complex amplitude space. -/
theorem ClassSolution.integral_dissipation_le_complex (h : ClassSolution w ν c T u N)
    (h0 : c * critical w (u 0) < ν) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    ∫ s in (0 : ℝ)..t, dissipation w (u s)
      ≤ critical w (u 0) / (ν - c * critical w (u 0)) := by
  let _ : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  exact ClassSolution.integral_dissipation_le h h0 ht

/-- [proved-derived; formal-checked] The continuation form on a complex amplitude space. -/
theorem ClassSolution.critical_le_mul_exp_complex (h : ClassSolution w ν c T u N) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) :
    critical w (u t)
      ≤ critical w (u 0) * Real.exp (c * ∫ s in (0 : ℝ)..t, dissipation w (u s)) := by
  let _ : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  exact ClassSolution.critical_le_mul_exp h ht

end ComplexAmplitudes

/-! ## The Fourier instance: the feed summed over all triads -/

section Fourier

variable {n : Type*} [Fintype n] {ι : Type*}

/-- [definition] The fibre over the mode `k`: the pairs of modes whose wave vectors add to
`κ k`. For the fluid it is unending. -/
def fibre (κ : ι → EuclideanSpace ℝ n) (k : ι) : Set (ι × ι) :=
  {pq | κ pq.1 + κ pq.2 = κ k}

omit [Fintype n] in
theorem mem_fibre {κ : ι → EuclideanSpace ℝ n} {k : ι} {pq : ι × ι} :
    pq ∈ fibre κ k ↔ κ pq.1 + κ pq.2 = κ k := Iff.rfl

omit [Fintype n] in
/-- With injective wave vectors a pair of modes feeds at most one mode. -/
theorem fibre_disjoint {κ : ι → EuclideanSpace ℝ n} (hκ : Function.Injective κ) (k k' : ι)
    (hkk' : k ≠ k') : Disjoint (fibre κ k) (fibre κ k') := by
  rw [Set.disjoint_left]
  intro pq h1 h2
  exact hkk' (hκ ((mem_fibre.mp h1).symm.trans (mem_fibre.mp h2)))

/-- [definition] The fluid's feed into the mode `k`, summed over all its triads:
`N_k = -i P_k ∑' (p, q) : κ p + κ q = κ k, (κ q · a_p) a_q`. -/
def feedAll (κ : ι → EuclideanSpace ℝ n)
    (P : ι → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) (a : ι → EuclideanSpace ℂ n)
    (k : ι) : EuclideanSpace ℂ n :=
  (-Complex.I) • P k (∑' pq : fibre κ k, wavePairing (κ pq.1.2) (a pq.1.1) • a pq.1.2)

/-- [proved-derived; formal-checked] **The triad bound of the fluid's feed, all triads.** With
projections of norm at most one, incompressible amplitudes and summable amplitudes,
`‖N_k‖ ≤ ‖κ k‖ * ∑' (p, q) ∈ fibre k, ‖a_p‖ * ‖a_q‖`: the comb's bound with `c = 1`. -/
theorem norm_feedAll_le (κ : ι → EuclideanSpace ℝ n)
    (P : ι → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) (hP : ∀ k, ‖P k‖ ≤ 1)
    (a : ι → EuclideanSpace ℂ n) (hdiv : ∀ p, wavePairing (κ p) (a p) = 0)
    (hA : Summable fun k => ‖a k‖) (k : ι) :
    ‖feedAll κ P a k‖ ≤ ‖κ k‖ * ∑' pq : fibre κ k, ‖a pq.1.1‖ * ‖a pq.1.2‖ := by
  have hprod : Summable fun pq : ι × ι => ‖a pq.1‖ * ‖a pq.2‖ :=
    hA.mul_of_nonneg hA (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  have hsub : Summable fun pq : fibre κ k => ‖a pq.1.1‖ * ‖a pq.1.2‖ := hprod.subtype _
  have hterm : ∀ pq : fibre κ k, ‖wavePairing (κ pq.1.2) (a pq.1.1) • a pq.1.2‖
      ≤ ‖κ k‖ * (‖a pq.1.1‖ * ‖a pq.1.2‖) := by
    intro pq
    have h1 := norm_transport_le (k := κ k) (p := κ pq.1.1) (q := κ pq.1.2)
      (mem_fibre.mp pq.2).symm (hdiv pq.1.1) (a pq.1.2)
    rwa [mul_assoc] at h1
  have hnorm : Summable fun pq : fibre κ k =>
      ‖wavePairing (κ pq.1.2) (a pq.1.1) • a pq.1.2‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm (hsub.mul_left _)
  calc ‖feedAll κ P a k‖
      = ‖P k (∑' pq : fibre κ k, wavePairing (κ pq.1.2) (a pq.1.1) • a pq.1.2)‖ := by
        unfold feedAll
        rw [norm_smul, norm_neg, Complex.norm_I, one_mul]
    _ ≤ 1 * ‖∑' pq : fibre κ k, wavePairing (κ pq.1.2) (a pq.1.1) • a pq.1.2‖ :=
        (P k).le_of_opNorm_le (hP k) _
    _ = ‖∑' pq : fibre κ k, wavePairing (κ pq.1.2) (a pq.1.1) • a pq.1.2‖ := one_mul _
    _ ≤ ∑' pq : fibre κ k, ‖wavePairing (κ pq.1.2) (a pq.1.1) • a pq.1.2‖ :=
        norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' pq : fibre κ k, ‖κ k‖ * (‖a pq.1.1‖ * ‖a pq.1.2‖) :=
        hnorm.tsum_le_tsum hterm (hsub.mul_left _)
    _ = ‖κ k‖ * ∑' pq : fibre κ k, ‖a pq.1.1‖ * ‖a pq.1.2‖ := hsub.tsum_mul_left _

/-- [definition] A solution of the fluid's law in Fourier variables, in the class, on `[0, T]`:
a positive viscosity, projections of norm at most one, amplitudes incompressible on `[0, T]`,
each mode damped at `ν * ‖κ k‖ ^ 2` and fed by `feedAll`, and the two readings summable and
continuous in time. The modes are any family `ι` with wave vectors `κ`. -/
structure FourierSolution (κ : ι → EuclideanSpace ℝ n) (ν T : ℝ)
    (P : ι → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (a : ℝ → ι → EuclideanSpace ℂ n) : Prop where
  viscosity_pos : 0 < ν
  projection_le : ∀ k, ‖P k‖ ≤ 1
  incompressible : ∀ t ∈ Icc (0 : ℝ) T, ∀ k, wavePairing (κ k) (a t k) = 0
  evolves : ∀ k, ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt (fun s => a s k)
    (-(ν * ‖κ k‖ ^ 2) • a t k + feedAll κ P (a t) k) (Icc 0 T) t
  summable_critical : ∀ t ∈ Icc (0 : ℝ) T, Summable fun k => ‖a t k‖ / ‖κ k‖
  summable_dissipation : ∀ t ∈ Icc (0 : ℝ) T, Summable fun k => ‖κ k‖ * ‖a t k‖
  continuousOn_critical : ContinuousOn (fun t => critical (fun k => ‖κ k‖) (a t)) (Icc 0 T)
  continuousOn_dissipation :
    ContinuousOn (fun t => dissipation (fun k => ‖κ k‖) (a t)) (Icc 0 T)

variable {κ : ι → EuclideanSpace ℝ n} {ν T : ℝ}
  {P : ι → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n} {a : ℝ → ι → EuclideanSpace ℂ n}

/-- [proved-derived; formal-checked] **The fluid's law in Fourier variables is a solution in the
class**, with weights `‖κ k‖` and coherence constant one, when the wave vectors are distinct and
nonzero. -/
theorem FourierSolution.classSolution (h : FourierSolution κ ν T P a)
    (hκ : Function.Injective κ) (hκ0 : ∀ k, κ k ≠ 0) :
    ClassSolution (fun k => ‖κ k‖) ν 1 T a (fun t => feedAll κ P (a t)) :=
  ClassSolution.of_triads (fun k => norm_pos_iff.mpr (hκ0 k)) h.viscosity_pos zero_le_one
    h.evolves h.summable_critical h.summable_dissipation h.continuousOn_critical
    h.continuousOn_dissipation (fibre_disjoint hκ)
    (fun t ht k => by
      have hA := summable_norm_of_class (fun k => norm_pos_iff.mpr (hκ0 k))
        (h.summable_critical t ht) (h.summable_dissipation t ht)
      rw [one_mul]
      exact norm_feedAll_le κ P h.projection_le (a t) (h.incompressible t ht) hA k)

/-- [proved-derived; formal-checked] **The laminar class of the fluid's law over all modes.** If
`∑' k, ‖a 0 k‖ / ‖κ k‖ < ν` then this reading never passes its opening value on `[0, T]`. -/
theorem FourierSolution.critical_le_initial [Countable ι] (h : FourierSolution κ ν T P a)
    (hκ : Function.Injective κ) (hκ0 : ∀ k, κ k ≠ 0)
    (h0 : critical (fun k => ‖κ k‖) (a 0) < ν) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    critical (fun k => ‖κ k‖) (a t) ≤ critical (fun k => ‖κ k‖) (a 0) :=
  (h.classSolution hκ hκ0).critical_le_initial_complex (by rwa [one_mul]) ht

/-- [proved-derived; formal-checked] The fluid's law in its laminar class pays
`(ν - X 0) * ∫ s in 0..t, Y s ≤ X 0 - X t`, with `Y = ∑' k, ‖κ k‖ * ‖a k‖`. -/
theorem FourierSolution.dissipation_integral_le_drop [Countable ι]
    (h : FourierSolution κ ν T P a) (hκ : Function.Injective κ) (hκ0 : ∀ k, κ k ≠ 0)
    (h0 : critical (fun k => ‖κ k‖) (a 0) < ν) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    (ν - critical (fun k => ‖κ k‖) (a 0)) *
        ∫ s in (0 : ℝ)..t, dissipation (fun k => ‖κ k‖) (a s)
      ≤ critical (fun k => ‖κ k‖) (a 0) - critical (fun k => ‖κ k‖) (a t) := by
  have := (h.classSolution hκ hκ0).dissipation_integral_le_drop_complex (by rwa [one_mul]) ht
  rwa [one_mul] at this

/-- [proved-derived; formal-checked] **The gradient's budget of the fluid's law.** Below the
threshold, `∫ s in 0..t, ∑' k, ‖κ k‖ * ‖a s k‖ ≤ X 0 / (ν - X 0)` on `[0, T]`, whatever `T`. -/
theorem FourierSolution.integral_dissipation_le [Countable ι] (h : FourierSolution κ ν T P a)
    (hκ : Function.Injective κ) (hκ0 : ∀ k, κ k ≠ 0)
    (h0 : critical (fun k => ‖κ k‖) (a 0) < ν) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    ∫ s in (0 : ℝ)..t, dissipation (fun k => ‖κ k‖) (a s)
      ≤ critical (fun k => ‖κ k‖) (a 0) / (ν - critical (fun k => ‖κ k‖) (a 0)) := by
  have := (h.classSolution hκ hκ0).integral_dissipation_le_complex (by rwa [one_mul]) ht
  rwa [one_mul] at this

/-- [proved-derived; formal-checked] The continuation form for the fluid's law, with no
smallness: `X t ≤ X 0 * exp (∫ s in 0..t, Y s)`. -/
theorem FourierSolution.critical_le_mul_exp [Countable ι] (h : FourierSolution κ ν T P a)
    (hκ : Function.Injective κ) (hκ0 : ∀ k, κ k ≠ 0) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    critical (fun k => ‖κ k‖) (a t) ≤ critical (fun k => ‖κ k‖) (a 0) *
      Real.exp (∫ s in (0 : ℝ)..t, dissipation (fun k => ‖κ k‖) (a s)) := by
  have := (h.classSolution hκ hκ0).critical_le_mul_exp_complex ht
  rwa [one_mul] at this

end Fourier

/-! ## The torus: the nonzero lattice vectors -/

section Lattice

variable {n : Type*} [Fintype n]

/-- [definition] The nonzero lattice vectors: the modes of a mean-free field on the torus. -/
abbrev LatticeMode (n : Type*) := {k : n → ℤ // k ≠ 0}

/-- [definition] The wave vector of a lattice mode, in the Euclidean norm. -/
def latticeWave (k : LatticeMode n) : EuclideanSpace ℝ n :=
  WithLp.toLp 2 fun j => (k.1 j : ℝ)

omit [Fintype n] in
theorem latticeWave_injective : Function.Injective (latticeWave (n := n)) := by
  intro k k' h
  have h1 : (fun j => (k.1 j : ℝ)) = fun j => (k'.1 j : ℝ) := WithLp.toLp_injective 2 h
  apply Subtype.ext
  funext j
  exact_mod_cast congrFun h1 j

omit [Fintype n] in
theorem latticeWave_ne_zero (k : LatticeMode n) : latticeWave k ≠ 0 := by
  intro h
  apply k.2
  funext j
  have h1 : (fun j => (k.1 j : ℝ)) = fun _ => (0 : ℝ) := WithLp.toLp_injective 2 h
  exact_mod_cast congrFun h1 j

variable {ν T : ℝ}
  {P : LatticeMode n → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n}
  {a : ℝ → LatticeMode n → EuclideanSpace ℂ n}

/-- [proved-derived; formal-checked] **The equation on the torus, in Fourier variables.** A
solution of the fluid's law on the nonzero lattice vectors (`n = Fin 3` for the fluid), in the
class on `[0, T]`, with `∑' k, ‖a 0 k‖ / |k| < ν`, keeps `X t ≤ X 0` on `[0, T]`. -/
theorem torus_critical_le_initial (h : FourierSolution latticeWave ν T P a)
    (h0 : critical (fun k => ‖latticeWave k‖) (a 0) < ν) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    critical (fun k => ‖latticeWave k‖) (a t) ≤ critical (fun k => ‖latticeWave k‖) (a 0) :=
  h.critical_le_initial latticeWave_injective latticeWave_ne_zero h0 ht

/-- [proved-derived; formal-checked] **The gradient's budget on the torus.** Below the threshold
`∫ s in 0..t, ∑' k, |k| * ‖a s k‖ ≤ X 0 / (ν - X 0)` on `[0, T]`, whatever `T`. -/
theorem torus_integral_dissipation_le (h : FourierSolution latticeWave ν T P a)
    (h0 : critical (fun k => ‖latticeWave k‖) (a 0) < ν) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    ∫ s in (0 : ℝ)..t, dissipation (fun k => ‖latticeWave k‖) (a s)
      ≤ critical (fun k => ‖latticeWave k‖) (a 0)
        / (ν - critical (fun k => ‖latticeWave k‖) (a 0)) :=
  h.integral_dissipation_le latticeWave_injective latticeWave_ne_zero h0 ht

end Lattice

section Audit

#print axioms summable_norm_of_class
#print axioms tsum_norm_sq_le
#print axioms feed_window_le_of_triads
#print axioms ClassSolution.of_triads
#print axioms ClassSolution.tsum_feed_le
#print axioms ClassSolution.window_balance
#print axioms ClassSolution.balance
#print axioms ClassSolution.frequently_slope_lt
#print axioms ClassSolution.critical_le_initial
#print axioms ClassSolution.dissipation_integral_le_drop
#print axioms ClassSolution.integral_dissipation_le
#print axioms ClassSolution.critical_le_initial_of_lt_div
#print axioms ClassSolution.critical_le_mul_exp
#print axioms ClassSolution.critical_le_of_integral_le
#print axioms ClassSolution.of_combSystem
#print axioms ClassSolution.critical_le_initial_complex
#print axioms ClassSolution.integral_dissipation_le_complex
#print axioms norm_feedAll_le
#print axioms FourierSolution.classSolution
#print axioms FourierSolution.critical_le_initial
#print axioms FourierSolution.dissipation_integral_le_drop
#print axioms FourierSolution.integral_dissipation_le
#print axioms FourierSolution.critical_le_mul_exp
#print axioms latticeWave_injective
#print axioms torus_critical_le_initial
#print axioms torus_integral_dissipation_le

end Audit

end Holonics.Fluid.LaminarAllModes
