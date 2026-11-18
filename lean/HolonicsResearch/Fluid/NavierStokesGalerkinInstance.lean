import HolonicsResearch.Fluid.NavierStokesLaminarClass
import Mathlib

/-!
# The truncated fluid is a comb, its energy count holds at every size, and the comb's threshold is attained

This module joins three statements to `Fluid/NavierStokesLaminarClass` (the laminar class of a
comb system, `c * X 0 < ν`).

## G1. The truncation of the fluid's equation is a comb system

[definition] A **truncation** is a finite family of modes `k : ι` with distinct nonzero wave
vectors `κ k` (real, over any finite set `n` of coordinates; the fluid is `n = Fin 3`), complex
amplitudes `a t k` across their wave vectors (`wavePairing (κ k) (a t k) = 0`, the
incompressible condition), and the law

  `d/dt a_k = -(ν * ‖κ k‖ ^ 2) • a_k + feed κ P a k`,
  `feed κ P a k = (-i) • P k (∑_{(p, q) ∈ triads κ k} (κ q · a_p) • a_q)`,

where `triads κ k` is the set of pairs with `κ p + κ q = κ k` and `P k` is a continuous linear
map of norm at most one (the projection across `κ k`). The derivative is taken on `[0, ∞)`.

[proved-derived; formal-checked]

* `triads_disjoint`: distinct wave vectors make the fibres of `triads` pairwise disjoint;
* `norm_feed_le_triads`: `‖feed κ P a k‖ ≤ ‖κ k‖ * ∑ ‖a p‖ * ‖a q‖` over the triads of `k`;
* `Truncation.combSystem`: a truncation is a `CombSystem` with weights `w k = ‖κ k‖`, coherence
  constant `c = 1` and comb `triads κ`;
* `Truncation.critical_le_initial`: `X 0 < ν` gives `X t ≤ X 0` for every `0 ≤ t`, with
  `X = criticalNorm (fun k => ‖κ k‖) a = ∑ k, ‖a k‖ / ‖κ k‖`;
* `Truncation.dissipation_integral_le_drop`: `(ν - X 0) * ∫ s in 0..t, Y s ≤ X 0 - X t`;
* `Truncation.integral_dissipation_le`: `∫ s in 0..t, Y s ≤ X 0 / (ν - X 0)`.

None of the three bounds names `ι`: the class and its bounds are the same at every truncation.
[proved-standard; from training] For the equation itself (all wave vectors of the torus or of the
whole space) this is the class of Lei and Lin (2011), `∫ |ξ|⁻¹ |û(ξ)| dξ < (2π)³ ν`; the passage
from the truncations to the equation is not made here.

[proved-derived; formal-checked] The projection can be the one of Leray: `leray q` is the
orthogonal projection of `EuclideanSpace ℂ n` across the complexified wave vector, with
`norm_leray_le : ‖leray q‖ ≤ 1` and `wavePairing_leray : wavePairing q (leray q v) = 0`, so that
`wavePairing_feed_leray`: the feed built with `P k = leray (κ k)` is again across `κ k`. Then the
opening state decides the incompressible condition (`wavePairing_eq_zero_of_evolves`, by G2's
energy count on the pairing `κ k · a_k`, which obeys `y' = -(ν ‖κ k‖²) y`), and
`Truncation.of_leray`, `leray_truncation_critical_le_initial` state the laminar class from the
opening state and the law alone.

## G2. The energy equality of a damped family with a conservative feed

[proved-derived; formal-checked] For modes in a real inner product space with
`d/dt u_k = -(ν * w_k ^ 2) • u_k + N_k` on `[0, ∞)` (`Evolves`) and a feed that does no work,
`∑ k, ⟪u_k, N_k⟫ = 0` (`Conservative`), with no feed bound, no comb and no smallness:

* `hasDerivWithinAt_energy`: `E = (1/2) ∑ ‖u_k‖ ^ 2` has the derivative
  `-(ν * ∑ w_k ^ 2 * ‖u_k‖ ^ 2)`;
* `energy_antitoneOn`: `E` is antitone on `[0, ∞)` for `0 ≤ ν`;
* `energy_add_dissipation`: `E t + ν * ∫ s in 0..t, ∑ w_k ^ 2 * ‖u_k s‖ ^ 2 = E 0`;
* `energy_le_initial`, `integral_dissipationRate_le`: the two bounds that follow.

Reading: the energy count holds at every Reynolds number and at every truncation, and it says
nothing of the critical reading `X`.

## G2′. A weighted count, and the second one

[proved-derived; formal-checked] For a weight `g : ι → ℝ` and a feed that does no work in the
weighted count, `∑ k, g k * ⟪u_k, N_k⟫ = 0` (`WeightedConservative`):

* `hasDerivWithinAt_weightedEnergy`: `E_g = (1/2) ∑ g_k * ‖u_k‖ ^ 2` has the derivative
  `-(ν * ∑ g_k * w_k ^ 2 * ‖u_k‖ ^ 2)`;
* `weightedEnergy_antitoneOn`, `weightedEnergy_le_initial`: for `0 ≤ g` and `0 ≤ ν` it never
  rises; G2 is `g = 1` (`weightedEnergy_one`, `weightedRate_one`, `weightedConservative_one`);
* `criticalNorm_le_sqrt_mul_sqrt`: `X ≤ √(∑ w_k ^ (-4)) * √(2 * E_g)` at `g k = w k ^ 2`
  (Cauchy-Schwarz on `X = ∑ w_k ^ (-2) * (w_k * ‖u_k‖)`);
* `critical_le_of_second_count`: if the feed conserves the second count (`g k = w k ^ 2`, the
  enstrophy) then `X t ≤ √(∑ w_k ^ (-4)) * √(2 * E_g 0)` at every `0 ≤ t`, with no feed bound
  and no smallness.

Reading: where the feed conserves the second count the critical reading is bounded at every
Reynolds number, which is the case of two dimensions. In three dimensions the second count is not
conserved, and that is the stretching the comb's coherence constant has to answer for. The bound
names the modes through `∑ w_k ^ (-4)`, which converges over the wave vectors of a torus of
dimension two or three.

## G4. Continuation: the critical reading leaves only through the dissipation integral

[proved-derived; formal-checked] For every comb system, whatever `c ≥ 0` and the size of the data:

* `CombSystem.critical_le_mul_exp`: `X t ≤ X 0 * exp (c * ∫ s in 0..t, Y s)` for `0 ≤ t`, from
  the slope bound `D⁺X ≤ -(ν - c X) Y ≤ c X Y` and Grönwall's argument on `X * exp (-c ∫ Y)`;
* `CombSystem.critical_le_of_integral_le`: `∫ s in 0..t, Y s ≤ M` gives `X t ≤ X 0 * exp (c M)`;
* `CombSystem.critical_le_mul_exp_complex`, `Truncation.critical_le_mul_exp`: the same on complex
  amplitudes and for the truncated fluid (`c = 1`), the same at every truncation.

Reading: the critical reading can leave every bound only through an unbounded dissipation
integral. This is the comb's form of the continuation criterion of Beale, Kato and Majda (atlas
`ns.bkm-continuation`), with `Y = ∑ k, w k * ‖u k‖`, the amplitude norm of the gradient, in the
place of the vorticity's maximum. G3's blow-up state shows the integral does diverge there.

## G3. The laminar threshold is attained inside the comb class

[definition] On a finite additive group `ι` (`ZMod m` for one), real amplitudes, every weight
equal to `ω > 0`, the comb `sumTriads k = {(p, q) | p + q = k}` and the coherent feed
`coherentFeed ω u k = ω * ∑_{p + q = k} u p * u q`.

[proved-derived; formal-checked]

* `norm_coherentFeed_le`: the coherent feed meets the comb's bound with `c = 1`, and
  `norm_coherentFeed_eq_of_nonneg`: with equality on nonnegative amplitudes;
* `uniform_combSystem`: a uniform state `u t k = φ t` is a comb system when
  `φ' = -(ν ω²) φ + ω m φ²` on `[0, ∞)`, `m = Fintype.card ι`;
* `constant_combSystem`, `criticalNorm_constantState`, `dissipationNorm_constantState`,
  `integral_dissipation_constantState`, `threshold_attained`, `threshold_attained_zmod`: the
  constant state `u k = ν ω / m` is a comb system with `X = ν` at every time and `Y = ν ω²`,
  so `∫ s in 0..t, Y = t * (ν ω²)` passes every bound: at `c * X 0 = ν` no bound `∫ Y ≤ C`
  holds;
* `logistic ν ω X₀ t = ν / (1 - (1 - ν / X₀) * exp (ν ω² t))` and
  `blowupTime ν ω X₀ = log (X₀ / (X₀ - ν)) / (ν ω²)`; for `0 < ν < X₀`:
  `logistic_zero` (it opens at `X₀`), `hasDerivAt_logistic` (`X' = ω² X (X - ν)`),
  `lt_logistic` (`ν < X` before the blow-up time), `logistic_strictMonoOn`,
  `tendsto_logistic_atTop` (`X → +∞` as `t → t*` from below);
* `hasDerivAt_blowupState`, `criticalNorm_blowupState`, `tendsto_criticalNorm_blowupState`,
  `blowup_above_threshold`: the uniform state `u t k = ω * logistic t / m` obeys the comb's law
  with the coherent feed on `[0, t*)`, its critical norm is `logistic t`, it opens at `X₀ > ν`,
  rises strictly and leaves every bound before `t*`;
* `subcritical_combSystem`, `criticalNorm_subcriticalState`: for `0 < X₀ < ν` the same closed form
  is a comb system on all of `[0, ∞)` with critical norm `logistic t`, the laminar class's own
  instance.

Reading: within the comb class every arrangement of the triads' phases is allowed, and there the
laminar threshold cannot be raised. What the fluid has beyond the comb is the constraint on its
phases, of which G2's conservation is the first consequence; the coherent feed of G3 does work on
every positive state (`coherentFeed_work_pos`, `constantState_not_conservative`) and is no fluid.

## What this does not state

Nothing here is the Clay statement. The module constructs no solution of the fluid's equation or
of its truncations: a truncation is a hypothesis, given on `[0, ∞)`. It does not prove that the
fluid's feed conserves the second count in two dimensions: `WeightedConservative` is a hypothesis. It makes no limit of
truncations and says nothing of infinitely many modes, of uniqueness, or of data with
`X 0 ≥ ν`. It does not prove that the fluid's own feed is conservative (that needs the mode set
closed under `k ↦ -k` with the reality condition, and is not assembled here). For projections
other than Leray's the incompressible condition is a hypothesis at every time. G3's states are
comb systems and not fluids; they bound what the comb's count alone can decide and say nothing of
whether a fluid above the threshold stays regular.
-/

noncomputable section

namespace Holonics.Fluid.GalerkinInstance

open Set Filter Topology MeasureTheory
open scoped RealInnerProductSpace
open Holonics.Fluid.LaminarClass

/-! ## G1. The truncation is a comb -/

section Truncation

variable {ι : Type*} [Fintype ι] {n : Type*} [Fintype n]

open Classical in
/-- [definition] The triads of a mode: the pairs whose wave vectors add to its own. -/
def triads (κ : ι → EuclideanSpace ℝ n) (k : ι) : Finset (ι × ι) :=
  Finset.univ.filter fun pq => κ pq.1 + κ pq.2 = κ k

theorem mem_triads {κ : ι → EuclideanSpace ℝ n} {k : ι} {pq : ι × ι} :
    pq ∈ triads κ k ↔ κ pq.1 + κ pq.2 = κ k := by
  classical
  simp [triads]

/-- [proved-derived; formal-checked] Distinct wave vectors: a pair of modes feeds at most one
mode. -/
theorem triads_disjoint {κ : ι → EuclideanSpace ℝ n} (hκ : Function.Injective κ) (k k' : ι)
    (h : k ≠ k') : Disjoint (triads κ k) (triads κ k') := by
  rw [Finset.disjoint_left]
  intro pq h1 h2
  rw [mem_triads] at h1 h2
  exact h (hκ (h1.symm.trans h2))

/-- [definition] The feed of the truncated equation into the mode `k`: the transport terms of
its triads, projected by `P k`, with the factor `-i` of the gradient. -/
def feed (κ : ι → EuclideanSpace ℝ n) (P : ι → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (a : ι → EuclideanSpace ℂ n) (k : ι) : EuclideanSpace ℂ n :=
  (-Complex.I) • P k (∑ pq ∈ triads κ k, wavePairing (κ pq.2) (a pq.1) • a pq.2)

/-- [proved-derived; formal-checked] The comb's feed bound for the truncated equation, with
weight `‖κ k‖` and coherence constant one. -/
theorem norm_feed_le_triads (κ : ι → EuclideanSpace ℝ n)
    (P : ι → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) (hP : ∀ k, ‖P k‖ ≤ 1)
    (a : ι → EuclideanSpace ℂ n) (hdiv : ∀ p, wavePairing (κ p) (a p) = 0) (k : ι) :
    ‖feed κ P a k‖ ≤ ‖κ k‖ * ∑ pq ∈ triads κ k, ‖a pq.1‖ * ‖a pq.2‖ := by
  unfold feed
  rw [norm_smul, norm_neg, Complex.norm_I, one_mul]
  exact norm_feed_le κ a hdiv k (triads κ k) (fun pq hpq => (mem_triads.mp hpq).symm) (P k)
    (hP k)

/-- [definition] A truncation of the fluid's equation on `[0, ∞)`: distinct nonzero wave
vectors, a positive viscosity, projections of norm at most one, amplitudes across their wave
vectors, and the truncated law. -/
structure Truncation (κ : ι → EuclideanSpace ℝ n) (ν : ℝ)
    (P : ι → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)
    (a : ℝ → ι → EuclideanSpace ℂ n) : Prop where
  wave_injective : Function.Injective κ
  wave_ne_zero : ∀ k, κ k ≠ 0
  viscosity_pos : 0 < ν
  projection_le : ∀ k, ‖P k‖ ≤ 1
  incompressible : ∀ t, 0 ≤ t → ∀ k, wavePairing (κ k) (a t k) = 0
  evolves : ∀ k t, 0 ≤ t →
    HasDerivWithinAt (fun s => a s k) (-(ν * ‖κ k‖ ^ 2) • a t k + feed κ P (a t) k) (Ici 0) t

variable {κ : ι → EuclideanSpace ℝ n} {ν : ℝ}
  {P : ι → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n} {a : ℝ → ι → EuclideanSpace ℂ n}

/-- A truncation from derivatives and the incompressible condition on the whole line. -/
theorem Truncation.of_hasDerivAt (hκ : Function.Injective κ) (hκ0 : ∀ k, κ k ≠ 0) (hν : 0 < ν)
    (hP : ∀ k, ‖P k‖ ≤ 1) (hdiv : ∀ t k, wavePairing (κ k) (a t k) = 0)
    (ha : ∀ k t, HasDerivAt (fun s => a s k)
      (-(ν * ‖κ k‖ ^ 2) • a t k + feed κ P (a t) k) t) :
    Truncation κ ν P a :=
  ⟨hκ, hκ0, hν, hP, fun t _ k => hdiv t k, fun k t _ => (ha k t).hasDerivWithinAt⟩

/-- [proved-derived; formal-checked] **The truncation is a comb system**, with weights
`w k = ‖κ k‖`, coherence constant one and the comb of its triads. -/
theorem Truncation.combSystem (h : Truncation κ ν P a) :
    CombSystem (fun k => ‖κ k‖) ν 1 (triads κ) a (fun t => feed κ P (a t)) where
  weight_pos k := norm_pos_iff.mpr (h.wave_ne_zero k)
  viscosity_pos := h.viscosity_pos
  coherence_nonneg := zero_le_one
  fibres_disjoint := triads_disjoint h.wave_injective
  evolves := h.evolves
  feed_le t ht k := by
    rw [one_mul]
    exact norm_feed_le_triads κ P h.projection_le (a t) (h.incompressible t ht) k

/-- [proved-derived; formal-checked] **The laminar class of the truncated fluid.** If
`∑ k, ‖a 0 k‖ / ‖κ k‖ < ν` then this reading never passes its opening value. The statement does
not name the set of modes: it is the same at every truncation. -/
theorem Truncation.critical_le_initial (h : Truncation κ ν P a)
    (h0 : criticalNorm (fun k => ‖κ k‖) (a 0) < ν) {t : ℝ} (ht : 0 ≤ t) :
    criticalNorm (fun k => ‖κ k‖) (a t) ≤ criticalNorm (fun k => ‖κ k‖) (a 0) :=
  h.combSystem.critical_le_initial_complex (by rwa [one_mul]) ht

/-- [proved-derived; formal-checked] The truncated fluid in its laminar class pays
`(ν - X 0) * ∫ s in 0..t, Y s ≤ X 0 - X t`, with `Y = ∑ k, ‖κ k‖ * ‖a k‖`. -/
theorem Truncation.dissipation_integral_le_drop (h : Truncation κ ν P a)
    (h0 : criticalNorm (fun k => ‖κ k‖) (a 0) < ν) {t : ℝ} (ht : 0 ≤ t) :
    (ν - criticalNorm (fun k => ‖κ k‖) (a 0)) *
        ∫ s in (0 : ℝ)..t, dissipationNorm (fun k => ‖κ k‖) (a s)
      ≤ criticalNorm (fun k => ‖κ k‖) (a 0) - criticalNorm (fun k => ‖κ k‖) (a t) := by
  have := h.combSystem.dissipation_integral_le_drop_complex (by rwa [one_mul]) ht
  rwa [one_mul] at this

/-- [proved-derived; formal-checked] The dissipation of the truncated fluid in its laminar class
is integrable over all time, with a bound that does not name the set of modes. -/
theorem Truncation.integral_dissipation_le (h : Truncation κ ν P a)
    (h0 : criticalNorm (fun k => ‖κ k‖) (a 0) < ν) {t : ℝ} (ht : 0 ≤ t) :
    ∫ s in (0 : ℝ)..t, dissipationNorm (fun k => ‖κ k‖) (a s)
      ≤ criticalNorm (fun k => ‖κ k‖) (a 0) / (ν - criticalNorm (fun k => ‖κ k‖) (a 0)) := by
  have hd : 0 < ν - criticalNorm (fun k => ‖κ k‖) (a 0) := sub_pos.mpr h0
  have h1 := h.dissipation_integral_le_drop h0 ht
  have h2 : 0 ≤ criticalNorm (fun k => ‖κ k‖) (a t) :=
    criticalNorm_nonneg (fun k => norm_nonneg _) _
  rw [le_div_iff₀ hd]
  linarith

end Truncation

/-! ### The projection of Leray -/

section Leray

variable {n : Type*} [Fintype n]

/-- [definition] A real wave vector read in the complex amplitude space. -/
def complexify (q : EuclideanSpace ℝ n) : EuclideanSpace ℂ n :=
  WithLp.toLp 2 fun j => (q j : ℂ)

/-- The wave pairing is the inner product with the complexified wave vector. -/
theorem wavePairing_eq_inner (q : EuclideanSpace ℝ n) (a : EuclideanSpace ℂ n) :
    wavePairing q a = inner ℂ (complexify q) a := by
  unfold wavePairing complexify
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [mul_comm]

/-- [definition] The projection of Leray at a wave vector: the orthogonal projection across
it. -/
def leray (q : EuclideanSpace ℝ n) : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n :=
  (ℂ ∙ complexify q)ᗮ.starProjection

/-- [proved-derived; formal-checked] The projection of Leray has norm at most one. -/
theorem norm_leray_le (q : EuclideanSpace ℝ n) : ‖leray q‖ ≤ 1 :=
  Submodule.starProjection_norm_le _

/-- [proved-derived; formal-checked] What the projection of Leray returns is across the wave
vector. -/
theorem wavePairing_leray (q : EuclideanSpace ℝ n) (v : EuclideanSpace ℂ n) :
    wavePairing q (leray q v) = 0 := by
  rw [wavePairing_eq_inner]
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp
    (Submodule.starProjection_apply_mem _ v)

/-- [proved-derived; formal-checked] With the projections of Leray the feed into a mode is across
its wave vector, so the truncated law keeps the incompressible condition's rate at zero. -/
theorem wavePairing_feed_leray {ι : Type*} [Fintype ι] (κ : ι → EuclideanSpace ℝ n)
    (a : ι → EuclideanSpace ℂ n) (k : ι) :
    wavePairing (κ k) (feed κ (fun k => leray (κ k)) a k) = 0 := by
  unfold feed
  rw [← map_smul]
  exact wavePairing_leray _ _

end Leray

/-! ## G2. The energy equality of a damped family with a conservative feed -/

section Energy

variable {ι : Type*} [Fintype ι] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {w : ι → ℝ} {ν : ℝ} {u N : ℝ → ι → E}

/-- [definition] The energy `E = (1/2) ∑ k, ‖a k‖ ^ 2`. -/
def energy (a : ι → E) : ℝ := 1 / 2 * ∑ k, ‖a k‖ ^ 2

/-- [definition] The rate the damping pays the energy at, per unit viscosity:
`∑ k, w k ^ 2 * ‖a k‖ ^ 2`. -/
def dissipationRate (w : ι → ℝ) (a : ι → E) : ℝ := ∑ k, w k ^ 2 * ‖a k‖ ^ 2

/-- [definition] A damped and fed family on `[0, ∞)`:
`d/dt u_k = -(ν * w_k ^ 2) • u_k + N_k`. No bound is asked of the feed. -/
def Evolves (w : ι → ℝ) (ν : ℝ) (u N : ℝ → ι → E) : Prop :=
  ∀ k t, 0 ≤ t →
    HasDerivWithinAt (fun s => u s k) (-(ν * w k ^ 2) • u t k + N t k) (Ici 0) t

/-- [definition] A feed that does no work on the family: `∑ k, ⟪u_k, N_k⟫ = 0`. -/
def Conservative (u N : ℝ → ι → E) : Prop :=
  ∀ t, 0 ≤ t → ∑ k, ⟪u t k, N t k⟫ = 0

omit [InnerProductSpace ℝ E] in
theorem energy_nonneg (a : ι → E) : 0 ≤ energy a :=
  mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => sq_nonneg _)

omit [InnerProductSpace ℝ E] in
theorem dissipationRate_nonneg (w : ι → ℝ) (a : ι → E) : 0 ≤ dissipationRate w a :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)

omit [Fintype ι] in
theorem Evolves.continuousOn_mode (hu : Evolves w ν u N) (k : ι) :
    ContinuousOn (fun s => u s k) (Ici 0) :=
  fun t ht => (hu k t ht).continuousWithinAt

theorem Evolves.continuousOn_dissipationRate (hu : Evolves w ν u N) :
    ContinuousOn (fun s => dissipationRate w (u s)) (Ici 0) := by
  unfold dissipationRate
  exact continuousOn_finsetSum _ fun k _ =>
    continuousOn_const.mul ((hu.continuousOn_mode k).norm.pow 2)

/-- [proved-derived; formal-checked] **The energy's rate.** Under a conservative feed the energy
has the derivative `-(ν * ∑ k, w k ^ 2 * ‖u k‖ ^ 2)` at every `0 ≤ t`. -/
theorem hasDerivWithinAt_energy (hu : Evolves w ν u N) (hN : Conservative u N) {t : ℝ}
    (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => energy (u s)) (-(ν * dissipationRate w (u t))) (Ici 0) t := by
  have h1 : ∀ k, HasDerivWithinAt (fun s => ‖u s k‖ ^ 2)
      (2 * ⟪u t k, -(ν * w k ^ 2) • u t k + N t k⟫) (Ici 0) t :=
    fun k => (hu k t ht).norm_sq
  have h2 : HasDerivWithinAt (fun s => ∑ k, ‖u s k‖ ^ 2)
      (∑ k, 2 * ⟪u t k, -(ν * w k ^ 2) • u t k + N t k⟫) (Ici 0) t :=
    HasDerivWithinAt.fun_sum fun k _ => h1 k
  have h3 := h2.const_mul (1 / 2 : ℝ)
  have hsum : ∑ k, 2 * ⟪u t k, -(ν * w k ^ 2) • u t k + N t k⟫
      = -(2 * ν * dissipationRate w (u t)) + 2 * ∑ k, ⟪u t k, N t k⟫ := by
    unfold dissipationRate
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq]
    ring
  have hval : (1 / 2 : ℝ) * (-(2 * ν * dissipationRate w (u t)) + 2 * 0)
      = -(ν * dissipationRate w (u t)) := by ring
  rw [hsum, hN t ht, hval] at h3
  exact h3

theorem Evolves.continuousOn_energy (hu : Evolves w ν u N) (hN : Conservative u N) :
    ContinuousOn (fun s => energy (u s)) (Ici 0) :=
  fun _ ht => (hasDerivWithinAt_energy hu hN ht).continuousWithinAt

/-- [proved-derived; formal-checked] Under a conservative feed the energy never rises. -/
theorem energy_antitoneOn (hν : 0 ≤ ν) (hu : Evolves w ν u N) (hN : Conservative u N) :
    AntitoneOn (fun s => energy (u s)) (Ici 0) := by
  have hd : ∀ x ∈ interior (Ici (0 : ℝ)),
      HasDerivAt (fun s => energy (u s)) (-(ν * dissipationRate w (u x))) x := by
    intro x hx
    rw [interior_Ici] at hx
    exact (hasDerivWithinAt_energy hu hN (le_of_lt hx)).hasDerivAt (Ici_mem_nhds hx)
  refine antitoneOn_of_deriv_nonpos (convex_Ici 0) (hu.continuousOn_energy hN)
    (fun x hx => (hd x hx).differentiableAt.differentiableWithinAt) (fun x hx => ?_)
  rw [(hd x hx).deriv]
  exact neg_nonpos.mpr (mul_nonneg hν (dissipationRate_nonneg _ _))

/-- [proved-derived; formal-checked] **The energy equality.**
`E t + ν * ∫ s in 0..t, ∑ k, w k ^ 2 * ‖u s k‖ ^ 2 = E 0`, at every size of the data. -/
theorem energy_add_dissipation (hu : Evolves w ν u N) (hN : Conservative u N) {t : ℝ}
    (ht : 0 ≤ t) :
    energy (u t) + ν * ∫ s in (0 : ℝ)..t, dissipationRate w (u s) = energy (u 0) := by
  have hint : IntervalIntegrable (fun s => -(ν * dissipationRate w (u s))) volume 0 t := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le ht]
    exact ((continuousOn_const.mul hu.continuousOn_dissipationRate).neg).mono
      Icc_subset_Ici_self
  have key := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht
    (f := fun s => energy (u s)) (f' := fun s => -(ν * dissipationRate w (u s)))
    ((hu.continuousOn_energy hN).mono Icc_subset_Ici_self)
    (fun x hx => (hasDerivWithinAt_energy hu hN (le_of_lt hx.1)).mono
      (fun y hy => le_trans (le_of_lt hx.1) (le_of_lt hy)))
    hint
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_const_mul] at key
  linarith

/-- [proved-derived; formal-checked] The energy never passes its opening value. -/
theorem energy_le_initial (hν : 0 ≤ ν) (hu : Evolves w ν u N) (hN : Conservative u N) {t : ℝ}
    (ht : 0 ≤ t) : energy (u t) ≤ energy (u 0) :=
  energy_antitoneOn hν hu hN (mem_Ici.mpr le_rfl) (mem_Ici.mpr ht) ht

/-- [proved-derived; formal-checked] The damping's payment is bounded by the opening energy,
whatever the size of the data. -/
theorem integral_dissipationRate_le (hu : Evolves w ν u N) (hN : Conservative u N) {t : ℝ}
    (ht : 0 ≤ t) :
    ν * ∫ s in (0 : ℝ)..t, dissipationRate w (u s) ≤ energy (u 0) := by
  have h1 := energy_add_dissipation hu hN ht
  have h2 := energy_nonneg (u t)
  linarith

/-! ### G2′. A weighted count, and the second one -/

/-- [definition] A weighted count `E_g = (1/2) ∑ k, g k * ‖a k‖ ^ 2`. -/
def weightedEnergy (g : ι → ℝ) (a : ι → E) : ℝ := 1 / 2 * ∑ k, g k * ‖a k‖ ^ 2

/-- [definition] The rate the damping pays a weighted count at, per unit viscosity:
`∑ k, g k * w k ^ 2 * ‖a k‖ ^ 2`. -/
def weightedRate (g w : ι → ℝ) (a : ι → E) : ℝ := ∑ k, g k * w k ^ 2 * ‖a k‖ ^ 2

/-- [definition] A feed that does no work in the weighted count:
`∑ k, g k * ⟪u_k, N_k⟫ = 0`. -/
def WeightedConservative (g : ι → ℝ) (u N : ℝ → ι → E) : Prop :=
  ∀ t, 0 ≤ t → ∑ k, g k * ⟪u t k, N t k⟫ = 0

omit [InnerProductSpace ℝ E] in
theorem weightedEnergy_nonneg {g : ι → ℝ} (hg : ∀ k, 0 ≤ g k) (a : ι → E) :
    0 ≤ weightedEnergy g a :=
  mul_nonneg (by norm_num)
    (Finset.sum_nonneg fun k _ => mul_nonneg (hg k) (sq_nonneg _))

omit [InnerProductSpace ℝ E] in
theorem weightedRate_nonneg {g : ι → ℝ} (hg : ∀ k, 0 ≤ g k) (w : ι → ℝ) (a : ι → E) :
    0 ≤ weightedRate g w a :=
  Finset.sum_nonneg fun k _ => mul_nonneg (mul_nonneg (hg k) (sq_nonneg _)) (sq_nonneg _)

omit [InnerProductSpace ℝ E] in
/-- The count of G2 is the weighted count at `g = 1`. -/
theorem weightedEnergy_one (a : ι → E) : weightedEnergy (fun _ => 1) a = energy a := by
  simp [weightedEnergy, energy]

omit [InnerProductSpace ℝ E] in
theorem weightedRate_one (w : ι → ℝ) (a : ι → E) :
    weightedRate (fun _ => 1) w a = dissipationRate w a := by
  simp [weightedRate, dissipationRate]

theorem weightedConservative_one :
    WeightedConservative (fun _ => 1) u N ↔ Conservative u N := by
  simp [WeightedConservative, Conservative]

/-- [proved-derived; formal-checked] **A weighted count's rate.** If the feed does no work in
the count weighted by `g`, that count has the derivative
`-(ν * ∑ k, g k * w k ^ 2 * ‖u k‖ ^ 2)` at every `0 ≤ t`. No sign is asked of `g` here. -/
theorem hasDerivWithinAt_weightedEnergy {g : ι → ℝ} (hu : Evolves w ν u N)
    (hN : WeightedConservative g u N) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => weightedEnergy g (u s)) (-(ν * weightedRate g w (u t)))
      (Ici 0) t := by
  have h1 : ∀ k, HasDerivWithinAt (fun s => g k * ‖u s k‖ ^ 2)
      (g k * (2 * ⟪u t k, -(ν * w k ^ 2) • u t k + N t k⟫)) (Ici 0) t :=
    fun k => ((hu k t ht).norm_sq).const_mul (g k)
  have h2 : HasDerivWithinAt (fun s => ∑ k, g k * ‖u s k‖ ^ 2)
      (∑ k, g k * (2 * ⟪u t k, -(ν * w k ^ 2) • u t k + N t k⟫)) (Ici 0) t :=
    HasDerivWithinAt.fun_sum fun k _ => h1 k
  have h3 := h2.const_mul (1 / 2 : ℝ)
  have hsum : ∑ k, g k * (2 * ⟪u t k, -(ν * w k ^ 2) • u t k + N t k⟫)
      = -(2 * ν * weightedRate g w (u t)) + 2 * ∑ k, g k * ⟪u t k, N t k⟫ := by
    unfold weightedRate
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq]
    ring
  have hval : (1 / 2 : ℝ) * (-(2 * ν * weightedRate g w (u t)) + 2 * 0)
      = -(ν * weightedRate g w (u t)) := by ring
  rw [hsum, hN t ht, hval] at h3
  exact h3

/-- [proved-derived; formal-checked] A conserved weighted count with nonnegative weights never
rises. The count of G2 is `g = 1`. -/
theorem weightedEnergy_antitoneOn {g : ι → ℝ} (hν : 0 ≤ ν) (hg : ∀ k, 0 ≤ g k)
    (hu : Evolves w ν u N) (hN : WeightedConservative g u N) :
    AntitoneOn (fun s => weightedEnergy g (u s)) (Ici 0) := by
  have hd : ∀ x ∈ interior (Ici (0 : ℝ)),
      HasDerivAt (fun s => weightedEnergy g (u s)) (-(ν * weightedRate g w (u x))) x := by
    intro x hx
    rw [interior_Ici] at hx
    exact (hasDerivWithinAt_weightedEnergy hu hN (le_of_lt hx)).hasDerivAt (Ici_mem_nhds hx)
  refine antitoneOn_of_deriv_nonpos (convex_Ici 0)
    (fun _ ht => (hasDerivWithinAt_weightedEnergy hu hN ht).continuousWithinAt)
    (fun x hx => (hd x hx).differentiableAt.differentiableWithinAt) (fun x hx => ?_)
  rw [(hd x hx).deriv]
  exact neg_nonpos.mpr (mul_nonneg hν (weightedRate_nonneg hg _ _))

/-- [proved-derived; formal-checked] A conserved weighted count never passes its opening
value. -/
theorem weightedEnergy_le_initial {g : ι → ℝ} (hν : 0 ≤ ν) (hg : ∀ k, 0 ≤ g k)
    (hu : Evolves w ν u N) (hN : WeightedConservative g u N) {t : ℝ} (ht : 0 ≤ t) :
    weightedEnergy g (u t) ≤ weightedEnergy g (u 0) :=
  weightedEnergy_antitoneOn hν hg hu hN (mem_Ici.mpr le_rfl) (mem_Ici.mpr ht) ht

omit [InnerProductSpace ℝ E] in
/-- [proved-derived; formal-checked] Cauchy-Schwarz between the critical norm and the second
count (`g k = w k ^ 2`): `X = ∑ k, w k ^ (-2) * (w k * ‖a k‖)`. -/
theorem criticalNorm_le_sqrt_mul_sqrt (hw : ∀ k, 0 < w k) (a : ι → E) :
    criticalNorm w a ≤
      √(∑ k, w k ^ (-4 : ℤ)) * √(2 * weightedEnergy (fun k => w k ^ 2) a) := by
  have h1 : criticalNorm w a = ∑ k, w k ^ (-2 : ℤ) * (w k * ‖a k‖) := by
    unfold criticalNorm
    refine Finset.sum_congr rfl fun k _ => ?_
    have hk := (hw k).ne'
    rw [zpow_neg, zpow_ofNat]
    field_simp
  have h2 : ∑ k, (w k ^ (-2 : ℤ)) ^ 2 = ∑ k, w k ^ (-4 : ℤ) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← zpow_natCast, ← zpow_mul]
    norm_num
  have h3 : ∑ k, (w k * ‖a k‖) ^ 2 = 2 * weightedEnergy (fun k => w k ^ 2) a := by
    unfold weightedEnergy
    rw [← mul_assoc, show (2 : ℝ) * (1 / 2) = 1 by norm_num, one_mul]
    exact Finset.sum_congr rfl fun k _ => mul_pow _ _ _
  rw [h1, ← h2, ← h3]
  exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _

/-- [proved-derived; formal-checked] **Where the feed conserves the second count the critical
reading is bounded at every size of the data.** With `g k = w k ^ 2` (the enstrophy, which the
fluid's feed conserves in two dimensions), no feed bound and no smallness:
`X t ≤ √(∑ k, w k ^ (-4)) * √(2 * E_g 0)` at every `0 ≤ t`. -/
theorem critical_le_of_second_count (hw : ∀ k, 0 < w k) (hν : 0 ≤ ν) (hu : Evolves w ν u N)
    (hN : WeightedConservative (fun k => w k ^ 2) u N) {t : ℝ} (ht : 0 ≤ t) :
    criticalNorm w (u t) ≤
      √(∑ k, w k ^ (-4 : ℤ)) * √(2 * weightedEnergy (fun k => w k ^ 2) (u 0)) := by
  refine (criticalNorm_le_sqrt_mul_sqrt hw (u t)).trans ?_
  refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (Real.sqrt_nonneg _)
  have := weightedEnergy_le_initial hν (fun k => sq_nonneg (w k)) hu hN ht
  linarith

omit [Fintype ι] in
/-- A comb system on a real inner product space is a damped and fed family. -/
theorem _root_.Holonics.Fluid.LaminarClass.CombSystem.evolves' {c : ℝ}
    {T : ι → Finset (ι × ι)} (h : CombSystem w ν c T u N) : Evolves w ν u N :=
  h.evolves

end Energy

/-! ### With the projections of Leray the incompressible condition is kept -/

section Kept

variable {ι : Type*} [Fintype ι] {n : Type*} [Fintype n]

/-- [proved-derived; formal-checked] A damped amplitude whose feed is across a wave vector, and
which opens across it, stays across it: the pairing `y = q · b` obeys `y' = -c y`, and its
energy, zero at the opening, never rises. -/
theorem wavePairing_eq_zero_of_evolves {q : EuclideanSpace ℝ n} {c : ℝ} (hc : 0 ≤ c)
    {b F : ℝ → EuclideanSpace ℂ n}
    (hb : ∀ t, 0 ≤ t → HasDerivWithinAt b (-c • b t + F t) (Ici 0) t)
    (hF : ∀ t, 0 ≤ t → wavePairing q (F t) = 0) (h0 : wavePairing q (b 0) = 0) {t : ℝ}
    (ht : 0 ≤ t) : wavePairing q (b t) = 0 := by
  let L : EuclideanSpace ℂ n →L[ℝ] ℂ := (innerSL ℂ (complexify q)).restrictScalars ℝ
  have hLw : ∀ v, L v = wavePairing q v := fun v => (wavePairing_eq_inner q v).symm
  have hEv : Evolves (fun _ : Unit => (1 : ℝ)) c (fun r _ => L (b r)) (fun _ _ => (0 : ℂ)) := by
    intro _ s hs
    have h1 := L.hasFDerivAt.comp_hasDerivWithinAt s (hb s hs)
    have h2 : L (-c • b s + F s) = -(c * (1 : ℝ) ^ 2) • L (b s) + 0 := by
      rw [map_add, map_smul, hLw (F s), hF s hs]
      simp
    rw [h2] at h1
    exact h1
  have hCons : Conservative (fun r (_ : Unit) => L (b r)) (fun _ _ => (0 : ℂ)) :=
    fun s _ => by simp
  have hE := energy_le_initial hc hEv hCons ht
  simp only [energy, Finset.univ_unique, Finset.sum_singleton] at hE
  rw [hLw, hLw, h0, norm_zero] at hE
  have h3 : ‖wavePairing q (b t)‖ ^ 2 ≤ 0 := by linarith
  have h4 : ‖wavePairing q (b t)‖ ^ 2 = 0 := le_antisymm h3 (sq_nonneg _)
  exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h4)

variable {κ : ι → EuclideanSpace ℝ n} {ν : ℝ} {a : ℝ → ι → EuclideanSpace ℂ n}

/-- [proved-derived; formal-checked] **With the projections of Leray the opening state decides
the incompressible condition.** Distinct nonzero wave vectors, amplitudes across them at the
opening and the truncated law make a truncation. -/
theorem Truncation.of_leray (hκ : Function.Injective κ) (hκ0 : ∀ k, κ k ≠ 0) (hν : 0 < ν)
    (h0 : ∀ k, wavePairing (κ k) (a 0 k) = 0)
    (ha : ∀ k t, 0 ≤ t → HasDerivWithinAt (fun s => a s k)
      (-(ν * ‖κ k‖ ^ 2) • a t k + feed κ (fun k => leray (κ k)) (a t) k) (Ici 0) t) :
    Truncation κ ν (fun k => leray (κ k)) a where
  wave_injective := hκ
  wave_ne_zero := hκ0
  viscosity_pos := hν
  projection_le k := norm_leray_le _
  incompressible t ht k :=
    wavePairing_eq_zero_of_evolves (c := ν * ‖κ k‖ ^ 2) (by positivity)
      (b := fun s => a s k) (F := fun s => feed κ (fun k => leray (κ k)) (a s) k)
      (fun s hs => ha k s hs) (fun s _ => wavePairing_feed_leray κ (a s) k) (h0 k) ht
  evolves := ha

/-- [proved-derived; formal-checked] **The laminar class of the truncated fluid, from its opening
state and its law alone.** With the projections of Leray: distinct nonzero wave vectors,
amplitudes across them at the opening, the truncated law on `[0, ∞)` and
`∑ k, ‖a 0 k‖ / ‖κ k‖ < ν` give `∑ k, ‖a t k‖ / ‖κ k‖ ≤ ∑ k, ‖a 0 k‖ / ‖κ k‖` at every
`0 ≤ t`, whatever the set of modes. -/
theorem leray_truncation_critical_le_initial (hκ : Function.Injective κ) (hκ0 : ∀ k, κ k ≠ 0)
    (hν : 0 < ν) (h0 : ∀ k, wavePairing (κ k) (a 0 k) = 0)
    (ha : ∀ k t, 0 ≤ t → HasDerivWithinAt (fun s => a s k)
      (-(ν * ‖κ k‖ ^ 2) • a t k + feed κ (fun k => leray (κ k)) (a t) k) (Ici 0) t)
    (hX : criticalNorm (fun k => ‖κ k‖) (a 0) < ν) {t : ℝ} (ht : 0 ≤ t) :
    criticalNorm (fun k => ‖κ k‖) (a t) ≤ criticalNorm (fun k => ‖κ k‖) (a 0) :=
  (Truncation.of_leray hκ hκ0 hν h0 ha).critical_le_initial hX ht

end Kept

/-! ## G4. Continuation: the critical reading leaves only through the dissipation integral -/

section Continuation

variable {ι : Type*} [Fintype ι] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {w : ι → ℝ} {ν c : ℝ} {T : ι → Finset (ι × ι)} {u N : ℝ → ι → E}

/-- [proved-derived; formal-checked] **Continuation, with no smallness.** For every comb system,
whatever its coherence constant and the size of its data,
`X t ≤ X 0 * exp (c * ∫ s in 0..t, Y s)` at every `0 ≤ t`: the slope bound
`D⁺X ≤ -(ν - c X) Y ≤ c X Y` and Grönwall's argument on `X * exp (-c ∫ Y)`. The critical reading
can leave every bound only through an unbounded dissipation integral. -/
theorem _root_.Holonics.Fluid.LaminarClass.CombSystem.critical_le_mul_exp
    (h : CombSystem w ν c T u N) {t : ℝ} (ht : 0 ≤ t) :
    criticalNorm w (u t) ≤ criticalNorm w (u 0) *
      Real.exp (c * ∫ s in (0 : ℝ)..t, dissipationNorm w (u s)) := by
  have hν := h.viscosity_pos
  have hYc := h.continuousOn_dissipation
  have hYint : ∀ x, 0 ≤ x →
      IntervalIntegrable (fun s => dissipationNorm w (u s)) volume 0 x := by
    intro x hx
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hx]
    exact hYc.mono Icc_subset_Ici_self
  have hprim_cont :
      ContinuousOn (fun x => ∫ s in (0 : ℝ)..x, dissipationNorm w (u s)) (Icc 0 t) := by
    have hI : IntegrableOn (fun s => dissipationNorm w (u s)) (uIcc 0 t) volume := by
      rw [uIcc_of_le ht]
      exact (hYc.mono Icc_subset_Ici_self).integrableOn_Icc
    have := intervalIntegral.continuousOn_primitive_interval hI
    rwa [uIcc_of_le ht] at this
  have hprim_deriv : ∀ x, 0 ≤ x →
      HasDerivWithinAt (fun y => ∫ s in (0 : ℝ)..y, dissipationNorm w (u s))
        (dissipationNorm w (u x)) (Ici x) x := by
    intro x hx
    have hYx : ContinuousOn (fun s => dissipationNorm w (u s)) (Ici x) :=
      hYc.mono (Ici_subset_Ici.mpr hx)
    refine intervalIntegral.integral_hasDerivWithinAt_right (hYint x hx)
      (s := Ici x) (t := Ioi x) ?_ ?_
    · exact (hYx.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Ici x).filter_mono
        (nhdsWithin_mono x Ioi_subset_Ici_self)
    · exact (hYx x (mem_Ici.mpr le_rfl)).mono Ioi_subset_Ici_self
  have key := image_le_of_deriv_right_le_deriv_boundary
    (f := fun s => criticalNorm w (u s) *
      Real.exp (-c * ∫ r in (0 : ℝ)..s, dissipationNorm w (u r)))
    (f' := fun x => criticalSlope w ν u N x *
        Real.exp (-c * ∫ r in (0 : ℝ)..x, dissipationNorm w (u r))
      + criticalNorm w (u x) *
        (Real.exp (-c * ∫ r in (0 : ℝ)..x, dissipationNorm w (u r)) *
          (-c * dissipationNorm w (u x))))
    (a := 0) (b := t)
    (B := fun _ => criticalNorm w (u 0)) (B' := fun _ => 0)
    ((h.continuousOn_critical.mono Icc_subset_Ici_self).mul
      (Real.continuous_exp.comp_continuousOn (continuousOn_const.mul hprim_cont)))
    (fun x hx => (h.hasDerivWithinAt_critical hx.1).mul
      (((hprim_deriv x hx.1).const_mul (-c)).exp))
    (by simp)
    continuousOn_const
    (fun x _ => hasDerivWithinAt_const _ _ _)
    (by
      intro x hx
      have hslope := h.criticalSlope_le hx.1
      have hY : 0 ≤ dissipationNorm w (u x) :=
        dissipationNorm_nonneg (fun k => (h.weight_pos k).le) _
      have he := Real.exp_pos (-c * ∫ r in (0 : ℝ)..x, dissipationNorm w (u r))
      have h1 : criticalSlope w ν u N x
          - c * criticalNorm w (u x) * dissipationNorm w (u x) ≤ 0 := by
        have h2 : -(ν - c * criticalNorm w (u x)) * dissipationNorm w (u x)
            = -(ν * dissipationNorm w (u x))
              + c * criticalNorm w (u x) * dissipationNorm w (u x) := by ring
        have h3 := mul_nonneg hν.le hY
        linarith
      show criticalSlope w ν u N x *
          Real.exp (-c * ∫ r in (0 : ℝ)..x, dissipationNorm w (u r))
        + criticalNorm w (u x) *
          (Real.exp (-c * ∫ r in (0 : ℝ)..x, dissipationNorm w (u r)) *
            (-c * dissipationNorm w (u x))) ≤ 0
      calc criticalSlope w ν u N x *
            Real.exp (-c * ∫ r in (0 : ℝ)..x, dissipationNorm w (u r))
          + criticalNorm w (u x) *
            (Real.exp (-c * ∫ r in (0 : ℝ)..x, dissipationNorm w (u r)) *
              (-c * dissipationNorm w (u x)))
          = Real.exp (-c * ∫ r in (0 : ℝ)..x, dissipationNorm w (u r)) *
            (criticalSlope w ν u N x
              - c * criticalNorm w (u x) * dissipationNorm w (u x)) := by ring
        _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos he.le h1)
  have hk : criticalNorm w (u t) *
      Real.exp (-c * ∫ r in (0 : ℝ)..t, dissipationNorm w (u r)) ≤ criticalNorm w (u 0) :=
    key (right_mem_Icc.mpr ht)
  have hmul := mul_le_mul_of_nonneg_right hk
    (Real.exp_pos (c * ∫ r in (0 : ℝ)..t, dissipationNorm w (u r))).le
  rw [mul_assoc, ← Real.exp_add, neg_mul, neg_add_cancel, Real.exp_zero, mul_one] at hmul
  exact hmul

/-- [proved-derived; formal-checked] While the dissipation integral stays under `M` the critical
reading stays under `X 0 * exp (c * M)`: the comb's form of a continuation criterion. -/
theorem _root_.Holonics.Fluid.LaminarClass.CombSystem.critical_le_of_integral_le
    (h : CombSystem w ν c T u N) {t M : ℝ} (ht : 0 ≤ t)
    (hM : ∫ s in (0 : ℝ)..t, dissipationNorm w (u s) ≤ M) :
    criticalNorm w (u t) ≤ criticalNorm w (u 0) * Real.exp (c * M) := by
  refine (h.critical_le_mul_exp ht).trans ?_
  refine mul_le_mul_of_nonneg_left ?_
    (criticalNorm_nonneg (fun k => (h.weight_pos k).le) _)
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hM h.coherence_nonneg)

/-- [proved-derived; formal-checked] The continuation bound on a complex amplitude space. -/
theorem _root_.Holonics.Fluid.LaminarClass.CombSystem.critical_le_mul_exp_complex
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {u N : ℝ → ι → F}
    (h : CombSystem w ν c T u N) {t : ℝ} (ht : 0 ≤ t) :
    criticalNorm w (u t) ≤ criticalNorm w (u 0) *
      Real.exp (c * ∫ s in (0 : ℝ)..t, dissipationNorm w (u s)) := by
  let _ : InnerProductSpace ℝ F := InnerProductSpace.complexToReal
  exact CombSystem.critical_le_mul_exp h ht

/-- [proved-derived; formal-checked] **Continuation for the truncated fluid**, at every size of
the data and every truncation alike: `X t ≤ X 0 * exp (∫ s in 0..t, Y s)`, with
`Y = ∑ k, ‖κ k‖ * ‖a k‖`, the amplitude norm of the gradient. -/
theorem Truncation.critical_le_mul_exp {n : Type*} [Fintype n]
    {κ : ι → EuclideanSpace ℝ n} {P : ι → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n}
    {a : ℝ → ι → EuclideanSpace ℂ n} (h : Truncation κ ν P a) {t : ℝ} (ht : 0 ≤ t) :
    criticalNorm (fun k => ‖κ k‖) (a t) ≤ criticalNorm (fun k => ‖κ k‖) (a 0) *
      Real.exp (∫ s in (0 : ℝ)..t, dissipationNorm (fun k => ‖κ k‖) (a s)) := by
  have := h.combSystem.critical_le_mul_exp_complex ht
  rwa [one_mul] at this

end Continuation

/-! ## G3. The threshold is attained inside the comb class -/

section Sharpness

variable {ι : Type*} [Fintype ι] [AddCommGroup ι]

/-- The pair `(p, k - p)`, as an embedding of the modes. -/
def pairTo (k : ι) : ι ↪ ι × ι := ⟨fun p => (p, k - p), fun _ _ h => congrArg Prod.fst h⟩

/-- [definition] The comb of a finite additive group: the pairs `(p, k - p)`, that is the pairs
with `p + q = k`. -/
def sumTriads (k : ι) : Finset (ι × ι) := Finset.univ.map (pairTo k)

theorem mem_sumTriads {k : ι} {pq : ι × ι} : pq ∈ sumTriads k ↔ pq.1 + pq.2 = k := by
  unfold sumTriads
  rw [Finset.mem_map]
  constructor
  · rintro ⟨p, -, rfl⟩
    show p + (k - p) = k
    abel
  · intro h
    refine ⟨pq.1, Finset.mem_univ _, ?_⟩
    have h2 : k - pq.1 = pq.2 := by
      rw [← h]
      abel
    exact Prod.ext rfl h2

theorem sumTriads_disjoint (k k' : ι) (h : k ≠ k') :
    Disjoint (sumTriads k) (sumTriads k') := by
  rw [Finset.disjoint_left]
  intro pq h1 h2
  rw [mem_sumTriads] at h1 h2
  exact h (h1.symm.trans h2)

theorem card_sumTriads (k : ι) : (sumTriads k).card = Fintype.card ι := by
  unfold sumTriads
  rw [Finset.card_map, Finset.card_univ]

/-- [definition] The coherent feed: every triad of `k` feeds it with the same sign. -/
def coherentFeed (ω : ℝ) (a : ι → ℝ) (k : ι) : ℝ := ω * ∑ pq ∈ sumTriads k, a pq.1 * a pq.2

/-- [proved-derived; formal-checked] The coherent feed meets the comb's feed bound with weight
`ω` and coherence constant one. -/
theorem norm_coherentFeed_le {ω : ℝ} (hω : 0 ≤ ω) (a : ι → ℝ) (k : ι) :
    ‖coherentFeed ω a k‖ ≤ 1 * ω * ∑ pq ∈ sumTriads k, ‖a pq.1‖ * ‖a pq.2‖ := by
  unfold coherentFeed
  rw [norm_mul, Real.norm_of_nonneg hω, one_mul]
  refine mul_le_mul_of_nonneg_left ?_ hω
  calc ‖∑ pq ∈ sumTriads k, a pq.1 * a pq.2‖
      ≤ ∑ pq ∈ sumTriads k, ‖a pq.1 * a pq.2‖ := norm_sum_le _ _
    _ = ∑ pq ∈ sumTriads k, ‖a pq.1‖ * ‖a pq.2‖ :=
        Finset.sum_congr rfl fun pq _ => norm_mul _ _

/-- [proved-derived; formal-checked] On nonnegative amplitudes the coherent feed meets the bound
with equality: nothing cancels. -/
theorem norm_coherentFeed_eq_of_nonneg {ω : ℝ} (hω : 0 ≤ ω) {a : ι → ℝ} (ha : ∀ k, 0 ≤ a k)
    (k : ι) :
    ‖coherentFeed ω a k‖ = 1 * ω * ∑ pq ∈ sumTriads k, ‖a pq.1‖ * ‖a pq.2‖ := by
  unfold coherentFeed
  have hs : 0 ≤ ∑ pq ∈ sumTriads k, a pq.1 * a pq.2 :=
    Finset.sum_nonneg fun pq _ => mul_nonneg (ha _) (ha _)
  rw [Real.norm_of_nonneg (mul_nonneg hω hs), one_mul]
  congr 1
  exact Finset.sum_congr rfl fun pq _ => by
    rw [Real.norm_of_nonneg (ha _), Real.norm_of_nonneg (ha _)]

/-- [proved-derived; formal-checked] On positive amplitudes the coherent feed is positive at every
mode. -/
theorem coherentFeed_pos {ω : ℝ} (hω : 0 < ω) {a : ι → ℝ} (ha : ∀ k, 0 < a k) (k : ι) :
    0 < coherentFeed ω a k := by
  unfold coherentFeed
  refine mul_pos hω (Finset.sum_pos (fun pq _ => mul_pos (ha _) (ha _)) ?_)
  rw [← Finset.card_pos, card_sumTriads]
  exact Fintype.card_pos

/-- [proved-derived; formal-checked] The coherent feed does work on every positive state: it is
not the feed of G2, and a comb system that carries it is no fluid. -/
theorem coherentFeed_work_pos {ω : ℝ} (hω : 0 < ω) {a : ι → ℝ} (ha : ∀ k, 0 < a k) :
    0 < ∑ k, ⟪a k, coherentFeed ω a k⟫ := by
  refine Finset.sum_pos (fun k _ => ?_) Finset.univ_nonempty
  rw [Real.inner_apply]
  exact mul_pos (ha k) (coherentFeed_pos hω ha k)

/-- The coherent feed of a uniform state. -/
theorem coherentFeed_const (ω x : ℝ) (k : ι) :
    coherentFeed ω (fun _ : ι => x) k = ω * (Fintype.card ι * x ^ 2) := by
  unfold coherentFeed
  rw [Finset.sum_const, card_sumTriads, nsmul_eq_mul, sq]

omit [AddCommGroup ι] in
/-- The critical norm of a uniform state. -/
theorem criticalNorm_const (ω x : ℝ) :
    criticalNorm (fun _ : ι => ω) (fun _ : ι => x) = Fintype.card ι * |x| / ω := by
  unfold criticalNorm
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Real.norm_eq_abs, mul_div_assoc]

omit [AddCommGroup ι] in
/-- The dissipation norm of a uniform state. -/
theorem dissipationNorm_const (ω x : ℝ) :
    dissipationNorm (fun _ : ι => ω) (fun _ : ι => x) = Fintype.card ι * (ω * |x|) := by
  unfold dissipationNorm
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Real.norm_eq_abs]

theorem card_pos' : (0 : ℝ) < Fintype.card ι := by
  exact_mod_cast Fintype.card_pos

/-- [proved-derived; formal-checked] A uniform state `u t k = φ t` under the coherent feed is a
comb system when `φ' = -(ν ω²) φ + ω m φ²` on `[0, ∞)`, `m` the number of modes. -/
theorem uniform_combSystem {ω ν : ℝ} (hω : 0 < ω) (hν : 0 < ν) {φ : ℝ → ℝ}
    (hφ : ∀ t, 0 ≤ t → HasDerivWithinAt φ
      (-(ν * ω ^ 2) * φ t + ω * (Fintype.card ι * φ t ^ 2)) (Ici 0) t) :
    CombSystem (fun _ : ι => ω) ν 1 sumTriads (fun t _ => φ t)
      (fun t => coherentFeed ω fun _ => φ t) where
  weight_pos _ := hω
  viscosity_pos := hν
  coherence_nonneg := zero_le_one
  fibres_disjoint := sumTriads_disjoint
  evolves k t ht := by
    have h := hφ t ht
    rw [← coherentFeed_const ω (φ t) k, ← smul_eq_mul (-(ν * ω ^ 2)) (φ t)] at h
    exact h
  feed_le _ _ k := norm_coherentFeed_le hω.le _ k

/-! ### The constant state on the threshold -/

/-- [definition] The constant state on the threshold: every mode at `ν ω / m`. -/
def constantState (ι : Type*) [Fintype ι] (ν ω : ℝ) : ι → ℝ := fun _ => ν * ω / Fintype.card ι

/-- [proved-derived; formal-checked] The constant state is a comb system: at `ν ω / m` the
damping and the coherent feed balance. -/
theorem constant_combSystem {ω ν : ℝ} (hω : 0 < ω) (hν : 0 < ν) :
    CombSystem (fun _ : ι => ω) ν 1 sumTriads (fun _ => constantState ι ν ω)
      (fun _ => coherentFeed ω (constantState ι ν ω)) := by
  refine uniform_combSystem (ι := ι) hω hν (φ := fun _ => ν * ω / Fintype.card ι)
    (fun t _ => ?_)
  have hm : (Fintype.card ι : ℝ) ≠ 0 := (card_pos' (ι := ι)).ne'
  have h0 : -(ν * ω ^ 2) * (ν * ω / Fintype.card ι)
      + ω * (Fintype.card ι * (ν * ω / Fintype.card ι) ^ 2) = 0 := by
    field_simp
    ring
  rw [h0]
  exact hasDerivWithinAt_const _ _ _

/-- [proved-derived; formal-checked] The constant state sits on the threshold: `X = ν`. -/
theorem criticalNorm_constantState {ω ν : ℝ} (hω : 0 < ω) (hν : 0 < ν) :
    criticalNorm (fun _ : ι => ω) (constantState ι ν ω) = ν := by
  have hm : (0 : ℝ) < Fintype.card ι := card_pos'
  unfold constantState
  rw [criticalNorm_const, abs_of_pos (div_pos (mul_pos hν hω) hm)]
  field_simp

/-- [proved-derived; formal-checked] The constant state dissipates at the constant rate
`Y = ν ω²`. -/
theorem dissipationNorm_constantState {ω ν : ℝ} (hω : 0 < ω) (hν : 0 < ν) :
    dissipationNorm (fun _ : ι => ω) (constantState ι ν ω) = ν * ω ^ 2 := by
  have hm : (0 : ℝ) < Fintype.card ι := card_pos'
  unfold constantState
  rw [dissipationNorm_const, abs_of_pos (div_pos (mul_pos hν hω) hm)]
  field_simp

/-- [proved-derived; formal-checked] The dissipation the constant state has paid by `t` is
`t * (ν ω²)`. -/
theorem integral_dissipation_constantState {ω ν : ℝ} (hω : 0 < ω) (hν : 0 < ν) (t : ℝ) :
    ∫ _ in (0 : ℝ)..t, dissipationNorm (fun _ : ι => ω) (constantState ι ν ω)
      = t * (ν * ω ^ 2) := by
  rw [intervalIntegral.integral_const, dissipationNorm_constantState hω hν, sub_zero,
    smul_eq_mul]

/-- [proved-derived; formal-checked] **The threshold is attained.** At every positive viscosity
and weight there is a comb system with coherence constant one that sits on `c * X = ν` for all
time and whose dissipation integral passes every bound. The laminar class's bound
`∫ Y ≤ X 0 / (ν - c * X 0)` has no counterpart on the threshold. -/
theorem threshold_attained {ω ν : ℝ} (hω : 0 < ω) (hν : 0 < ν) :
    ∃ u N : ℝ → ι → ℝ, CombSystem (fun _ : ι => ω) ν 1 sumTriads u N ∧
      (∀ t, 1 * criticalNorm (fun _ : ι => ω) (u t) = ν) ∧
      ∀ C : ℝ, ∃ t, 0 ≤ t ∧
        C < ∫ s in (0 : ℝ)..t, dissipationNorm (fun _ : ι => ω) (u s) := by
  refine ⟨fun _ => constantState ι ν ω, fun _ => coherentFeed ω (constantState ι ν ω),
    constant_combSystem hω hν, fun _ => by rw [one_mul, criticalNorm_constantState hω hν],
    fun C => ?_⟩
  have hY : 0 < ν * ω ^ 2 := mul_pos hν (pow_pos hω 2)
  refine ⟨(|C| + 1) / (ν * ω ^ 2), div_nonneg (by positivity) hY.le, ?_⟩
  rw [integral_dissipation_constantState hω hν, div_mul_cancel₀ _ hY.ne']
  linarith [le_abs_self C]

/-- [proved-derived; formal-checked] The constant state's feed is not conservative: the energy
count of G2 does not hold on the comb system that attains the threshold. -/
theorem constantState_not_conservative {ω ν : ℝ} (hω : 0 < ω) (hν : 0 < ν) :
    ¬ Conservative (fun _ : ℝ => constantState ι ν ω)
      (fun _ => coherentFeed ω (constantState ι ν ω)) := by
  intro h
  have hpos : ∀ k : ι, 0 < constantState ι ν ω k := fun _ =>
    div_pos (mul_pos hν hω) card_pos'
  exact (coherentFeed_work_pos hω hpos).ne' (h 0 le_rfl)

/-- [proved-derived; formal-checked] The threshold is attained on `ZMod m`, the comb
`{(p, q) | p + q = k}` of the residues modulo any `m ≥ 1`. -/
theorem threshold_attained_zmod (m : ℕ) [NeZero m] {ω ν : ℝ} (hω : 0 < ω) (hν : 0 < ν) :
    ∃ u N : ℝ → ZMod m → ℝ, CombSystem (fun _ : ZMod m => ω) ν 1 sumTriads u N ∧
      (∀ t, 1 * criticalNorm (fun _ : ZMod m => ω) (u t) = ν) ∧
      ∀ C : ℝ, ∃ t, 0 ≤ t ∧
        C < ∫ s in (0 : ℝ)..t, dissipationNorm (fun _ : ZMod m => ω) (u s) :=
  threshold_attained hω hν

end Sharpness

/-! ### The closed form above and below the threshold -/

section Logistic

/-- [definition] The closed form of the uniform state's critical norm:
`X t = ν / (1 - (1 - ν / X₀) * exp (ν ω² t))`. -/
def logistic (ν ω X₀ t : ℝ) : ℝ := ν / (1 - (1 - ν / X₀) * Real.exp (ν * ω ^ 2 * t))

/-- [definition] The time at which the closed form leaves every bound, for `X₀ > ν`. -/
def blowupTime (ν ω X₀ : ℝ) : ℝ := Real.log (X₀ / (X₀ - ν)) / (ν * ω ^ 2)

variable {ν ω X₀ : ℝ}

/-- The closed form opens at `X₀`. -/
theorem logistic_zero (hν : ν ≠ 0) : logistic ν ω X₀ 0 = X₀ := by
  unfold logistic
  rw [mul_zero, Real.exp_zero, mul_one, sub_sub_cancel, div_div_eq_mul_div, mul_comm,
    mul_div_assoc, div_self hν, mul_one]

/-- [proved-derived; formal-checked] Wherever its denominator is not zero the closed form obeys
`X' = ω² X (X - ν)`, the comb's law of a uniform state read in the critical norm. -/
theorem hasDerivAt_logistic (ν ω X₀ : ℝ) {t : ℝ}
    (hg : 1 - (1 - ν / X₀) * Real.exp (ν * ω ^ 2 * t) ≠ 0) :
    HasDerivAt (logistic ν ω X₀)
      (ω ^ 2 * logistic ν ω X₀ t * (logistic ν ω X₀ t - ν)) t := by
  have h1 : HasDerivAt (fun s => Real.exp (ν * ω ^ 2 * s))
      (Real.exp (ν * ω ^ 2 * t) * (ν * ω ^ 2)) t := by
    simpa using ((hasDerivAt_id t).const_mul (ν * ω ^ 2)).exp
  have h2 : HasDerivAt (fun s => 1 - (1 - ν / X₀) * Real.exp (ν * ω ^ 2 * s))
      (-((1 - ν / X₀) * (Real.exp (ν * ω ^ 2 * t) * (ν * ω ^ 2)))) t := by
    simpa using (h1.const_mul (1 - ν / X₀)).const_sub 1
  have h3 := (hasDerivAt_const t ν).div h2 hg
  refine h3.congr_deriv ?_
  unfold logistic
  rw [← mul_assoc (1 - ν / X₀)]
  generalize (1 - ν / X₀) * Real.exp (ν * ω ^ 2 * t) = e at hg ⊢
  field_simp
  ring

/-- Before the blow-up time the denominator is positive. -/
theorem denominator_pos (hν : 0 < ν) (hω : 0 < ω) (hX : ν < X₀) {t : ℝ}
    (ht : t < blowupTime ν ω X₀) :
    0 < 1 - (1 - ν / X₀) * Real.exp (ν * ω ^ 2 * t) := by
  have hX0 : 0 < X₀ := hν.trans hX
  have hd : 0 < X₀ - ν := sub_pos.mpr hX
  have hl : 0 < ν * ω ^ 2 := mul_pos hν (pow_pos hω 2)
  have h1 : ν * ω ^ 2 * t < Real.log (X₀ / (X₀ - ν)) := by
    unfold blowupTime at ht
    rw [lt_div_iff₀ hl] at ht
    linarith
  have h2 : Real.exp (ν * ω ^ 2 * t) < X₀ / (X₀ - ν) := by
    have := Real.exp_lt_exp.mpr h1
    rwa [Real.exp_log (div_pos hX0 hd)] at this
  have h3 : 1 - ν / X₀ = (X₀ - ν) / X₀ := by
    field_simp
  have h4 : (1 - ν / X₀) * Real.exp (ν * ω ^ 2 * t) < (1 - ν / X₀) * (X₀ / (X₀ - ν)) :=
    mul_lt_mul_of_pos_left h2 (by rw [h3]; exact div_pos hd hX0)
  have h5 : (1 - ν / X₀) * (X₀ / (X₀ - ν)) = 1 := by
    rw [h3]
    field_simp
  linarith

/-- At the blow-up time the denominator is zero. -/
theorem denominator_blowupTime (hν : 0 < ν) (hω : 0 < ω) (hX : ν < X₀) :
    1 - (1 - ν / X₀) * Real.exp (ν * ω ^ 2 * blowupTime ν ω X₀) = 0 := by
  have hX0 : 0 < X₀ := hν.trans hX
  have hd : 0 < X₀ - ν := sub_pos.mpr hX
  have hl : 0 < ν * ω ^ 2 := mul_pos hν (pow_pos hω 2)
  unfold blowupTime
  rw [mul_div_cancel₀ _ hl.ne', Real.exp_log (div_pos hX0 hd)]
  field_simp
  ring

/-- The blow-up time is positive. -/
theorem blowupTime_pos (hν : 0 < ν) (hω : 0 < ω) (hX : ν < X₀) : 0 < blowupTime ν ω X₀ := by
  have hd : 0 < X₀ - ν := sub_pos.mpr hX
  unfold blowupTime
  refine div_pos (Real.log_pos ?_) (mul_pos hν (pow_pos hω 2))
  rw [lt_div_iff₀ hd]
  linarith

/-- [proved-derived; formal-checked] Above the threshold the closed form stays above it. -/
theorem lt_logistic (hν : 0 < ν) (hω : 0 < ω) (hX : ν < X₀) {t : ℝ}
    (ht : t < blowupTime ν ω X₀) : ν < logistic ν ω X₀ t := by
  have hg := denominator_pos hν hω hX ht
  have hX0 : 0 < X₀ := hν.trans hX
  have hβ : 0 < 1 - ν / X₀ := by
    rw [sub_pos, div_lt_one hX0]
    exact hX
  unfold logistic
  rw [lt_div_iff₀ hg]
  nlinarith [mul_pos hβ (Real.exp_pos (ν * ω ^ 2 * t))]

/-- [proved-derived; formal-checked] Above the threshold the closed form rises strictly up to
the blow-up time. -/
theorem logistic_strictMonoOn (hν : 0 < ν) (hω : 0 < ω) (hX : ν < X₀) :
    StrictMonoOn (logistic ν ω X₀) (Iio (blowupTime ν ω X₀)) := by
  intro s _ t ht hst
  have hgt := denominator_pos hν hω hX ht
  have hX0 : 0 < X₀ := hν.trans hX
  have hβ : 0 < 1 - ν / X₀ := by
    rw [sub_pos, div_lt_one hX0]
    exact hX
  have hl : 0 < ν * ω ^ 2 := mul_pos hν (pow_pos hω 2)
  have hexp : Real.exp (ν * ω ^ 2 * s) < Real.exp (ν * ω ^ 2 * t) :=
    Real.exp_lt_exp.mpr (mul_lt_mul_of_pos_left hst hl)
  unfold logistic
  exact div_lt_div_of_pos_left hν hgt (by nlinarith)

/-- [proved-derived; formal-checked] **Blow-up above the threshold.** The closed form leaves
every bound as `t` rises to the blow-up time. -/
theorem tendsto_logistic_atTop (hν : 0 < ν) (hω : 0 < ω) (hX : ν < X₀) :
    Tendsto (logistic ν ω X₀) (𝓝[<] blowupTime ν ω X₀) atTop := by
  have hcont : Continuous fun t : ℝ => 1 - (1 - ν / X₀) * Real.exp (ν * ω ^ 2 * t) := by
    fun_prop
  have h0 : Tendsto (fun t : ℝ => 1 - (1 - ν / X₀) * Real.exp (ν * ω ^ 2 * t))
      (𝓝[<] blowupTime ν ω X₀) (𝓝 0) := by
    have := hcont.tendsto (blowupTime ν ω X₀)
    rw [denominator_blowupTime hν hω hX] at this
    exact this.mono_left nhdsWithin_le_nhds
  have h1 : Tendsto (fun t : ℝ => 1 - (1 - ν / X₀) * Real.exp (ν * ω ^ 2 * t))
      (𝓝[<] blowupTime ν ω X₀) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨h0, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact denominator_pos hν hω hX ht
  have h2 := (tendsto_inv_nhdsGT_zero.comp h1).const_mul_atTop hν
  refine h2.congr fun t => ?_
  simp [logistic, div_eq_mul_inv]

variable {ι : Type*} [Fintype ι] [AddCommGroup ι]

/-- [definition] The uniform state whose critical norm is the closed form: every mode at
`ω * logistic t / m`. -/
def blowupState (ι : Type*) [Fintype ι] (ν ω X₀ t : ℝ) : ι → ℝ :=
  fun _ => ω * logistic ν ω X₀ t / Fintype.card ι

/-- [proved-derived; formal-checked] Wherever the closed form's denominator is not zero the
uniform state obeys the comb's law with the coherent feed, at every mode. -/
theorem hasDerivAt_blowupState (ν ω X₀ : ℝ) {t : ℝ}
    (hg : 1 - (1 - ν / X₀) * Real.exp (ν * ω ^ 2 * t) ≠ 0) (k : ι) :
    HasDerivAt (fun s => blowupState ι ν ω X₀ s k)
      (-(ν * ω ^ 2) • blowupState ι ν ω X₀ t k
        + coherentFeed ω (blowupState ι ν ω X₀ t) k) t := by
  have hm : (Fintype.card ι : ℝ) ≠ 0 := (card_pos' (ι := ι)).ne'
  have h := ((hasDerivAt_logistic ν ω X₀ hg).const_mul ω).div_const (Fintype.card ι : ℝ)
  refine h.congr_deriv ?_
  unfold blowupState
  rw [coherentFeed_const, smul_eq_mul]
  generalize logistic ν ω X₀ t = L
  field_simp
  ring

/-- The critical norm of the uniform state is the closed form, where the closed form is not
negative. -/
theorem criticalNorm_blowupState_of_nonneg (hω : 0 < ω) {t : ℝ}
    (hX : 0 ≤ logistic ν ω X₀ t) :
    criticalNorm (fun _ : ι => ω) (blowupState ι ν ω X₀ t) = logistic ν ω X₀ t := by
  have hm : (0 : ℝ) < Fintype.card ι := card_pos'
  unfold blowupState
  rw [criticalNorm_const, abs_of_nonneg (div_nonneg (mul_nonneg hω.le hX) hm.le)]
  field_simp

/-- [proved-derived; formal-checked] Above the threshold and before the blow-up time the critical
norm of the uniform state is the closed form. -/
theorem criticalNorm_blowupState (hν : 0 < ν) (hω : 0 < ω) (hX : ν < X₀) {t : ℝ}
    (ht : t < blowupTime ν ω X₀) :
    criticalNorm (fun _ : ι => ω) (blowupState ι ν ω X₀ t) = logistic ν ω X₀ t :=
  criticalNorm_blowupState_of_nonneg hω (hν.trans (lt_logistic hν hω hX ht)).le

/-- [proved-derived; formal-checked] The critical norm of the uniform state leaves every bound
as `t` rises to the blow-up time. -/
theorem tendsto_criticalNorm_blowupState (hν : 0 < ν) (hω : 0 < ω) (hX : ν < X₀) :
    Tendsto (fun t => criticalNorm (fun _ : ι => ω) (blowupState ι ν ω X₀ t))
      (𝓝[<] blowupTime ν ω X₀) atTop := by
  refine (tendsto_logistic_atTop hν hω hX).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (criticalNorm_blowupState hν hω hX ht).symm

/-- [proved-derived; formal-checked] **Above the threshold the comb's count does not decide.**
For `0 < ν < X₀` the uniform state opens with critical norm `X₀`, obeys the comb's law with the
coherent feed (which meets the comb's feed bound at coherence constant one) at every time before
`blowupTime`, has a strictly rising critical norm there, and leaves every bound as `t` rises to
`blowupTime`. -/
theorem blowup_above_threshold (hν : 0 < ν) (hω : 0 < ω) (hX : ν < X₀) :
    criticalNorm (fun _ : ι => ω) (blowupState ι ν ω X₀ 0) = X₀ ∧
    (∀ t, t < blowupTime ν ω X₀ → ∀ k : ι,
      HasDerivAt (fun s => blowupState ι ν ω X₀ s k)
        (-(ν * ω ^ 2) • blowupState ι ν ω X₀ t k
          + coherentFeed ω (blowupState ι ν ω X₀ t) k) t) ∧
    (∀ t (k : ι), ‖coherentFeed ω (blowupState ι ν ω X₀ t) k‖ ≤
      1 * ω * ∑ pq ∈ sumTriads k,
        ‖blowupState ι ν ω X₀ t pq.1‖ * ‖blowupState ι ν ω X₀ t pq.2‖) ∧
    StrictMonoOn (fun t => criticalNorm (fun _ : ι => ω) (blowupState ι ν ω X₀ t))
      (Iio (blowupTime ν ω X₀)) ∧
    Tendsto (fun t => criticalNorm (fun _ : ι => ω) (blowupState ι ν ω X₀ t))
      (𝓝[<] blowupTime ν ω X₀) atTop := by
  refine ⟨?_, fun t ht k => hasDerivAt_blowupState ν ω X₀
    (denominator_pos hν hω hX ht).ne' k, fun t k => norm_coherentFeed_le hω.le _ k, ?_,
    tendsto_criticalNorm_blowupState hν hω hX⟩
  · rw [criticalNorm_blowupState hν hω hX (blowupTime_pos hν hω hX),
      logistic_zero hν.ne']
  · intro s hs t ht hst
    simp only [criticalNorm_blowupState hν hω hX (mem_Iio.mp hs),
      criticalNorm_blowupState hν hω hX (mem_Iio.mp ht)]
    exact logistic_strictMonoOn hν hω hX hs ht hst

/-! ### Below the threshold: the same closed form, for all time -/

/-- Below the threshold the denominator is at least one at every time. -/
theorem one_le_denominator (hX0 : 0 < X₀) (hX : X₀ ≤ ν) (t : ℝ) :
    1 ≤ 1 - (1 - ν / X₀) * Real.exp (ν * ω ^ 2 * t) := by
  have hβ : 1 - ν / X₀ ≤ 0 := by
    rw [sub_nonpos, one_le_div hX0]
    exact hX
  nlinarith [mul_nonneg (neg_nonneg.mpr hβ) (Real.exp_pos (ν * ω ^ 2 * t)).le]

/-- [proved-derived; formal-checked] Below the threshold the uniform state with the closed form
is a comb system on all of `[0, ∞)`. -/
theorem subcritical_combSystem (hν : 0 < ν) (hω : 0 < ω) (hX0 : 0 < X₀) (hX : X₀ ≤ ν) :
    CombSystem (fun _ : ι => ω) ν 1 sumTriads (fun t => blowupState ι ν ω X₀ t)
      (fun t => coherentFeed ω (blowupState ι ν ω X₀ t)) where
  weight_pos _ := hω
  viscosity_pos := hν
  coherence_nonneg := zero_le_one
  fibres_disjoint := sumTriads_disjoint
  evolves k t _ := (hasDerivAt_blowupState ν ω X₀
    (lt_of_lt_of_le one_pos (one_le_denominator hX0 hX t)).ne' k).hasDerivWithinAt
  feed_le _ _ k := norm_coherentFeed_le hω.le _ k

/-- [proved-derived; formal-checked] Below the threshold the critical norm of that comb system is
the closed form at every time, and it opens at `X₀`. -/
theorem criticalNorm_subcriticalState (hν : 0 < ν) (hω : 0 < ω) (hX0 : 0 < X₀) (hX : X₀ ≤ ν)
    (t : ℝ) :
    criticalNorm (fun _ : ι => ω) (blowupState ι ν ω X₀ t) = logistic ν ω X₀ t := by
  refine criticalNorm_blowupState_of_nonneg hω ?_
  unfold logistic
  exact div_nonneg hν.le (le_trans zero_le_one (one_le_denominator hX0 hX t))

end Logistic

section Audit

#print axioms triads_disjoint
#print axioms norm_feed_le_triads
#print axioms Truncation.combSystem
#print axioms Truncation.critical_le_initial
#print axioms Truncation.dissipation_integral_le_drop
#print axioms Truncation.integral_dissipation_le
#print axioms norm_leray_le
#print axioms wavePairing_leray
#print axioms wavePairing_feed_leray
#print axioms hasDerivWithinAt_energy
#print axioms energy_antitoneOn
#print axioms energy_add_dissipation
#print axioms integral_dissipationRate_le
#print axioms hasDerivWithinAt_weightedEnergy
#print axioms weightedEnergy_antitoneOn
#print axioms criticalNorm_le_sqrt_mul_sqrt
#print axioms critical_le_of_second_count
#print axioms CombSystem.critical_le_mul_exp
#print axioms CombSystem.critical_le_of_integral_le
#print axioms CombSystem.critical_le_mul_exp_complex
#print axioms Truncation.critical_le_mul_exp
#print axioms wavePairing_eq_zero_of_evolves
#print axioms Truncation.of_leray
#print axioms leray_truncation_critical_le_initial
#print axioms norm_coherentFeed_le
#print axioms norm_coherentFeed_eq_of_nonneg
#print axioms uniform_combSystem
#print axioms constant_combSystem
#print axioms criticalNorm_constantState
#print axioms threshold_attained
#print axioms threshold_attained_zmod
#print axioms coherentFeed_work_pos
#print axioms constantState_not_conservative
#print axioms hasDerivAt_logistic
#print axioms lt_logistic
#print axioms logistic_strictMonoOn
#print axioms tendsto_logistic_atTop
#print axioms hasDerivAt_blowupState
#print axioms criticalNorm_blowupState
#print axioms blowup_above_threshold
#print axioms subcritical_combSystem
#print axioms criticalNorm_subcriticalState

end Audit

end Holonics.Fluid.GalerkinInstance
