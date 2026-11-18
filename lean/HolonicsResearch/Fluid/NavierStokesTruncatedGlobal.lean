import HolonicsResearch.Fluid.NavierStokesTriadConservation
import HolonicsResearch.Fluid.DissipativeGlobalFlow
import HolonicsResearch.Fluid.NavierStokesLaminarStability

/-!
# Every truncated fluid runs for all time, once, and keeps its energy account

Source record: `research/records/2026-11-18_AN_ABELIAN_COVER_FACTORS_THROUGH_ITS_CHARACTERS_A_TEMPERED_COMPLEX_MIXES_AT_ITS_HALF_THE_FLUIDS_TRIADS_DO_NO_WORK_SO_EVERY_TRUNCATION_FLOWS_FOR_ALL_TIME_AND_HARD_LEFSCHETZ_IS_A_POSITIVE_COMMUTATOR.md` (§7). This module
joins `Fluid/DissipativeGlobalFlow` (a dissipative field that is Lipschitz on balls has one global
flow) to `Fluid/NavierStokesTriadConservation` (the truncated fluid's triads do no work on real,
divergence-free data, and the law keeps those data), on the truncation of
`Fluid/NavierStokesGalerkinInstance`.

[definition] The state space `State ι n` is the amplitudes of all modes with the sum of their
squared norms, `PiLp 2` over the modes of `EuclideanSpace ℂ n`, read as a real inner product
space. The real, divergence-free states (`realStates κ bar`: `a (bar k) = conj (a k)` and
`κ k · a k = 0`) are a real subspace of it. The damping `damping κ ν` is a continuous linear map,
the feed `feedB κ` a continuous bilinear map, and the truncated field `fieldState κ ν` is
`damping κ ν x + feedB κ x x` (`fieldState_eq`).

[proved-derived; formal-checked] The join:

* `fieldState_lipschitzOnBalls`: the truncated field is Lipschitz on every ball of the state space;
* `fieldOn`: it maps the real, divergence-free states to themselves;
* `inner_fieldOn`: on them its work is the damping's alone,
  `⟪x, F x⟫ = -ν ∑ k, ‖κ k‖² ‖x_k‖²`, so it is dissipative for `ν ≥ 0` (`fieldOn_dissipative`);
* `exists_truncation`: every Galerkin truncation with Leray's projections on a wave set closed under
  `k ↦ -k`, with distinct nonzero wave vectors and `ν > 0`, has from every real divergence-free
  opening state a solution for all `t ≥ 0` that is a `Truncation` in the sense of
  `Fluid/NavierStokesGalerkinInstance`, stays real and divergence-free at every time, and whose
  energy never passes its opening value;
* `truncation_eq`: two `Truncation`s with Leray's projections from one opening state agree at every
  `t ≥ 0`, real or not; neither the reality condition nor the feed's work is used, only that the
  field is Lipschitz on a ball that holds both on `[0, T]`;
* `exists_truncation_energy`: the solution satisfies the energy equality
  `E t + ν * ∫₀ᵗ ∑ k, ‖κ k‖² ‖a_k‖² = E 0` at every `t ≥ 0`, with no hypothesis on the feed;
* `exists_truncation_plane`: in the plane, also `X t ≤ √(∑ ‖κ k‖⁻⁴) * √(2 E₂ 0)` at every `t ≥ 0`;
* `exists_truncation_laminar`: in any dimension, below Reynolds one (`X 0 < ν`), the solution's
  critical reading decays at the lowest mode's rate, `X t ≤ X 0 · exp (-(ν - X 0) w₀² t)`, a bound
  that names neither the horizon nor the modes (S6 of `Fluid/NavierStokesLaminarStability`, which
  now has its instance).

## What this does not state

Nothing here is a statement about the fluid's equation with infinitely many modes or about a limit
of truncations: every constant in the existence proof (the Lipschitz constant on a ball, the step
time) depends on the truncation. The energy equality and the plane's bound on `X` are uniform in
the truncation; the existence of a limit from them is not formalized. The solution is forward in
time only. Uniqueness is among `Truncation`s, which are divergence-free at every time by their
definition.

## The computational object

The helical pair interaction in its tube (a clocked span): the truncation's triads are pair
contacts among the modes, the flow is the tube's clock run without end, and the energy is the
reading its interior keeps. Pair (the triads) and tube (the flow) are touched; helix, faces and
placement, cell holonomy and tower thread stay attached through
`Fluid/NavierStokesGalerkinInstance`.

Consumers: the record (atlas row `ns.truncated-global-solution`), and every
statement of `Fluid/NavierStokesGalerkinInstance` and `Fluid/NavierStokesTriadConservation` that
takes a `Truncation` as a hypothesis, which now has an instance from every real divergence-free
opening state.

No `sorry`, no `axiom`, no `native_decide`.
-/

open Set Complex Filter Topology
open scoped InnerProductSpace ComplexConjugate NNReal

namespace Holonics.Fluid.TruncatedGlobal

open Holonics.Fluid.LaminarClass Holonics.Fluid.GalerkinInstance Holonics.Fluid.TriadConservation
open Holonics.Fluid.DissipativeGlobalFlow

noncomputable section

variable {n : Type*} [Fintype n] {ι : Type*} [Fintype ι]

/-! ## G1. The state space, the damping and the feed -/

/-- [definition] The state space: the amplitudes of all modes, with the sum of their squared
norms. -/
abbrev State (ι n : Type*) [Fintype n] := PiLp 2 (fun _ : ι => EuclideanSpace ℂ n)

/-- [definition] The damping, mode by mode: `x_k ↦ -(ν ‖κ k‖²) • x_k`. -/
def dampingₗ (κ : ι → EuclideanSpace ℝ n) (ν : ℝ) : State ι n →ₗ[ℝ] State ι n where
  toFun x := WithLp.toLp 2 (fun k => -(ν * ‖κ k‖ ^ 2) • x k)
  map_add' x y := by
    ext k : 1
    simp [smul_add]
  map_smul' r x := by
    ext k : 1
    simp [smul_comm r]

/-- [definition] The damping as a continuous linear map. -/
def damping (κ : ι → EuclideanSpace ℝ n) (ν : ℝ) : State ι n →L[ℝ] State ι n :=
  LinearMap.toContinuousLinearMap (dampingₗ κ ν)

/-- [definition] The feed of the pair `(x, y)`: the transport of `y` by `x` along the triads,
projected by Leray and turned by `-i`. On the diagonal it is the truncation's feed. -/
def pairFeed (κ : ι → EuclideanSpace ℝ n) (x y : State ι n) : State ι n :=
  WithLp.toLp 2 fun k =>
    (-I) • leray (κ k) (∑ pq ∈ triads κ k, wavePairing (κ pq.2) (x pq.1) • y pq.2)

theorem pairFeed_add_left (κ : ι → EuclideanSpace ℝ n) (x x' y : State ι n) :
    pairFeed κ (x + x') y = pairFeed κ x y + pairFeed κ x' y := by
  ext k : 1
  simp only [pairFeed, PiLp.toLp_apply, PiLp.add_apply, wavePairing_add_right, add_smul,
    Finset.sum_add_distrib, map_add, smul_add]

theorem pairFeed_smul_left (κ : ι → EuclideanSpace ℝ n) (r : ℝ) (x y : State ι n) :
    pairFeed κ (r • x) y = r • pairFeed κ x y := by
  ext k : 1
  simp only [pairFeed, PiLp.toLp_apply, PiLp.smul_apply, wavePairing_real_smul]
  have : ∀ pq : ι × ι, ((r : ℂ) * wavePairing (κ pq.2) (x pq.1)) • y pq.2
      = r • (wavePairing (κ pq.2) (x pq.1) • y pq.2) := by
    intro pq
    rw [mul_smul, Complex.coe_smul]
  simp only [this, ← Finset.smul_sum, ContinuousLinearMap.map_smul_of_tower]
  rw [smul_comm]

theorem pairFeed_add_right (κ : ι → EuclideanSpace ℝ n) (x y y' : State ι n) :
    pairFeed κ x (y + y') = pairFeed κ x y + pairFeed κ x y' := by
  ext k : 1
  simp only [pairFeed, PiLp.toLp_apply, PiLp.add_apply, smul_add, Finset.sum_add_distrib, map_add]

theorem pairFeed_smul_right (κ : ι → EuclideanSpace ℝ n) (r : ℝ) (x y : State ι n) :
    pairFeed κ x (r • y) = r • pairFeed κ x y := by
  ext k : 1
  simp only [pairFeed, PiLp.toLp_apply, PiLp.smul_apply]
  have : ∀ pq : ι × ι, wavePairing (κ pq.2) (x pq.1) • (r • y pq.2)
      = r • (wavePairing (κ pq.2) (x pq.1) • y pq.2) := fun pq => smul_comm _ _ _
  simp only [this, ← Finset.smul_sum, ContinuousLinearMap.map_smul_of_tower]
  rw [smul_comm]

/-- [definition] The feed as a bilinear map over the reals. -/
def feedₗ (κ : ι → EuclideanSpace ℝ n) : State ι n →ₗ[ℝ] State ι n →ₗ[ℝ] State ι n :=
  LinearMap.mk₂ ℝ (pairFeed κ) (pairFeed_add_left κ) (pairFeed_smul_left κ)
    (pairFeed_add_right κ) (pairFeed_smul_right κ)

/-- [definition] The feed as a continuous bilinear map (the state space is finite-dimensional). -/
def feedB (κ : ι → EuclideanSpace ℝ n) : State ι n →L[ℝ] State ι n →L[ℝ] State ι n :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (State ι n →ₗ[ℝ] State ι n) ≃ₗ[ℝ] _).toLinearMap ∘ₗ
      feedₗ κ)

theorem feedB_apply (κ : ι → EuclideanSpace ℝ n) (x y : State ι n) :
    feedB κ x y = pairFeed κ x y := rfl

theorem damping_apply (κ : ι → EuclideanSpace ℝ n) (ν : ℝ) (x : State ι n) :
    damping κ ν x = WithLp.toLp 2 (fun k => -(ν * ‖κ k‖ ^ 2) • x k) := rfl

/-- [definition] The truncated field on the state space. -/
def fieldState (κ : ι → EuclideanSpace ℝ n) (ν : ℝ) (x : State ι n) : State ι n :=
  WithLp.toLp 2 (field κ ν (WithLp.ofLp x))

/-- [proved-derived; formal-checked] The truncated field is the damping plus the feed's
diagonal. -/
theorem fieldState_eq (κ : ι → EuclideanSpace ℝ n) (ν : ℝ) (x : State ι n) :
    fieldState κ ν x = damping κ ν x + feedB κ x x := by
  ext k : 1
  rfl

/-- [proved-derived; formal-checked] The truncated field is Lipschitz on every ball of the state
space. -/
theorem fieldState_lipschitzOnBalls (κ : ι → EuclideanSpace ℝ n) (ν : ℝ) :
    LipschitzOnBalls (fieldState κ ν) := by
  have h := lipschitzOnBalls_linear_add_bilinear (damping κ ν) (feedB κ)
  have he : fieldState κ ν = fun x => damping κ ν x + feedB κ x x :=
    funext (fieldState_eq κ ν)
  rw [he]
  exact h

/-! ## G2. The real, divergence-free states -/

/-- [definition] The real, divergence-free states: `a (bar k) = conj (a k)` and `κ k · a k = 0`. -/
def realStates (κ : ι → EuclideanSpace ℝ n) (bar : ι → ι) : Submodule ℝ (State ι n) where
  carrier := {x | IsRealField bar (WithLp.ofLp x) ∧ ∀ k, wavePairing (κ k) (x k) = 0}
  zero_mem' := by
    refine ⟨fun k j => by simp, fun k => ?_⟩
    unfold wavePairing
    simp
  add_mem' := by
    rintro x y ⟨hx, hdx⟩ ⟨hy, hdy⟩
    refine ⟨fun k j => ?_, fun k => ?_⟩
    · simp only [PiLp.add_apply, map_add]
      rw [hx k j, hy k j]
    · simp only [PiLp.add_apply, wavePairing_add_right, hdx k, hdy k, add_zero]
  smul_mem' := by
    rintro r x ⟨hx, hdx⟩
    refine ⟨fun k j => ?_, fun k => ?_⟩
    · simp only [PiLp.smul_apply, Complex.real_smul, map_mul, Complex.conj_ofReal]
      rw [hx k j]
    · simp only [PiLp.smul_apply, wavePairing_real_smul, hdx k, mul_zero]

omit [Fintype ι] in
theorem mem_realStates {κ : ι → EuclideanSpace ℝ n} {bar : ι → ι} {x : State ι n} :
    x ∈ realStates κ bar ↔
      IsRealField bar (WithLp.ofLp x) ∧ ∀ k, wavePairing (κ k) (x k) = 0 := Iff.rfl

variable {κ : ι → EuclideanSpace ℝ n} {bar : ι → ι}

/-- [proved-derived; formal-checked] **The truncated field keeps the real, divergence-free
states**, so it restricts to them. -/
def fieldOn (hs : WaveSymmetric κ bar) (ν : ℝ) (x : realStates κ bar) : realStates κ bar :=
  ⟨fieldState κ ν x, by
    refine ⟨?_, fun k => ?_⟩
    · simpa [fieldState] using field_isRealField hs ν x.2.1
    · simpa [fieldState] using wavePairing_field_eq_zero κ ν x.2.2 k⟩

theorem coe_fieldOn (hs : WaveSymmetric κ bar) (ν : ℝ) (x : realStates κ bar) :
    (fieldOn hs ν x : State ι n) = fieldState κ ν x := rfl

/-- [proved-derived; formal-checked] On the real, divergence-free states the field's work is the
damping's alone: `⟪x, F x⟫ = -ν ∑ k, ‖κ k‖² ‖x_k‖²`. -/
theorem inner_fieldOn (hs : WaveSymmetric κ bar) (ν : ℝ) (x : realStates κ bar) :
    inner ℝ x (fieldOn hs ν x) = -(ν * ∑ k, ‖κ k‖ ^ 2 * ‖(x : State ι n) k‖ ^ 2) := by
  rw [Submodule.coe_inner, coe_fieldOn, PiLp.inner_apply]
  have hfeed := sum_real_inner_feed_leray_eq_zero hs x.2.1 x.2.2
  have hk : ∀ k, inner ℝ ((x : State ι n) k) ((fieldState κ ν x) k)
      = -(ν * ‖κ k‖ ^ 2) * ‖(x : State ι n) k‖ ^ 2
        + inner ℝ ((x : State ι n) k) (feed κ (fun k => leray (κ k)) (WithLp.ofLp (x : State ι n)) k) := by
    intro k
    simp only [fieldState, PiLp.toLp_apply, field, inner_add_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq]
  simp only [hk, Finset.sum_add_distrib]
  rw [show (∑ k, inner ℝ ((x : State ι n) k)
      (feed κ (fun k => leray (κ k)) (WithLp.ofLp (x : State ι n)) k)) = 0 from hfeed]
  rw [add_zero, Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- [proved-derived; formal-checked] The restricted field is dissipative for `ν ≥ 0`. -/
theorem fieldOn_dissipative (hs : WaveSymmetric κ bar) {ν : ℝ} (hν : 0 ≤ ν) :
    Dissipative (fieldOn hs ν) := by
  intro x
  rw [inner_fieldOn]
  have : 0 ≤ ∑ k, ‖κ k‖ ^ 2 * ‖(x : State ι n) k‖ ^ 2 :=
    Finset.sum_nonneg fun k _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  nlinarith

/-- [proved-derived; formal-checked] The restricted field is Lipschitz on every ball of the
subspace. -/
theorem fieldOn_lipschitzOnBalls (hs : WaveSymmetric κ bar) (ν : ℝ) :
    LipschitzOnBalls (fieldOn hs ν) := by
  intro R
  obtain ⟨K, hK⟩ := fieldState_lipschitzOnBalls κ ν R
  refine ⟨K, LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_⟩
  have hx' : (x : State ι n) ∈ Metric.closedBall (0 : State ι n) R := by
    rw [Metric.mem_closedBall] at hx ⊢
    rw [Subtype.dist_eq] at hx
    simpa using hx
  have hy' : (y : State ι n) ∈ Metric.closedBall (0 : State ι n) R := by
    rw [Metric.mem_closedBall] at hy ⊢
    rw [Subtype.dist_eq] at hy
    simpa using hy
  rw [Subtype.dist_eq, Subtype.dist_eq, coe_fieldOn, coe_fieldOn]
  exact hK.dist_le_mul _ hx' _ hy'

/-! ## G3. Existence for all time -/

variable {ν : ℝ}

/-- [proved-derived; formal-checked] **Every truncated fluid runs for all time.** A Galerkin
truncation with Leray's projections on a wave set closed under `k ↦ -k`, with distinct nonzero
wave vectors and `ν > 0`, has from every real divergence-free opening state a solution on
`[0, ∞)`: a `Truncation`, real and divergence-free at every time, with its energy never above the
opening one. -/
theorem exists_truncation (hs : WaveSymmetric κ bar) (hκ : Function.Injective κ)
    (hκ0 : ∀ k, κ k ≠ 0) (hν : 0 < ν) {a₀ : ι → EuclideanSpace ℂ n}
    (hreal : IsRealField bar a₀) (hdiv : ∀ k, wavePairing (κ k) (a₀ k) = 0) :
    ∃ a : ℝ → ι → EuclideanSpace ℂ n, a 0 = a₀ ∧ Truncation κ ν (fun k => leray (κ k)) a ∧
      (∀ t, IsRealField bar (a t)) ∧ (∀ t, ∀ k, wavePairing (κ k) (a t k) = 0) ∧
      ∀ t, 0 ≤ t → energy (a t) ≤ energy a₀ := by
  set x₀ : realStates κ bar := ⟨WithLp.toLp 2 a₀, hreal, hdiv⟩ with hx₀
  obtain ⟨y, hy0, hyd, hynorm⟩ :=
    exists_global (fieldOn_dissipative hs hν.le) (fieldOn_lipschitzOnBalls hs ν) x₀
  set a : ℝ → ι → EuclideanSpace ℂ n := fun t => WithLp.ofLp ((y t : realStates κ bar) : State ι n)
    with ha
  have ha0 : a 0 = a₀ := by simp [ha, hy0, hx₀]
  have hreal_t : ∀ t, IsRealField bar (a t) := fun t => (y t).2.1
  have hdiv_t : ∀ t, ∀ k, wavePairing (κ k) (a t k) = 0 := fun t => (y t).2.2
  have hevolves : ∀ k t, 0 ≤ t → HasDerivWithinAt (fun s => a s k)
      (-(ν * ‖κ k‖ ^ 2) • a t k + feed κ (fun k => leray (κ k)) (a t) k) (Ici 0) t := by
    intro k t ht
    have h1 := ((realStates κ bar).subtypeL.hasFDerivAt).comp_hasDerivWithinAt t (hyd t ht)
    have h2 := (PiLp.proj 2 (𝕜 := ℝ) (fun _ : ι => EuclideanSpace ℂ n) k).hasFDerivAt.comp_hasDerivWithinAt
      t h1
    exact h2
  have htr : Truncation κ ν (fun k => leray (κ k)) a :=
    { wave_injective := hκ
      wave_ne_zero := hκ0
      viscosity_pos := hν
      projection_le := fun k => norm_leray_le (κ k)
      incompressible := fun t _ k => hdiv_t t k
      evolves := hevolves }
  refine ⟨a, ha0, htr, hreal_t, hdiv_t, fun t ht => ?_⟩
  have := htr.energy_le_initial_of_real hs (fun s _ => hreal_t s) ht
  rwa [ha0] at this

/-! ## G4. Uniqueness among all truncations -/

/-- A truncation read as a curve in the state space has the truncated field as its derivative. -/
theorem _root_.Holonics.Fluid.GalerkinInstance.Truncation.hasDerivWithinAt_state
    {a : ℝ → ι → EuclideanSpace ℂ n} (h : Truncation κ ν (fun k => leray (κ k)) a)
    {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => (WithLp.toLp 2 (a s) : State ι n)) (fieldState κ ν (WithLp.toLp 2 (a t)))
      (Ici 0) t := by
  have hpi : HasDerivWithinAt (fun s => a s) (field κ ν (a t)) (Ici 0) t :=
    hasDerivWithinAt_pi.mpr fun k => h.evolves k t ht
  have := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => EuclideanSpace ℂ n)).symm.hasFDerivAt
    |>.comp_hasDerivWithinAt t hpi
  exact this

/-- [proved-derived; formal-checked] **The truncated fluid's solution is unique.** Two
`Truncation`s with Leray's projections from one opening state agree at every `t ≥ 0`. No reality
condition and no energy bound is used: on `[0, T]` both are bounded, and the field is Lipschitz on
the ball that holds both. -/
theorem truncation_eq {a b : ℝ → ι → EuclideanSpace ℂ n}
    (ha : Truncation κ ν (fun k => leray (κ k)) a) (hb : Truncation κ ν (fun k => leray (κ k)) b)
    (h0 : a 0 = b 0) {T : ℝ} (hT : 0 ≤ T) : a T = b T := by
  set f : ℝ → State ι n := fun s => WithLp.toLp 2 (a s) with hf
  set g : ℝ → State ι n := fun s => WithLp.toLp 2 (b s) with hg
  have hfd : ∀ s, 0 ≤ s → HasDerivWithinAt f (fieldState κ ν (f s)) (Ici 0) s :=
    fun s hs => ha.hasDerivWithinAt_state hs
  have hgd : ∀ s, 0 ≤ s → HasDerivWithinAt g (fieldState κ ν (g s)) (Ici 0) s :=
    fun s hs => hb.hasDerivWithinAt_state hs
  have hfc : ContinuousOn f (Icc 0 T) := fun s hs =>
    ((hfd s hs.1).continuousWithinAt).mono Icc_subset_Ici_self
  have hgc : ContinuousOn g (Icc 0 T) := fun s hs =>
    ((hgd s hs.1).continuousWithinAt).mono Icc_subset_Ici_self
  obtain ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn hfc
  obtain ⟨C₂, hC₂⟩ := isCompact_Icc.exists_bound_of_continuousOn hgc
  obtain ⟨K, hK⟩ := fieldState_lipschitzOnBalls κ ν (max C₁ C₂)
  have hderiv : ∀ {φ : ℝ → State ι n}, (∀ s, 0 ≤ s → HasDerivWithinAt φ (fieldState κ ν (φ s))
      (Ici 0) s) → ∀ s ∈ Ico 0 T, HasDerivWithinAt φ (fieldState κ ν (φ s)) (Ici s) s :=
    fun hφ s hs => (hφ s hs.1).mono (Ici_subset_Ici.mpr hs.1)
  have heq := ODE_solution_unique_of_mem_Icc_right (v := fun _ => fieldState κ ν)
    (s := fun _ => Metric.closedBall (0 : State ι n) (max C₁ C₂)) (K := K)
    (fun _ _ => hK) hfc (hderiv hfd)
    (fun s hs => mem_closedBall_zero_iff.mpr
      ((hC₁ s (Ico_subset_Icc_self hs)).trans (le_max_left _ _)))
    hgc (hderiv hgd)
    (fun s hs => mem_closedBall_zero_iff.mpr
      ((hC₂ s (Ico_subset_Icc_self hs)).trans (le_max_right _ _)))
    (by simp [hf, hg, h0])
  have := heq ⟨hT, le_rfl⟩
  simpa [hf, hg] using congrArg WithLp.ofLp this

/-! ## G5. The energy account and the plane's bound, for the solution that exists -/

/-- [proved-derived; formal-checked] **Existence, uniqueness and the energy equality.** From
every real divergence-free opening state there is exactly one truncated solution on `[0, ∞)`, and
it satisfies `E t + ν * ∫₀ᵗ ∑ k, ‖κ k‖² ‖a_k‖² = E 0` at every `t ≥ 0`, with no hypothesis on the
feed. -/
theorem exists_truncation_energy (hs : WaveSymmetric κ bar) (hκ : Function.Injective κ)
    (hκ0 : ∀ k, κ k ≠ 0) (hν : 0 < ν) {a₀ : ι → EuclideanSpace ℂ n}
    (hreal : IsRealField bar a₀) (hdiv : ∀ k, wavePairing (κ k) (a₀ k) = 0) :
    ∃ a : ℝ → ι → EuclideanSpace ℂ n, a 0 = a₀ ∧ Truncation κ ν (fun k => leray (κ k)) a ∧
      (∀ t, IsRealField bar (a t)) ∧
      (∀ t, 0 ≤ t → energy (a t) + ν * ∫ s in (0 : ℝ)..t, dissipationRate (fun k => ‖κ k‖) (a s)
        = energy a₀) ∧
      ∀ b : ℝ → ι → EuclideanSpace ℂ n, Truncation κ ν (fun k => leray (κ k)) b → b 0 = a₀ →
        ∀ t, 0 ≤ t → b t = a t := by
  obtain ⟨a, ha0, htr, hreal_t, -, -⟩ := exists_truncation hs hκ hκ0 hν hreal hdiv
  refine ⟨a, ha0, htr, hreal_t, fun t ht => ?_, fun b hb hb0 t ht =>
    truncation_eq hb htr (hb0.trans ha0.symm) ht⟩
  have := htr.energy_add_dissipation_of_real hs (fun s _ => hreal_t s) ht
  rwa [ha0] at this

/-- [proved-derived; formal-checked] **In the plane the critical reading stays bounded for all
time.** The solution from every real divergence-free opening state on a symmetric plane wave set
has `X t ≤ √(∑ ‖κ k‖⁻⁴) * √(2 E₂ 0)` at every `t ≥ 0`, with no smallness of the data. -/
theorem exists_truncation_plane {ι : Type*} [Fintype ι] {κ : ι → EuclideanSpace ℝ (Fin 2)}
    {bar : ι → ι} (hs : WaveSymmetric κ bar) (hκ : Function.Injective κ) (hκ0 : ∀ k, κ k ≠ 0)
    (hν : 0 < ν) {a₀ : ι → EuclideanSpace ℂ (Fin 2)} (hreal : IsRealField bar a₀)
    (hdiv : ∀ k, wavePairing (κ k) (a₀ k) = 0) :
    ∃ a : ℝ → ι → EuclideanSpace ℂ (Fin 2), a 0 = a₀ ∧
      Truncation κ ν (fun k => leray (κ k)) a ∧
      ∀ t, 0 ≤ t → criticalNorm (fun k => ‖κ k‖) (a t) ≤
        √(∑ k, ‖κ k‖ ^ (-4 : ℤ)) * √(2 * weightedEnergy (fun k => ‖κ k‖ ^ 2) a₀) := by
  obtain ⟨a, ha0, htr, hreal_t, -, -⟩ := exists_truncation hs hκ hκ0 hν hreal hdiv
  refine ⟨a, ha0, htr, fun t ht => ?_⟩
  have := htr.critical_le_of_real_two hs (fun s _ => hreal_t s) ht
  rwa [ha0] at this

/-- [proved-derived; formal-checked] **Below Reynolds one, in any dimension.** From every real
divergence-free opening state with `X 0 < ν`, on a symmetric wave set whose wave vectors are at
least `w₀ > 0` long, the solution exists for all time and its critical reading decays at the
lowest mode's rate, `X t ≤ X 0 · exp (-(ν - X 0) w₀² t)`. Neither the constant nor the rate names
the truncation. -/
theorem exists_truncation_laminar (hs : WaveSymmetric κ bar) (hκ : Function.Injective κ)
    (hκ0 : ∀ k, κ k ≠ 0) (hν : 0 < ν) {a₀ : ι → EuclideanSpace ℂ n}
    (hreal : IsRealField bar a₀) (hdiv : ∀ k, wavePairing (κ k) (a₀ k) = 0)
    (hX : criticalNorm (fun k => ‖κ k‖) a₀ < ν) {w₀ : ℝ} (hw₀ : 0 < w₀)
    (hle : ∀ k, w₀ ≤ ‖κ k‖) :
    ∃ a : ℝ → ι → EuclideanSpace ℂ n, a 0 = a₀ ∧ Truncation κ ν (fun k => leray (κ k)) a ∧
      ∀ t, 0 ≤ t → criticalNorm (fun k => ‖κ k‖) (a t) ≤ criticalNorm (fun k => ‖κ k‖) a₀ *
        Real.exp (-(ν - criticalNorm (fun k => ‖κ k‖) a₀) * w₀ ^ 2 * t) := by
  obtain ⟨a, ha0, htr, -, -, -⟩ := exists_truncation hs hκ hκ0 hν hreal hdiv
  refine ⟨a, ha0, htr, fun t ht => ?_⟩
  have := htr.critical_le_mul_exp_decay (by rwa [ha0]) hw₀ hle ht
  rwa [ha0] at this

end

/-! ## Audit -/

section Audit

#print axioms fieldState_eq
#print axioms fieldState_lipschitzOnBalls
#print axioms inner_fieldOn
#print axioms fieldOn_dissipative
#print axioms fieldOn_lipschitzOnBalls
#print axioms exists_truncation
#print axioms truncation_eq
#print axioms exists_truncation_energy
#print axioms exists_truncation_plane
#print axioms exists_truncation_laminar

end Audit

end Holonics.Fluid.TruncatedGlobal
