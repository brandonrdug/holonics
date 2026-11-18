import HolonicsResearch.Fluid.NavierStokesGalerkinInstance
import Mathlib

/-!
# The truncated fluid's own triads do no work

Source record: `research/records/2026-11-18_AN_ABELIAN_COVER_FACTORS_THROUGH_ITS_CHARACTERS_A_TEMPERED_COMPLEX_MIXES_AT_ITS_HALF_THE_FLUIDS_TRIADS_DO_NO_WORK_SO_EVERY_TRUNCATION_FLOWS_FOR_ALL_TIME_AND_HARD_LEFSCHETZ_IS_A_POSITIVE_COMMUTATOR.md` (§6; it follows
`research/records/2026-11-18_THE_HALF_IS_THE_POSITIVITY_OF_THE_REVERSALS_OWN_FORM_A_FINITE_COMPLEX_HAS_ITS_ZEROS_AND_COUNT_IN_LEAN_COUPLED_LOCKS_KEEP_THE_CIRCLE_TWO_TORIS_INDEX_THEOREM_IS_A_NORM_AND_BELOW_REYNOLDS_ONE_THE_COUNT_DECIDES.md`,
§10.4, which carried the conservation of the energy as a hypothesis).

`Fluid/NavierStokesGalerkinInstance` proves the energy equality for a damped family whose feed
does no work (`Conservative`), and its docstring says that the fluid's own feed being
conservative "needs the mode set closed under `k ↦ -k` with the reality condition, and is not
assembled here". This module assembles it.

## What is proved

[definition] A **symmetric truncation set** is an involution `bar` of the modes with
`κ (bar k) = -κ k` (`WaveSymmetric`). A state is a **real field** when `a (bar k) = conj (a k)`
coordinate by coordinate (`IsRealField`): the Fourier amplitudes of a real velocity. The bilinear
pairing of two amplitudes is `dot x y = ∑ j, x j * y j`, with no conjugation.

[proved-derived; formal-checked] **The triad identity.** For any wave vectors and amplitudes
across their own wave vectors (`wavePairing (κ p) (a p) = 0`), the sum over the triples with
`κ p + κ q + κ r = 0`,

  `triadSum κ a = ∑_{κ p + κ q + κ r = 0} (κ q · a_p) * (a_q · a_r)`,

is zero (`triadSum_eq_zero`). The proof is the triad's own symmetry: exchanging `q` and `r`
keeps the condition and the second factor (`triadSum_swap`), and the two halves add to
`(κ q + κ r) · a_p = -(κ p · a_p) = 0`. In the physical chart this is
`∫ (u · ∇ u) · u = -½ ∫ (∇ · u) |u|² = 0`.

[proved-derived; formal-checked] **The feed does no work.** With Leray's projections:

* `inner_leray_of_across`: Leray's projection is self-adjoint and fixes an amplitude across its
  wave vector, so `⟪a_k, leray (κ k) v⟫ = ⟪a_k, v⟫`;
* `inner_feed_leray`: `⟪a_k, N_k⟫ = -i * ∑_{(p, q) ∈ triads k} (κ q · a_p) * ⟪a_k, a_q⟫`;
* `sum_inner_feed_leray`: on a real field over a symmetric set,
  `∑ k, ⟪a_k, N_k⟫ = -i * triadSum κ a` (the reality condition turns `⟪a_k, a_q⟫` into
  `a_q · a_(bar k)`, and `bar` reindexes the modes);
* `sum_inner_feed_leray_eq_zero`: so `∑ k, ⟪a_k, N_k⟫ = 0` in `ℂ`, and
  `sum_real_inner_feed_leray_eq_zero`: `∑ k, Re ⟪a_k, N_k⟫ = 0`, the real inner product that
  `Conservative` reads (`real_inner_eq_re_inner'`).

[proved-derived; formal-checked] **The energy equality with no hypothesis on the feed.**

* `Truncation.conservative_of_real`: a truncation with Leray's projections whose state is a real
  field at every time is `Conservative`;
* `Truncation.energy_add_dissipation_of_real`:
  `E t + ν * ∫ s in 0..t, ∑ k, ‖κ k‖ ^ 2 * ‖a s k‖ ^ 2 = E 0`, at every size of the data and at
  every truncation;
* `Truncation.energy_le_initial_of_real`, `Truncation.integral_dissipationRate_le_of_real`: the
  energy never rises and the dissipation is paid within the opening energy.

[proved-derived; formal-checked] **The real, incompressible states are kept by the law.** The
truncated field `F(a)_k = -(ν ‖κ k‖²) • a_k + N_k` maps a real field across its wave vectors to a
real field across its wave vectors:

* `leray_apply`, `leray_neg`, `leray_conj`: Leray's projection in coordinates, the same at `-q`,
  and commuting with conjugation (its wave vector is real);
* `transport_bar`: the transport sum into `bar k` is minus the conjugate of the sum into `k`;
* `feed_leray_isRealField`: the feed of a real field is a real field;
* `field_isRealField`, `wavePairing_field_eq_zero`: so is the whole truncated field, and it is
  across its wave vectors.

[proved-derived; formal-checked] **In two dimensions the second count is conserved too.** For
wave vectors of the plane (`n = Fin 2`):

* `eq_stream_smul_perp`: an amplitude across a nonzero wave vector is `ψ • perp q`, a stream
  amplitude times the quarter-turn `perp q = (-q₁, q₀)`;
* `sum_weighted_inner_feed_leray`: for a weight with `g (bar k) = g k`, the weighted work
  `∑ k, g k * ⟪a_k, N_k⟫` is `-i` times the triad sum weighted at the receiving mode;
* `triadGeometry_perm_sum`: with stream amplitudes each ordered triad contributes
  `ψ_p ψ_q ψ_r (κ_p × κ_q)(κ_q · κ_r) ‖κ_r‖²`, and on a closed triad the six orderings of this
  geometric factor add to zero (a polynomial identity once `κ_r = -κ_p - κ_q`);
* `weightedTriadSum_normSq_eq_zero`: so the triad sum weighted by `‖κ r‖²` vanishes, by
  averaging over the six permutations of the triple (`cycEquiv`, `swapEquiv`);
* `sum_normSq_real_inner_feed_leray_eq_zero`, `Truncation.weightedConservative_of_real_two`: a
  plane truncation with Leray's projections whose state is a real field is
  `WeightedConservative` for `g k = ‖κ k‖²` (the enstrophy);
* `Truncation.critical_le_of_real_two`: so the critical reading of every plane truncation is
  bounded for all time by `√(∑ ‖κ k‖⁻⁴) * √(2 E₂ 0)`, with no smallness: the hypothesis that
  `critical_le_of_second_count` carried is the plane fluid's own.

## Limits

The module constructs no solution: a truncation is a hypothesis given on `[0, ∞)`, and the
reality of the state at every time is a hypothesis of the energy corollaries (the invariance of
the field under the reality condition is proved here). `Fluid/NavierStokesTruncatedGlobal` closes
both: it constructs the truncation from every real divergence-free opening state, unique among
truncations, real at every time, with the energy equality. In three dimensions the second count is
not conserved (the stretching of vorticity) and nothing here bounds it. Projections other than
Leray's are not treated. The bound of two dimensions names the modes through `∑ ‖κ k‖⁻⁴`, which
is finite over the wave vectors of a torus of dimension two, so the limit of truncations is not
taken here.

Computational object: the helical pair interaction. A triad `κ p + κ q + κ r = 0` is a closed
pair contact of three modes, and the identity is the statement that the transport around it
returns the energy it moves: of the winding guide's six objects it touches the pair and the
faces and placement (the pairing `dot` and the receiver's inner product), with the helix, the
cell holonomy, the tube and the tower thread kept attached through the truncation's modes.

Consumers: `Fluid/NavierStokesGalerkinInstance` (`energy_add_dissipation`, `Conservative`),
`Fluid/NavierStokesTruncatedGlobal`, the atlas rows `ns.triads-do-no-work`,
`ns.comb-conserved-counts` and `ns.energy-count-cannot-decide`.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

open Finset Set Complex
open scoped InnerProductSpace ComplexConjugate

namespace Holonics.Fluid.TriadConservation

open Holonics.Fluid.LaminarClass Holonics.Fluid.GalerkinInstance

/-! ## T1. Two pairings and the triad identity -/

section Triad

variable {n : Type*} [Fintype n] {ι : Type*} [Fintype ι]

/-- [definition] The bilinear pairing of two amplitudes, `x · y = ∑ j, x j * y j`, with no
conjugation. -/
def dot (x y : EuclideanSpace ℂ n) : ℂ := ∑ j, x j * y j

theorem dot_comm (x y : EuclideanSpace ℂ n) : dot x y = dot y x := by
  unfold dot
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem wavePairing_neg (q : EuclideanSpace ℝ n) (a : EuclideanSpace ℂ n) :
    wavePairing (-q) a = -wavePairing q a := by
  unfold wavePairing
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp

open Classical in
/-- [definition] The triad sum: over the triples of modes whose wave vectors close,
`κ p + κ q + κ r = 0`, the transport `(κ q · a_p)` times the pairing `(a_q · a_r)`. -/
def triadSum (κ : ι → EuclideanSpace ℝ n) (a : ι → EuclideanSpace ℂ n) : ℂ :=
  ∑ p, ∑ q, ∑ r, if κ p + κ q + κ r = 0 then wavePairing (κ q) (a p) * dot (a q) (a r) else 0

open Classical in
/-- [proved-derived; formal-checked] Exchanging the last two modes of a triad keeps its condition
and its pairing, and moves the transport's wave vector. -/
theorem triadSum_swap (κ : ι → EuclideanSpace ℝ n) (a : ι → EuclideanSpace ℂ n) :
    triadSum κ a =
      ∑ p, ∑ q, ∑ r, if κ p + κ q + κ r = 0 then wavePairing (κ r) (a p) * dot (a q) (a r)
        else 0 := by
  unfold triadSum
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun r _ => ?_
  have h : κ p + κ r + κ q = κ p + κ q + κ r := add_right_comm _ _ _
  simp only [h, dot_comm (a r) (a q)]

/-- [proved-derived; formal-checked] **The triad identity.** For amplitudes across their own wave
vectors the triad sum vanishes: the two halves of the exchange add to
`(κ q + κ r) · a_p = -(κ p · a_p) = 0`. -/
theorem triadSum_eq_zero (κ : ι → EuclideanSpace ℝ n) (a : ι → EuclideanSpace ℂ n)
    (hdiv : ∀ p, wavePairing (κ p) (a p) = 0) : triadSum κ a = 0 := by
  classical
  have h2 : triadSum κ a + triadSum κ a = 0 := by
    conv_lhs => arg 2; rw [triadSum_swap]
    unfold triadSum
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun p _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun q _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun r _ => ?_
    split_ifs with hc
    · have hqr : κ q + κ r = -κ p := by
        rw [eq_neg_iff_add_eq_zero, add_comm, ← add_assoc]
        exact hc
      rw [← add_mul, ← wavePairing_add, hqr, wavePairing_neg, hdiv p, neg_zero, zero_mul]
    · exact add_zero 0
  exact add_self_eq_zero.mp h2

end Triad

/-! ## T2. The real inner product, Leray's projection and the feed's work -/

section Work

variable {n : Type*} [Fintype n] {ι : Type*} [Fintype ι]

/-- [proved-derived; formal-checked] The real inner product of the complex amplitude space (the
one `Conservative` reads) is the real part of the complex one. -/
theorem real_inner_eq_re_inner' (x y : EuclideanSpace ℂ n) :
    inner ℝ x y = (inner ℂ x y).re := by
  rw [PiLp.inner_apply, PiLp.inner_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.inner, RCLike.inner_apply]

/-- [proved-derived; formal-checked] Leray's projection is self-adjoint and fixes an amplitude
across its wave vector: `⟪b, leray q v⟫ = ⟪b, v⟫` when `q · b = 0`. -/
theorem inner_leray_of_across {q : EuclideanSpace ℝ n} {b : EuclideanSpace ℂ n}
    (hb : wavePairing q b = 0) (v : EuclideanSpace ℂ n) :
    inner ℂ b (leray q v) = inner ℂ b v := by
  have hmem : b ∈ (ℂ ∙ complexify q)ᗮ := by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, ← wavePairing_eq_inner]
    exact hb
  unfold leray
  rw [← Submodule.inner_starProjection_left_eq_right,
    Submodule.starProjection_eq_self_iff.mpr hmem]

/-- [proved-derived; formal-checked] The work of the feed on one mode:
`⟪a_k, N_k⟫ = -i * ∑_{(p, q) ∈ triads k} (κ q · a_p) * ⟪a_k, a_q⟫`. -/
theorem inner_feed_leray (κ : ι → EuclideanSpace ℝ n) (a : ι → EuclideanSpace ℂ n) (k : ι)
    (hk : wavePairing (κ k) (a k) = 0) :
    inner ℂ (a k) (feed κ (fun k => leray (κ k)) a k)
      = -I * ∑ pq ∈ triads κ k, wavePairing (κ pq.2) (a pq.1) * inner ℂ (a k) (a pq.2) := by
  unfold feed
  rw [inner_smul_right, inner_leray_of_across hk, inner_sum]
  congr 1
  refine Finset.sum_congr rfl fun pq _ => ?_
  rw [inner_smul_right]

/-- [definition] A symmetric truncation set: an involution `bar` of the modes reversing the wave
vectors, `κ (bar k) = -κ k`. -/
structure WaveSymmetric (κ : ι → EuclideanSpace ℝ n) (bar : ι → ι) : Prop where
  involutive : Function.Involutive bar
  wave_bar : ∀ k, κ (bar k) = -κ k

/-- [definition] A real field: `a (bar k) = conj (a k)` coordinate by coordinate, the Fourier
amplitudes of a real velocity. -/
def IsRealField (bar : ι → ι) (a : ι → EuclideanSpace ℂ n) : Prop :=
  ∀ k j, a (bar k) j = conj (a k j)

omit [Fintype ι] in
/-- On a real field the complex inner product of two modes is the bilinear pairing with the
reversed first mode: `⟪a_k, a_q⟫ = a_q · a_(bar k)`. -/
theorem inner_eq_dot_of_real {bar : ι → ι} {a : ι → EuclideanSpace ℂ n} (ha : IsRealField bar a)
    (k q : ι) : inner ℂ (a k) (a q) = dot (a q) (a (bar k)) := by
  rw [PiLp.inner_apply]
  unfold dot
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [RCLike.inner_apply, ha k j]

open Classical in
/-- A sum over the triads of a mode as a double sum over the modes. -/
theorem sum_triads_eq (κ : ι → EuclideanSpace ℝ n) (k : ι) (f : ι × ι → ℂ) :
    ∑ pq ∈ triads κ k, f pq = ∑ p, ∑ q, if κ p + κ q = κ k then f (p, q) else 0 := by
  unfold triads
  rw [Finset.sum_filter, ← Finset.univ_product_univ, Finset.sum_product]

/-- [proved-derived; formal-checked] On a real field over a symmetric set the work of the feed is
`-i` times the triad sum. -/
theorem sum_inner_feed_leray {κ : ι → EuclideanSpace ℝ n} {bar : ι → ι}
    (hs : WaveSymmetric κ bar) {a : ι → EuclideanSpace ℂ n} (ha : IsRealField bar a)
    (hdiv : ∀ k, wavePairing (κ k) (a k) = 0) :
    ∑ k, inner ℂ (a k) (feed κ (fun k => leray (κ k)) a k) = -I * triadSum κ a := by
  classical
  simp_rw [inner_feed_leray κ a _ (hdiv _), inner_eq_dot_of_real ha, sum_triads_eq]
  rw [← Finset.mul_sum]
  congr 1
  -- reindex the receiving mode by `bar`
  rw [← Equiv.sum_comp (Function.Involutive.toPerm bar hs.involutive)]
  simp only [Function.Involutive.coe_toPerm, hs.involutive _, hs.wave_bar]
  unfold triadSum
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun r _ => ?_
  have h : (κ p + κ q = -κ r) ↔ (κ p + κ q + κ r = 0) := eq_neg_iff_add_eq_zero
  simp only [h]

/-- [proved-derived; formal-checked] **The feed does no work.** On a real field across its wave
vectors over a symmetric set, `∑ k, ⟪a_k, N_k⟫ = 0`. -/
theorem sum_inner_feed_leray_eq_zero {κ : ι → EuclideanSpace ℝ n} {bar : ι → ι}
    (hs : WaveSymmetric κ bar) {a : ι → EuclideanSpace ℂ n} (ha : IsRealField bar a)
    (hdiv : ∀ k, wavePairing (κ k) (a k) = 0) :
    ∑ k, inner ℂ (a k) (feed κ (fun k => leray (κ k)) a k) = 0 := by
  rw [sum_inner_feed_leray hs ha hdiv, triadSum_eq_zero κ a hdiv, mul_zero]

/-- [proved-derived; formal-checked] The same in the real inner product that `Conservative`
reads. -/
theorem sum_real_inner_feed_leray_eq_zero {κ : ι → EuclideanSpace ℝ n} {bar : ι → ι}
    (hs : WaveSymmetric κ bar) {a : ι → EuclideanSpace ℂ n} (ha : IsRealField bar a)
    (hdiv : ∀ k, wavePairing (κ k) (a k) = 0) :
    ∑ k, inner ℝ (a k) (feed κ (fun k => leray (κ k)) a k) = 0 := by
  simp_rw [real_inner_eq_re_inner']
  rw [← Complex.re_sum, sum_inner_feed_leray_eq_zero hs ha hdiv, Complex.zero_re]

end Work

/-! ## T3. The energy equality of the truncated fluid, with no hypothesis on the feed -/

section Energy

variable {n : Type*} [Fintype n] {ι : Type*} [Fintype ι]
  {κ : ι → EuclideanSpace ℝ n} {ν : ℝ} {a : ℝ → ι → EuclideanSpace ℂ n} {bar : ι → ι}

/-- [proved-derived; formal-checked] **The truncated fluid's feed is conservative.** A truncation
with Leray's projections, over a symmetric set, whose state is a real field at every time. -/
theorem _root_.Holonics.Fluid.GalerkinInstance.Truncation.conservative_of_real (h : Truncation κ ν (fun k => leray (κ k)) a)
    (hs : WaveSymmetric κ bar) (ha : ∀ t, 0 ≤ t → IsRealField bar (a t)) :
    Conservative a (fun t => feed κ (fun k => leray (κ k)) (a t)) :=
  fun t ht => sum_real_inner_feed_leray_eq_zero hs (ha t ht) (h.incompressible t ht)

theorem _root_.Holonics.Fluid.GalerkinInstance.Truncation.evolves' (h : Truncation κ ν (fun k => leray (κ k)) a) :
    Evolves (fun k => ‖κ k‖) ν a (fun t => feed κ (fun k => leray (κ k)) (a t)) :=
  h.evolves

/-- [proved-derived; formal-checked] **The energy equality of the truncated fluid.**
`E t + ν * ∫ s in 0..t, ∑ k, ‖κ k‖ ^ 2 * ‖a s k‖ ^ 2 = E 0` at every `0 ≤ t`, for every size of
the data and every symmetric truncation, with no hypothesis on the feed. -/
theorem _root_.Holonics.Fluid.GalerkinInstance.Truncation.energy_add_dissipation_of_real (h : Truncation κ ν (fun k => leray (κ k)) a)
    (hs : WaveSymmetric κ bar) (ha : ∀ t, 0 ≤ t → IsRealField bar (a t)) {t : ℝ} (ht : 0 ≤ t) :
    energy (a t) + ν * ∫ s in (0 : ℝ)..t, dissipationRate (fun k => ‖κ k‖) (a s)
      = energy (a 0) :=
  energy_add_dissipation h.evolves' (h.conservative_of_real hs ha) ht

/-- [proved-derived; formal-checked] The truncated fluid's energy never passes its opening
value. -/
theorem _root_.Holonics.Fluid.GalerkinInstance.Truncation.energy_le_initial_of_real (h : Truncation κ ν (fun k => leray (κ k)) a)
    (hs : WaveSymmetric κ bar) (ha : ∀ t, 0 ≤ t → IsRealField bar (a t)) {t : ℝ} (ht : 0 ≤ t) :
    energy (a t) ≤ energy (a 0) :=
  energy_le_initial h.viscosity_pos.le h.evolves' (h.conservative_of_real hs ha) ht

/-- [proved-derived; formal-checked] The dissipation of the truncated fluid is paid within its
opening energy: `ν * ∫ s in 0..t, ∑ k, ‖κ k‖ ^ 2 * ‖a s k‖ ^ 2 ≤ E 0`. -/
theorem _root_.Holonics.Fluid.GalerkinInstance.Truncation.integral_dissipationRate_le_of_real
    (h : Truncation κ ν (fun k => leray (κ k)) a)
    (hs : WaveSymmetric κ bar) (ha : ∀ t, 0 ≤ t → IsRealField bar (a t)) {t : ℝ} (ht : 0 ≤ t) :
    ν * ∫ s in (0 : ℝ)..t, dissipationRate (fun k => ‖κ k‖) (a s) ≤ energy (a 0) := by
  have h1 := h.energy_add_dissipation_of_real hs ha ht
  have h2 := energy_nonneg (a t)
  linarith

end Energy

/-! ## T4. The law keeps the real, incompressible states -/

section Invariance

variable {n : Type*} [Fintype n] {ι : Type*} [Fintype ι]

/-- [proved-derived; formal-checked] Leray's projection in coordinates:
`(leray q v) j = v j - (q · v / ‖q̂‖²) * q j`. -/
theorem leray_apply (q : EuclideanSpace ℝ n) (v : EuclideanSpace ℂ n) (j : n) :
    leray q v j
      = v j - wavePairing q v / ((‖complexify q‖ ^ 2 : ℝ) : ℂ) * (q j : ℂ) := by
  unfold leray
  rw [Submodule.starProjection_orthogonal_val, Submodule.starProjection_singleton,
    ← wavePairing_eq_inner]
  simp [complexify]

omit [Fintype n] in
theorem complexify_neg (q : EuclideanSpace ℝ n) : complexify (-q) = -complexify q := by
  ext j
  simp [complexify]

/-- [proved-derived; formal-checked] Leray's projection is the same across `q` and `-q`. -/
theorem leray_neg (q : EuclideanSpace ℝ n) (v : EuclideanSpace ℂ n) :
    leray (-q) v = leray q v := by
  ext j
  rw [leray_apply, leray_apply, complexify_neg, norm_neg, wavePairing_neg]
  simp only [PiLp.neg_apply]
  push_cast
  ring

/-- The wave pairing of a conjugated amplitude is the conjugate pairing. -/
theorem wavePairing_conj (q : EuclideanSpace ℝ n) {v w : EuclideanSpace ℂ n}
    (hw : ∀ j, w j = conj (v j)) : wavePairing q w = conj (wavePairing q v) := by
  unfold wavePairing
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hw j, map_mul, Complex.conj_ofReal]

/-- [proved-derived; formal-checked] Leray's projection commutes with conjugation, its wave
vector being real. -/
theorem leray_conj (q : EuclideanSpace ℝ n) {v w : EuclideanSpace ℂ n}
    (hw : ∀ j, w j = conj (v j)) (j : n) : leray q w j = conj (leray q v j) := by
  rw [leray_apply, leray_apply, wavePairing_conj q hw, hw j, map_sub, map_mul, map_div₀,
    Complex.conj_ofReal, Complex.conj_ofReal]

/-- [definition] The transport sum into a mode, before the projection. -/
def transport (κ : ι → EuclideanSpace ℝ n) (a : ι → EuclideanSpace ℂ n) (k : ι) :
    EuclideanSpace ℂ n :=
  ∑ pq ∈ triads κ k, wavePairing (κ pq.2) (a pq.1) • a pq.2

theorem feed_eq_transport (κ : ι → EuclideanSpace ℝ n)
    (P : ι → EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) (a : ι → EuclideanSpace ℂ n) (k : ι) :
    feed κ P a k = (-I) • P k (transport κ a k) := rfl

/-- [proved-derived; formal-checked] On a real field over a symmetric set, the transport into
`bar k` is minus the conjugate of the transport into `k`. -/
theorem transport_bar {κ : ι → EuclideanSpace ℝ n} {bar : ι → ι} (hs : WaveSymmetric κ bar)
    {a : ι → EuclideanSpace ℂ n} (ha : IsRealField bar a) (k : ι) (j : n) :
    transport κ a (bar k) j = -conj (transport κ a k j) := by
  classical
  unfold transport
  have hsum : ∀ m, (∑ pq ∈ triads κ m, wavePairing (κ pq.2) (a pq.1) • a pq.2) j
      = ∑ p, ∑ q, if κ p + κ q = κ m then wavePairing (κ q) (a p) * a q j else 0 := by
    intro m
    rw [WithLp.ofLp_sum, Finset.sum_apply]
    rw [sum_triads_eq κ m (fun pq => (wavePairing (κ pq.2) (a pq.1) • a pq.2) j)]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    simp
  rw [hsum, hsum]
  rw [map_sum, ← Finset.sum_neg_distrib]
  rw [← Equiv.sum_comp (Function.Involutive.toPerm bar hs.involutive)]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_sum, ← Finset.sum_neg_distrib]
  rw [← Equiv.sum_comp (Function.Involutive.toPerm bar hs.involutive)]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [Function.Involutive.coe_toPerm, hs.wave_bar]
  have hc : (-κ p + -κ q = -κ k) ↔ (κ p + κ q = κ k) := by
    rw [← neg_add, neg_inj]
  simp only [hc]
  split_ifs
  · have hw : ∀ i, a (bar p) i = conj (a p i) := ha p
    rw [wavePairing_neg, wavePairing_conj (κ q) hw, ha q j, map_mul]
    ring
  · simp

/-- [proved-derived; formal-checked] **The feed of a real field is a real field.** -/
theorem feed_leray_isRealField {κ : ι → EuclideanSpace ℝ n} {bar : ι → ι}
    (hs : WaveSymmetric κ bar) {a : ι → EuclideanSpace ℂ n} (ha : IsRealField bar a) :
    IsRealField bar (fun k => feed κ (fun k => leray (κ k)) a k) := by
  intro k j
  simp only [feed_eq_transport, hs.wave_bar, leray_neg]
  -- the transport into `bar k` is `-w` with `w` the conjugate of the transport into `k`
  set w : EuclideanSpace ℂ n := WithLp.toLp 2 fun i => conj (transport κ a k i) with hwdef
  have hw : ∀ i, w i = conj (transport κ a k i) := fun i => by simp [hwdef]
  have ht : transport κ a (bar k) = -w := by
    ext i
    rw [transport_bar hs ha k i, PiLp.neg_apply, hw i]
  rw [ht, map_neg, PiLp.smul_apply, PiLp.smul_apply, PiLp.neg_apply,
    leray_conj (κ k) hw j, smul_eq_mul, smul_eq_mul, map_mul, map_neg, Complex.conj_I]
  ring

theorem wavePairing_add_right (q : EuclideanSpace ℝ n) (x y : EuclideanSpace ℂ n) :
    wavePairing q (x + y) = wavePairing q x + wavePairing q y := by
  unfold wavePairing
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [PiLp.add_apply, mul_add]

theorem wavePairing_real_smul (q : EuclideanSpace ℝ n) (r : ℝ) (x : EuclideanSpace ℂ n) :
    wavePairing q (r • x) = (r : ℂ) * wavePairing q x := by
  unfold wavePairing
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [PiLp.smul_apply, Complex.real_smul]
  ring

/-- [definition] The truncated field: `F(a)_k = -(ν ‖κ k‖²) • a_k + N_k`. -/
def field (κ : ι → EuclideanSpace ℝ n) (ν : ℝ) (a : ι → EuclideanSpace ℂ n) (k : ι) :
    EuclideanSpace ℂ n :=
  -(ν * ‖κ k‖ ^ 2) • a k + feed κ (fun k => leray (κ k)) a k

/-- [proved-derived; formal-checked] **The truncated field keeps the real fields.** -/
theorem field_isRealField {κ : ι → EuclideanSpace ℝ n} {bar : ι → ι} (hs : WaveSymmetric κ bar)
    (ν : ℝ) {a : ι → EuclideanSpace ℂ n} (ha : IsRealField bar a) :
    IsRealField bar (field κ ν a) := by
  intro k j
  unfold field
  rw [PiLp.add_apply, PiLp.add_apply, feed_leray_isRealField hs ha k j, hs.wave_bar, norm_neg,
    PiLp.smul_apply, PiLp.smul_apply, ha k j, map_add]
  congr 1
  rw [Complex.real_smul, Complex.real_smul, map_mul, Complex.conj_ofReal]

/-- [proved-derived; formal-checked] **The truncated field is across its wave vectors** when the
state is. -/
theorem wavePairing_field_eq_zero (κ : ι → EuclideanSpace ℝ n) (ν : ℝ)
    {a : ι → EuclideanSpace ℂ n} (hdiv : ∀ k, wavePairing (κ k) (a k) = 0) (k : ι) :
    wavePairing (κ k) (field κ ν a k) = 0 := by
  unfold field
  rw [wavePairing_add_right, wavePairing_feed_leray, add_zero, wavePairing_real_smul, hdiv k,
    mul_zero]

end Invariance

/-! ## T5. In two dimensions the feed also conserves the second count -/

section Weighted

variable {n : Type*} [Fintype n] {ι : Type*} [Fintype ι]

open Classical in
/-- [definition] The triad sum weighted at the receiving mode `r` by `g r`. -/
def weightedTriadSum (g : ι → ℝ) (κ : ι → EuclideanSpace ℝ n) (a : ι → EuclideanSpace ℂ n) :
    ℂ :=
  ∑ p, ∑ q, ∑ r, if κ p + κ q + κ r = 0 then
    wavePairing (κ q) (a p) * dot (a q) (a r) * (g r : ℂ) else 0

/-- [proved-derived; formal-checked] On a real field over a symmetric set, the work of the feed
in a count weighted by `g` with `g (bar k) = g k` is `-i` times the weighted triad sum. -/
theorem sum_weighted_inner_feed_leray {κ : ι → EuclideanSpace ℝ n} {bar : ι → ι}
    (hs : WaveSymmetric κ bar) {g : ι → ℝ} (hg : ∀ k, g (bar k) = g k)
    {a : ι → EuclideanSpace ℂ n} (ha : IsRealField bar a)
    (hdiv : ∀ k, wavePairing (κ k) (a k) = 0) :
    ∑ k, (g k : ℂ) * inner ℂ (a k) (feed κ (fun k => leray (κ k)) a k)
      = -I * weightedTriadSum g κ a := by
  classical
  simp_rw [inner_feed_leray κ a _ (hdiv _), inner_eq_dot_of_real ha, sum_triads_eq]
  simp_rw [mul_left_comm _ (-I), ← Finset.mul_sum]
  congr 1
  rw [← Equiv.sum_comp (Function.Involutive.toPerm bar hs.involutive)]
  simp only [Function.Involutive.coe_toPerm, hs.involutive _, hs.wave_bar, hg]
  unfold weightedTriadSum
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun r _ => ?_
  have h : (κ p + κ q = -κ r) ↔ (κ p + κ q + κ r = 0) := eq_neg_iff_add_eq_zero
  simp only [h]
  split_ifs <;> ring

end Weighted

section TwoD

variable {ι : Type*} [Fintype ι]

/-- [definition] The quarter-turn of a wave vector of the plane, read in the amplitude space:
`perp q = (-q₁, q₀)`. -/
def perp (q : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℂ (Fin 2) :=
  WithLp.toLp 2 ![-((q 1 : ℝ) : ℂ), ((q 0 : ℝ) : ℂ)]

/-- [definition] The stream amplitude of an amplitude across `q`:
`ψ = (perp q · a) / ‖q‖²`. -/
def stream (q : EuclideanSpace ℝ (Fin 2)) (a : EuclideanSpace ℂ (Fin 2)) : ℂ :=
  (-((q 1 : ℝ) : ℂ) * a 0 + ((q 0 : ℝ) : ℂ) * a 1) / (((q 0 ^ 2 + q 1 ^ 2 : ℝ)) : ℂ)

theorem wavePairing_fin_two (q : EuclideanSpace ℝ (Fin 2)) (a : EuclideanSpace ℂ (Fin 2)) :
    wavePairing q a = (q 0 : ℂ) * a 0 + (q 1 : ℂ) * a 1 := by
  unfold wavePairing
  rw [Fin.sum_univ_two]

theorem sq_add_sq_ne_zero {q : EuclideanSpace ℝ (Fin 2)} (hq : q ≠ 0) : q 0 ^ 2 + q 1 ^ 2 ≠ 0 := by
  intro h
  apply hq
  have h0 : q 0 = 0 := by nlinarith [sq_nonneg (q 0), sq_nonneg (q 1)]
  have h1 : q 1 = 0 := by nlinarith [sq_nonneg (q 0), sq_nonneg (q 1)]
  ext j
  fin_cases j
  · simpa using h0
  · simpa using h1

/-- [proved-derived; formal-checked] **In the plane an amplitude across its wave vector is a stream
amplitude times the quarter-turn of the wave vector.** -/
theorem eq_stream_smul_perp {q : EuclideanSpace ℝ (Fin 2)} (hq : q ≠ 0)
    {a : EuclideanSpace ℂ (Fin 2)} (ha : wavePairing q a = 0) : a = stream q a • perp q := by
  have hD : (((q 0 ^ 2 + q 1 ^ 2 : ℝ)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (sq_add_sq_ne_zero hq)
  rw [wavePairing_fin_two] at ha
  ext j
  fin_cases j
  · simp only [Fin.zero_eta, Fin.isValue, PiLp.smul_apply, smul_eq_mul, stream, perp]
    simp only [Fin.isValue, Matrix.cons_val_zero]
    field_simp
    push_cast
    linear_combination (q 0 : ℂ) * ha
  · simp only [Fin.mk_one, Fin.isValue, PiLp.smul_apply, smul_eq_mul, stream, perp]
    simp only [Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    field_simp
    push_cast
    linear_combination (q 1 : ℂ) * ha

theorem wavePairing_smul (q : EuclideanSpace ℝ (Fin 2)) (c : ℂ) (x : EuclideanSpace ℂ (Fin 2)) :
    wavePairing q (c • x) = c * wavePairing q x := by
  rw [wavePairing_fin_two, wavePairing_fin_two, PiLp.smul_apply, PiLp.smul_apply, smul_eq_mul,
    smul_eq_mul]
  ring

theorem dot_smul_smul (c d : ℂ) (x y : EuclideanSpace ℂ (Fin 2)) :
    dot (c • x) (d • y) = c * d * dot x y := by
  unfold dot
  rw [Fin.sum_univ_two, Fin.sum_univ_two, PiLp.smul_apply, PiLp.smul_apply, PiLp.smul_apply,
    PiLp.smul_apply, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul]
  ring

/-- The transport of a quarter-turned amplitude is the cross product of the wave vectors. -/
theorem wavePairing_perp (q p : EuclideanSpace ℝ (Fin 2)) :
    wavePairing q (perp p) = ((p 0 * q 1 - p 1 * q 0 : ℝ) : ℂ) := by
  rw [wavePairing_fin_two]
  simp [perp]
  ring

/-- The pairing of two quarter-turned amplitudes is the dot product of the wave vectors. -/
theorem dot_perp (q r : EuclideanSpace ℝ (Fin 2)) :
    dot (perp q) (perp r) = ((q 0 * r 0 + q 1 * r 1 : ℝ) : ℂ) := by
  unfold dot
  rw [Fin.sum_univ_two]
  simp [perp]
  ring

theorem norm_sq_fin_two (q : EuclideanSpace ℝ (Fin 2)) : ‖q‖ ^ 2 = q 0 ^ 2 + q 1 ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]

/-- [definition] The geometric factor of one ordered triad in the second count:
`(x × y) (y · z) ‖z‖²`. -/
def triadGeometry (x y z : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  (x 0 * y 1 - x 1 * y 0) * (y 0 * z 0 + y 1 * z 1) * (z 0 ^ 2 + z 1 ^ 2)

/-- [proved-derived; formal-checked] **The six orderings of a closed triad of the plane cancel in
the second count.** -/
theorem triadGeometry_perm_sum {x y z : EuclideanSpace ℝ (Fin 2)} (h : x + y + z = 0) :
    triadGeometry x y z + triadGeometry y z x + triadGeometry z x y
      + triadGeometry x z y + triadGeometry z y x + triadGeometry y x z = 0 := by
  have hz0 : z 0 = -x 0 - y 0 := by
    have := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 0) h
    simp only [PiLp.add_apply, PiLp.zero_apply] at this
    linarith
  have hz1 : z 1 = -x 1 - y 1 := by
    have := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 1) h
    simp only [PiLp.add_apply, PiLp.zero_apply] at this
    linarith
  unfold triadGeometry
  rw [hz0, hz1]
  ring

/-- The permutations of a triple of modes, as equivalences. -/
def cycEquiv (ι : Type*) : ι × ι × ι ≃ ι × ι × ι where
  toFun x := (x.2.1, x.2.2, x.1)
  invFun x := (x.2.2, x.1, x.2.1)
  left_inv _ := rfl
  right_inv _ := rfl

def swapEquiv (ι : Type*) : ι × ι × ι ≃ ι × ι × ι where
  toFun x := (x.1, x.2.2, x.2.1)
  invFun x := (x.1, x.2.2, x.2.1)
  left_inv _ := rfl
  right_inv _ := rfl

open Classical in
/-- [proved-derived; formal-checked] **The second count's triad identity in the plane.** For
nonzero wave vectors and amplitudes across them, the triad sum weighted by `‖κ r‖²` vanishes. -/
theorem weightedTriadSum_normSq_eq_zero (κ : ι → EuclideanSpace ℝ (Fin 2))
    (a : ι → EuclideanSpace ℂ (Fin 2)) (hκ0 : ∀ k, κ k ≠ 0)
    (hdiv : ∀ k, wavePairing (κ k) (a k) = 0) :
    weightedTriadSum (fun k => ‖κ k‖ ^ 2) κ a = 0 := by
  set ψ : ι → ℂ := fun k => stream (κ k) (a k) with hψ
  have ha : ∀ k, a k = ψ k • perp (κ k) := fun k => eq_stream_smul_perp (hκ0 k) (hdiv k)
  let F : ι × ι × ι → ℂ := fun x =>
    if κ x.1 + κ x.2.1 + κ x.2.2 = 0 then
      ψ x.1 * ψ x.2.1 * ψ x.2.2 * (triadGeometry (κ x.1) (κ x.2.1) (κ x.2.2) : ℂ) else 0
  have hS : weightedTriadSum (fun k => ‖κ k‖ ^ 2) κ a = ∑ x, F x := by
    unfold weightedTriadSum
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun r _ => ?_
    simp only [F]
    split_ifs
    · rw [ha p, ha q, ha r, wavePairing_smul, dot_smul_smul, wavePairing_perp, dot_perp,
        norm_sq_fin_two]
      unfold triadGeometry
      push_cast
      ring
    · rfl
  have hc : ∀ x, F x + F (cycEquiv ι x) + F (cycEquiv ι (cycEquiv ι x)) + F (swapEquiv ι x)
      + F (swapEquiv ι (cycEquiv ι x)) + F (swapEquiv ι (cycEquiv ι (cycEquiv ι x))) = 0 := by
    rintro ⟨p, q, r⟩
    simp only [F, cycEquiv, swapEquiv, Equiv.coe_fn_mk]
    have e1 : κ q + κ r + κ p = κ p + κ q + κ r := by abel
    have e2 : κ r + κ p + κ q = κ p + κ q + κ r := by abel
    have e3 : κ p + κ r + κ q = κ p + κ q + κ r := by abel
    have e4 : κ q + κ p + κ r = κ p + κ q + κ r := by abel
    have e5 : κ r + κ q + κ p = κ p + κ q + κ r := by abel
    rw [e1, e2, e3, e4, e5]
    split_ifs with hcl
    · have hG := triadGeometry_perm_sum hcl
      have hG' : ((triadGeometry (κ p) (κ q) (κ r) + triadGeometry (κ q) (κ r) (κ p)
          + triadGeometry (κ r) (κ p) (κ q) + triadGeometry (κ p) (κ r) (κ q)
          + triadGeometry (κ r) (κ q) (κ p) + triadGeometry (κ q) (κ p) (κ r) : ℝ) : ℂ) = 0 := by
        rw [hG, Complex.ofReal_zero]
      push_cast at hG'
      linear_combination (ψ p * ψ q * ψ r) * hG'
    · ring
  have h6 : (6 : ℂ) * ∑ x, F x = 0 := by
    have e1 : ∑ x, F (cycEquiv ι x) = ∑ x, F x := Equiv.sum_comp _ F
    have e2 : ∑ x, F (cycEquiv ι (cycEquiv ι x)) = ∑ x, F x :=
      Equiv.sum_comp ((cycEquiv ι).trans (cycEquiv ι)) F
    have e3 : ∑ x, F (swapEquiv ι x) = ∑ x, F x := Equiv.sum_comp _ F
    have e4 : ∑ x, F (swapEquiv ι (cycEquiv ι x)) = ∑ x, F x :=
      Equiv.sum_comp ((cycEquiv ι).trans (swapEquiv ι)) F
    have e5 : ∑ x, F (swapEquiv ι (cycEquiv ι (cycEquiv ι x))) = ∑ x, F x :=
      Equiv.sum_comp (((cycEquiv ι).trans (cycEquiv ι)).trans (swapEquiv ι)) F
    have hsum := Finset.sum_eq_zero (s := Finset.univ) fun x (_ : x ∈ Finset.univ) => hc x
    simp only [Finset.sum_add_distrib] at hsum
    rw [e1, e2, e3, e4, e5] at hsum
    linear_combination hsum
  rw [hS]
  have h6' : (6 : ℂ) ≠ 0 := by norm_num
  exact (mul_eq_zero.mp h6).resolve_left h6'

/-- [proved-derived; formal-checked] **In two dimensions the truncated fluid's feed conserves the
second count.** On a real field across nonzero wave vectors over a symmetric set,
`∑ k, ‖κ k‖² Re ⟪a_k, N_k⟫ = 0`. -/
theorem sum_normSq_real_inner_feed_leray_eq_zero {κ : ι → EuclideanSpace ℝ (Fin 2)}
    {bar : ι → ι} (hs : WaveSymmetric κ bar) (hκ0 : ∀ k, κ k ≠ 0)
    {a : ι → EuclideanSpace ℂ (Fin 2)} (ha : IsRealField bar a)
    (hdiv : ∀ k, wavePairing (κ k) (a k) = 0) :
    ∑ k, ‖κ k‖ ^ 2 * inner ℝ (a k) (feed κ (fun k => leray (κ k)) a k) = 0 := by
  have hg : ∀ k, (fun k => ‖κ k‖ ^ 2) (bar k) = (fun k => ‖κ k‖ ^ 2) k := fun k => by
    simp only [hs.wave_bar, norm_neg]
  have hC := sum_weighted_inner_feed_leray hs (g := fun k => ‖κ k‖ ^ 2) hg ha hdiv
  rw [weightedTriadSum_normSq_eq_zero κ a hκ0 hdiv, mul_zero] at hC
  have hre := congrArg Complex.re hC
  rw [Complex.re_sum, Complex.zero_re] at hre
  rw [← hre]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [real_inner_eq_re_inner', Complex.re_ofReal_mul]

variable {ν : ℝ} {κ : ι → EuclideanSpace ℝ (Fin 2)} {a : ℝ → ι → EuclideanSpace ℂ (Fin 2)}
  {bar : ι → ι}

/-- [proved-derived; formal-checked] A plane truncation with Leray's projections whose state is a
real field at every time conserves the second count. -/
theorem _root_.Holonics.Fluid.GalerkinInstance.Truncation.weightedConservative_of_real_two
    (h : Truncation κ ν (fun k => leray (κ k)) a) (hs : WaveSymmetric κ bar)
    (ha : ∀ t, 0 ≤ t → IsRealField bar (a t)) :
    WeightedConservative (fun k => ‖κ k‖ ^ 2) a (fun t => feed κ (fun k => leray (κ k)) (a t)) :=
  fun t ht => sum_normSq_real_inner_feed_leray_eq_zero hs h.wave_ne_zero (ha t ht)
    (h.incompressible t ht)

/-- [proved-derived; formal-checked] **The plane truncated fluid's critical reading is bounded at
every size of the data.** `X t ≤ √(∑ k, ‖κ k‖ ^ (-4)) * √(2 * E₂ 0)` at every `0 ≤ t`, with
`E₂ = ½ ∑ ‖κ k‖² ‖a_k‖²`, no smallness and no feed bound: the hypothesis of
`critical_le_of_second_count` is the fluid's own in two dimensions. -/
theorem _root_.Holonics.Fluid.GalerkinInstance.Truncation.critical_le_of_real_two
    (h : Truncation κ ν (fun k => leray (κ k)) a) (hs : WaveSymmetric κ bar)
    (ha : ∀ t, 0 ≤ t → IsRealField bar (a t)) {t : ℝ} (ht : 0 ≤ t) :
    criticalNorm (fun k => ‖κ k‖) (a t) ≤
      √(∑ k, ‖κ k‖ ^ (-4 : ℤ)) * √(2 * weightedEnergy (fun k => ‖κ k‖ ^ 2) (a 0)) :=
  critical_le_of_second_count (fun k => norm_pos_iff.mpr (h.wave_ne_zero k))
    h.viscosity_pos.le h.evolves' (h.weightedConservative_of_real_two hs ha) ht

end TwoD

/-! ## Audit -/

section Audit

#print axioms triadSum_eq_zero
#print axioms sum_inner_feed_leray_eq_zero
#print axioms sum_real_inner_feed_leray_eq_zero
#print axioms Truncation.conservative_of_real
#print axioms Truncation.energy_add_dissipation_of_real
#print axioms Truncation.energy_le_initial_of_real
#print axioms Truncation.integral_dissipationRate_le_of_real
#print axioms leray_neg
#print axioms leray_conj
#print axioms transport_bar
#print axioms feed_leray_isRealField
#print axioms field_isRealField
#print axioms wavePairing_field_eq_zero
#print axioms sum_weighted_inner_feed_leray
#print axioms eq_stream_smul_perp
#print axioms triadGeometry_perm_sum
#print axioms weightedTriadSum_normSq_eq_zero
#print axioms sum_normSq_real_inner_feed_leray_eq_zero
#print axioms Truncation.weightedConservative_of_real_two
#print axioms Truncation.critical_le_of_real_two

end Audit

end Holonics.Fluid.TriadConservation
