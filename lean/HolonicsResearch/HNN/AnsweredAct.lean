import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

/-!
# An act is read by its answer: an unanswered act carries no news, a probe reads its loop, every medium propagates and fades by its quality, a boundary reads by its ports, and a rhythm is a period carried

Atlas: `receipt.unanswered-act-is-discounted`, `receipt.probe-reads-its-loop`, `swing.zero-mean-probe-reads-slope`,
`wave.fade-per-turn-is-the-quality`, `wave.one-propagation-two-ratios`, `contact.handed-turn-travels`,
`pair.crossing-sum-and-difference`, `receiver.boundary-ports-count`, `lock.carried-period-reads-no-news`. Record:
`research/records/2026-11-23_PLAY_IS_AN_ACT_ANSWERED_IN_KIND_…` (§3 to §7).

Most of the law has its owners, named where each is used: a world that answers the field's own act and the friction at its answer
(`receipt.world-answers-own-act`), a receiver cancelling its own release at its own clock's phase (`receipt.reafference-lag`), the
replicator's rise at its fitness's variance (`Compression/FacesOnCycles`), the telegraph constitution and its modes
(`em.telegrapher-constitution`, `heat.cattaneo-modes`), an interior eliminated to its boundary relation (`tube.staged-elimination`)
and a phase's lock (`lock.phase-viability`). This module holds the statements those rows do not.

1. **An unanswered act carries no news of what it is compared with** (`unanswered_act_marginal`, `unanswered_act_conditional`). A
   context `c`, an act `d` drawn from the context alone, a hidden continuation `r` drawn from the context alone, and a target `x`
   drawn from the context and the hidden continuation. Summed over the hidden continuation, the joint law is the act's law times a
   term the act does not enter, so the target's law given the context and the act is the same for every act. A comparison of that
   target at a reader that holds the act as context has its least code where the reader ignores the act.
2. **A probe reads its loop** (`probe_reads_loop`, `unsubtracted_act_power`). A reading `w t + l * a t` of a world `w` and of the
   reader's own act `a` through a loop of gain `l`. Where the act is uncorrelated with the world over the dwell, the reading
   demodulated against the act is the gain times the act's power, whatever the world is; and the reading's power is the world's
   plus the loop's, so an own act that is not subtracted stands in the reading as news.
3. **A zero-mean probe reads the slope and moves the mean at second order** (`probe_mean_quadratic`, `probe_demodulates_slope`,
   `probe_step_gain`). On a response with a slope and a curvature, a probe whose sum is zero leaves the summed response as it was
   but for the curvature times the probe's power; demodulated against itself it returns the slope at the operating point times its
   power; and a step along that slope gains the slope's square times the step, less the curvature's term.
4. **Every medium propagates, and fades by its quality** (`fade_lt_turn`, `fade_per_turn`, `fade_per_turn_viscous`,
   `diffusion_wavenumber`, `diffusion_phase_speed`, `telegraph_complex_diffusivity`). A wavenumber `a + i b` whose square has real
   part `A > 0` and imaginary part `B`: the fading part is less than the turning part, and their ratio `t` satisfies
   `t / (1 − t²) = B / (2A)`, one over twice the medium's quality at that frequency. A friction on the flow and a friction on the
   strain rate give the same form. At the end where the real part vanishes the two parts are equal, and the disturbance still
   travels: its phase moves at `ω δ` with `(ω δ)² = 2 D ω`. The telegraph constitution at one clock is a diffusion whose
   diffusivity is complex, at the angle `arctan (ω/γ)`: a wave and a diffusion are one law read at two ratios of the reader's
   clock to the medium's relaxation.
5. **A boundary reads by its ports** (`response_from_upper`, `star_spoke_from_three_ports`, `two_ports_one_number`). A reciprocal
   response with nothing made or lost inside is fixed by its entries above the diagonal, so `n` ports carry at most `n(n − 1)/2`
   numbers of any interior. Three ports of a star read each spoke. Two ports read one number, and two interiors share it.
6. **A rhythm is a period carried** (`follower_standing_error`, `carried_period_no_error`). A receiver that corrects its phase
   alone stands off a steady beat by the detuning over its gain; one that also carries the period as a state stands at no error
   and holds the beat's own period.
7. **A handed turn travels where each member carries it** (`settled_mode_discriminant`, `handed_turn_travels`). Members joined by
   contacts of stiffness `J`, each carrying its turn with inertia `χ` against a friction `η`: a mode of the contacts' eigenvalue
   `λ` settles without turning only where `4 χ J λ ≤ η²`, and above that bound it has no real rate. With no carried turn
   (`χ = 0`) every mode settles (`contact.alignment-spectral-gap`).
8. **Two trains that cross answer at their sum and their difference** (`crossing_sum_and_difference`). The product of two real
   oscillations is half a term that turns at the sum of their rates and half a term that turns at the difference, so a medium or
   a receiver quadratic in the motion hands two trains' power to a third (`pair.beat-is-slip`, `contact.triad-manley-rowe-gauge`).

The computational object is the helical pair interaction: an act and its answer are the two strands of one contact. Of the winding
guide's six objects this touches the pair (a loop's gain is a contact's), faces and placement (the answer's places are the only
places compared), the tube (a medium's turn and fade along its length) and the helix (a carried period); cell holonomy and the tower
thread stay attached through the owners above.
-/

namespace Holonics.HNN.AnsweredAct

open Finset

/-- **An unanswered act's joint law factors.** The act `d` enters the law of `(c, d, x)` only through its own draw. -/
theorem unanswered_act_marginal {C D R X : Type*} [Fintype R] (μ : C → ℝ) (π : C → D → ℝ) (ρ : C → R → ℝ)
    (q : C → R → X → ℝ) (c : C) (d : D) (x : X) :
    ∑ r, μ c * π c d * ρ c r * q c r x = π c d * (μ c * ∑ r, ρ c r * q c r x) := by
  rw [Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun r _ => by ring

/-- **An unanswered act carries no news of its target.** The target's law given the context and the act is the same for every act
the context can draw. -/
theorem unanswered_act_conditional {C D R X : Type*} [Fintype R] [Fintype X] (μ : C → ℝ) (π : C → D → ℝ) (ρ : C → R → ℝ)
    (q : C → R → X → ℝ) (c : C) (d d' : D) (hd : π c d ≠ 0) (hd' : π c d' ≠ 0) (x : X) :
    (∑ r, μ c * π c d * ρ c r * q c r x) / (∑ y, ∑ r, μ c * π c d * ρ c r * q c r y)
      = (∑ r, μ c * π c d' * ρ c r * q c r x) / (∑ y, ∑ r, μ c * π c d' * ρ c r * q c r y) := by
  have h : ∀ e, ∑ y, ∑ r, μ c * π c e * ρ c r * q c r y = π c e * ∑ y, μ c * ∑ r, ρ c r * q c r y := fun e => by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => unanswered_act_marginal μ π ρ q c e y
  rw [unanswered_act_marginal μ π ρ q c d x, unanswered_act_marginal μ π ρ q c d' x, h d, h d',
    mul_div_mul_left _ _ hd, mul_div_mul_left _ _ hd']

/-- **A probe reads its loop.** An act uncorrelated with the world over a dwell returns the loop's gain times its own power. -/
theorem probe_reads_loop {ι : Type*} (s : Finset ι) (w a : ι → ℝ) (l : ℝ) (h : ∑ t ∈ s, w t * a t = 0) :
    ∑ t ∈ s, (w t + l * a t) * a t = l * ∑ t ∈ s, a t ^ 2 := by
  have e : ∀ t ∈ s, (w t + l * a t) * a t = w t * a t + l * a t ^ 2 := fun t _ => by ring
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, h, zero_add, Finset.mul_sum]

/-- **An act that is not subtracted stands as news.** The reading's power is the world's plus the loop's. -/
theorem unsubtracted_act_power {ι : Type*} (s : Finset ι) (w a : ι → ℝ) (l : ℝ) (h : ∑ t ∈ s, w t * a t = 0) :
    ∑ t ∈ s, (w t + l * a t) ^ 2 = ∑ t ∈ s, w t ^ 2 + l ^ 2 * ∑ t ∈ s, a t ^ 2 := by
  have e : ∀ t ∈ s, (w t + l * a t) ^ 2 = w t ^ 2 + 2 * l * (w t * a t) + l ^ 2 * a t ^ 2 := fun t _ => by ring
  have h2 : ∑ t ∈ s, 2 * l * (w t * a t) = 0 := by rw [← Finset.mul_sum, h, mul_zero]
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_add_distrib, h2, add_zero, Finset.mul_sum]

/-- **A zero-mean probe moves the mean at second order.** Over a probe whose sum is zero, a response with slope and curvature sums to
its value at rest for every tick, plus the curvature times the probe's power. -/
theorem probe_mean_quadratic {ι : Type*} (s : Finset ι) (a : ι → ℝ) (f0 g h u : ℝ) (hz : ∑ t ∈ s, a t = 0) :
    ∑ t ∈ s, (f0 + g * (u + a t) + h * (u + a t) ^ 2)
      = (s.card : ℝ) * (f0 + g * u + h * u ^ 2) + h * ∑ t ∈ s, a t ^ 2 := by
  have e : ∀ t ∈ s, f0 + g * (u + a t) + h * (u + a t) ^ 2
      = (f0 + g * u + h * u ^ 2) + (g + 2 * h * u) * a t + h * a t ^ 2 := fun t _ => by ring
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
    ← Finset.mul_sum, ← Finset.mul_sum, hz]
  ring

/-- **A zero-mean probe reads the slope.** Demodulated against itself, a probe with no first and no third moment returns the slope
at the operating point times its power. -/
theorem probe_demodulates_slope {ι : Type*} (s : Finset ι) (a : ι → ℝ) (f0 g h u : ℝ) (hz : ∑ t ∈ s, a t = 0)
    (h3 : ∑ t ∈ s, a t ^ 3 = 0) :
    ∑ t ∈ s, (f0 + g * (u + a t) + h * (u + a t) ^ 2) * a t = (g + 2 * h * u) * ∑ t ∈ s, a t ^ 2 := by
  have e : ∀ t ∈ s, (f0 + g * (u + a t) + h * (u + a t) ^ 2) * a t
      = (f0 + g * u + h * u ^ 2) * a t + (g + 2 * h * u) * a t ^ 2 + h * a t ^ 3 := fun t _ => by ring
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum, hz, h3]
  ring

/-- **A step along the read slope gains the slope's square.** With `σ = g + 2 h u` the slope at `u` and a step `η σ P`, the response
moves by `η σ² P` and by the curvature's term at second order in the step. -/
theorem probe_step_gain (f0 g h u η P : ℝ) :
    (f0 + g * (u + η * (g + 2 * h * u) * P) + h * (u + η * (g + 2 * h * u) * P) ^ 2) - (f0 + g * u + h * u ^ 2)
      = η * (g + 2 * h * u) ^ 2 * P + h * (η * (g + 2 * h * u) * P) ^ 2 := by
  ring

/-- **A medium fades less than it turns** wherever its wavenumber's square has a positive real part. -/
theorem fade_lt_turn (a b A : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hA : 0 < A) (h1 : a ^ 2 - b ^ 2 = A) : b < a := by
  by_contra hcon
  have hle : a ≤ b := not_lt.mp hcon
  nlinarith [mul_nonneg (sub_nonneg.mpr hle) (add_pos_of_pos_of_nonneg ha hb).le]

/-- **A medium fades by its quality.** With `t = b / a` the fade over the turn, `t / (1 − t²)` is the imaginary part of the
wavenumber's square over twice its real part. -/
theorem fade_per_turn (a b A B : ℝ) (ha : 0 < a) (hA : 0 < A) (h1 : a ^ 2 - b ^ 2 = A) (h2 : 2 * a * b = B) :
    (b / a) / (1 - (b / a) ^ 2) = B / (2 * A) := by
  have ha' : a ≠ 0 := ha.ne'
  have hA' : A ≠ 0 := hA.ne'
  have hden : 1 - (b / a) ^ 2 = A / a ^ 2 := by
    rw [← h1]
    field_simp
  rw [hden, ← h2]
  field_simp

/-- **A friction on the strain rate gives the same form**: where the imaginary part of the wavenumber's square is `s` times its real
part, the fade over the turn satisfies `t / (1 − t²) = s / 2`. -/
theorem fade_per_turn_viscous (a b s : ℝ) (ha : 0 < a) (hlt : 0 < a ^ 2 - b ^ 2) (h2 : 2 * a * b = s * (a ^ 2 - b ^ 2)) :
    (b / a) / (1 - (b / a) ^ 2) = s / 2 := by
  have hne : a ^ 2 - b ^ 2 ≠ 0 := hlt.ne'
  rw [fade_per_turn a b _ _ ha hlt rfl h2]
  field_simp

/-- **The diffusive end.** A wavenumber that fades as much as it turns squares to a pure imaginary: the relation of a diffusion. -/
theorem diffusion_wavenumber (a : ℝ) : (((1 : ℂ) + Complex.I) * a) ^ 2 = 2 * (a : ℂ) ^ 2 * Complex.I := by
  have h : ((1 : ℂ) + Complex.I) ^ 2 = 2 * Complex.I := by
    rw [add_sq, Complex.I_sq]
    ring
  rw [mul_pow, h]
  ring

/-- **A diffusion travels.** With `δ² = 2D/ω` the depth of a diffusion of diffusivity `D` at the clock `ω`, its phase moves at
`ω δ`, whose square is `2 D ω`: a speed above zero at every clock above zero. -/
theorem diffusion_phase_speed (D ω δ : ℝ) (hω : ω ≠ 0) (h : δ ^ 2 = 2 * D / ω) : (ω * δ) ^ 2 = 2 * D * ω := by
  rw [mul_pow, h]
  calc ω ^ 2 * (2 * D / ω) = 2 * D * ω * (ω / ω) := by ring
    _ = 2 * D * ω := by rw [div_self hω, mul_one]

/-- **One medium at every clock is a diffusion at an angle.** For the telegraph constitution `u_tt + γ u_t = c² u_xx` the
wavenumber's square is `(ω² + iγω)/c²`, which is `iω` over the complex diffusivity `c² (γ + iω)/(γ² + ω²)`. Its argument is
`arctan (ω/γ)`, the quality's angle: zero for a diffusion and a quarter turn for a wave that does not fade. Stated with the
denominators cleared. -/
theorem telegraph_complex_diffusivity (ω γ c : ℝ) :
    ((c : ℂ) ^ 2 * (γ + Complex.I * ω)) * ((ω : ℂ) ^ 2 + Complex.I * γ * ω)
      = Complex.I * ω * c ^ 2 * ((γ : ℂ) ^ 2 + (ω : ℂ) ^ 2) := by
  linear_combination ((c : ℂ) ^ 2 * γ * ω ^ 2) * Complex.I_sq

/-- **A reciprocal response with nothing made inside is fixed above its diagonal.** Two symmetric responses whose rows sum to zero
and which agree at every pair of distinct ports, read once, are one response. -/
theorem response_from_upper {n : ℕ} (M N : Fin n → Fin n → ℝ) (hM : ∀ i j, M i j = M j i) (hN : ∀ i j, N i j = N j i)
    (rM : ∀ i, ∑ j, M i j = 0) (rN : ∀ i, ∑ j, N i j = 0) (h : ∀ i j, i < j → M i j = N i j) : M = N := by
  have off : ∀ i j, i ≠ j → M i j = N i j := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact h i j hlt
    · rw [hM i j, hN i j]
      exact h j i hgt
  funext i j
  by_cases hij : i = j
  · subst hij
    have eM : M i i + ∑ j ∈ Finset.univ.erase i, M i j = ∑ j, M i j :=
      Finset.add_sum_erase Finset.univ (fun j => M i j) (Finset.mem_univ i)
    have eN : N i i + ∑ j ∈ Finset.univ.erase i, N i j = ∑ j, N i j :=
      Finset.add_sum_erase Finset.univ (fun j => N i j) (Finset.mem_univ i)
    have es : ∑ j ∈ Finset.univ.erase i, M i j = ∑ j ∈ Finset.univ.erase i, N i j :=
      Finset.sum_congr rfl fun j hj => off i j (Finset.ne_of_mem_erase hj).symm
    linarith [rM i, rN i]
  · exact off i j hij

/-- The response of a star read at its ends: spokes `g` to one interior node, the interior eliminated. -/
noncomputable def starResponse {ι : Type*} [DecidableEq ι] [Fintype ι] (g : ι → ℝ) (i j : ι) : ℝ :=
  if i = j then g i - g i ^ 2 / ∑ m, g m else -(g i * g j / ∑ m, g m)

/-- **Three ports read a star's spoke.** The interior it cannot touch is read from the boundary's own response. -/
theorem star_spoke_from_three_ports {ι : Type*} [DecidableEq ι] [Fintype ι] (g : ι → ℝ) {i j k : ι} (hij : i ≠ j)
    (hik : i ≠ k) (hjk : j ≠ k) (hj : g j ≠ 0) (hk : g k ≠ 0) (hS : ∑ m, g m ≠ 0) :
    starResponse g i i - starResponse g i j * starResponse g i k / starResponse g j k = g i := by
  unfold starResponse
  rw [if_pos rfl, if_neg hij, if_neg hik, if_neg hjk]
  field_simp
  ring

/-- **Two ports read one number.** Two spokes in series of conductances `(1, 1)` and `(3/4, 3/2)` answer every probe alike. -/
theorem two_ports_one_number : (1 : ℝ) * 1 / (1 + 1) = (3 / 4) * (3 / 2) / (3 / 4 + 3 / 2) := by
  norm_num

/-- **A follower stands off the beat.** A receiver that corrects its phase by `α` of its error and keeps its own period `p` settles
at an error of the detuning over its gain. -/
theorem follower_standing_error (e α P p : ℝ) (hα : α ≠ 0) (h : e = (1 - α) * e + (P - p)) : e = (P - p) / α := by
  field_simp
  linarith

/-- **A carried period reads no news of a steady beat.** A receiver that also moves its period by `β` of its error settles only at no
error, holding the beat's own period. -/
theorem carried_period_no_error (e α β P p : ℝ) (hβ : β ≠ 0) (h : e = (1 - α) * e + (P - p)) (hp : p = p + β * e) :
    e = 0 ∧ p = P := by
  have he : e = 0 := by
    have hz : β * e = 0 := by linarith
    rcases mul_eq_zero.mp hz with h0 | h0
    · exact absurd h0 hβ
    · exact h0
  refine ⟨he, ?_⟩
  rw [he] at h
  linarith

/-- **A mode that settles without turning** has a friction at least its discriminant's bound: a real rate `s` of
`χ s² + η s + J λ = 0` needs `4 χ J λ ≤ η²`. -/
theorem settled_mode_discriminant (χ η J lam s : ℝ) (h : χ * s ^ 2 + η * s + J * lam = 0) : 4 * χ * J * lam ≤ η ^ 2 := by
  have key : η ^ 2 - 4 * χ * J * lam = (2 * χ * s + η) ^ 2 := by linear_combination (-4 * χ) * h
  linarith [sq_nonneg (2 * χ * s + η)]

/-- **A handed turn travels where each member carries it.** With inertia `χ`, friction `η` and contact stiffness `J`, a mode of the
contacts' eigenvalue `λ` with `η² < 4 χ J λ` has no real rate: it turns as it fades. -/
theorem handed_turn_travels (χ η J lam : ℝ) (h : η ^ 2 < 4 * χ * J * lam) : ¬ ∃ s : ℝ, χ * s ^ 2 + η * s + J * lam = 0 := by
  rintro ⟨s, hs⟩
  exact absurd (settled_mode_discriminant χ η J lam s hs) (not_le.mpr h)

/-- **Two trains that cross answer at their sum and their difference.** The product of two real oscillations, the real parts of
`z` and `w`, is half the real part of `z w`, which turns at the sum of their rates, and half that of `z w̄`, which turns at the
difference. -/
theorem crossing_sum_and_difference (z w : ℂ) :
    z.re * w.re = (1 / 2) * (z * w).re + (1 / 2) * (z * (starRingEnd ℂ) w).re := by
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

end Holonics.HNN.AnsweredAct
