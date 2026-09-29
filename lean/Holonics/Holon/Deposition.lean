import Holonics.Holon.Element
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Holon.Deposition: deposition work, passivity under learning, and the passive projection

[definition] The deposition facet `Θ̇` of the Holon. A port Holon whose storage `Q` and a learned
active relation `L` (entering the flow as `(J − R + L) Q x`) change between commits. The word
may be passive at fixed material and still diverge under learning: the balance carries two terms
that fixed-material passivity does not see — the learned power `⟨e, L e⟩` and the deposition work
`½⟨x, ΔQ x⟩`.

[proved-derived; formal-checked]

1. **Continuous balance** over `ℝ`: along `ẋ = (J − R + L) Q(τ) x + B u`,
   `dE/dτ = −⟨e, R e⟩ + ⟨e, L e⟩ + ⟨e, B u⟩ + ½⟨x, Q̇ x⟩`, `e = Q x` (`learned_energy_balance`).
   **Commit balance** over a field: one implicit-midpoint word at `Θ_k` then a deposit
   `Q_k → Q_(k+1)` gives exactly
   `E(x⁺; Q⁺) − E(x; Q) = −h⟨ē,Rē⟩ + h⟨ē,Lē⟩ + h⟨ē,Bu⟩ + ½⟨x⁺, (Q⁺ − Q) x⁺⟩`
   (`commit_balance`): the word balance at `Θ_k` plus the deposition work.
2. **Passivity-preserving deposition.** If every word is passive (`R ⪰ 0`, `⟨e, L e⟩ ≤ 0` — the
   effort form of `AᵀQ + QA ⪯ 0` for `A = L Q`, `learned_rate_form`), inputs are off, `h ≥ 0`, and
   each deposit satisfies `Q_(k+1) ⪯ (1 + ε_k) Q_k` with `1 + ε_k ≥ 0`, then the committed energy obeys
   `E_n ≤ ∏_(k<n) (1 + ε_k) · E_0` (`committed_energy_bound`, from the abstract recurrence
   `energy_product_bound`), and over `ℝ` `∏(1 + ε_k) ≤ exp(Σ ε_k)` (`product_le_exp_sum`): bounded
   when `Σ ε_k < ∞`, non-increasing when every `ε_k ≤ 0`.
3. **Divergence witness.** The normal law `W H = B` with orthonormal features (`H = 1`) and the
   indefinite bilinear block `B = diag(1, −1)` learns `L = W` whose rate form `WᵀQ + QW = 2W` is
   indefinite; with `h = 1` the committed state `(3ⁿ, 0)` is a midpoint trajectory and its energy
   grows by the factor `9` per commit (`normal_law_divergence_witness`).
4. **The passive projection.** Clipping the positive eigenvalues of the symmetric part
   (`clipNeg`, spectral theorem over `ℝ`) gives `projectPassive L` with `⟨e, L' e⟩ ≤ 0` for every
   `e` (`projectPassive_passive`), fixing every already-passive `L` (`projectPassive_of_passive`);
   hence projecting each update restores the bound of item 2 (`projected_committed_energy_bound`).
5. **The certified projection (exact over `ℚ`).** For a certified congruence `Pᵀ (sym L) P = diag d`
   with `P P⁻¹ = 1`, removing `P⁻ᵀ diag(d₊) P⁻¹` gives `S' = P⁻ᵀ diag(min(d,0)) P⁻¹ ⪯ 0`
   (`congruenceClip_eq`, `congruenceClip_nonpos`), equal to `S` when `S ⪯ 0` (`d_i = ⟨Pδ_i, S Pδ_i⟩`,
   `congruence_diag`, `congruenceClip_of_nonpos`); the projected relation is passive, fixes passive
   relations, and restores the committed-energy bound (`projectPassiveCongruence_passive`,
   `projectPassiveCongruence_of_passive`, `certified_committed_energy_bound`). It is not the
   eigen-clip: for `S = [[1,1],[1,0]]` with `P = [[1,−1],[0,1]]` the certified clip is `diag(0,−1)`,
   whose removed part does not commute with `S`, while the eigen-clip does (`clipNeg_commute`,
   `congruence_vs_eigen_witness`).
6. **The certified step** (September 29). Along a ray `t ↦ Θ + tΔ` whose score has slope `−a` at
   `0` and curvature at most `C` on `[0, η]`, `φ(η) ≤ φ(0) − η a + ½ η² C`
   (`quadratic_upper_model`). Loci `ℓ ∈ B` stepping together with steps `η_ℓ ≥ 0` under the joint
   model `φ ≤ φ₀ − Σ η_ℓ a_ℓ + ½ Σ η_ℓ² C_ℓ` and `η_ℓ C_ℓ ≤ a_ℓ` descend by at least half their
   first-order decrease, `φ ≤ φ₀ − ½ Σ η_ℓ a_ℓ` (`certified_step_descends`). The joint model's
   curvature splits per locus: `‖Σ_(ℓ∈B) u_ℓ‖² ≤ |B| Σ ‖u_ℓ‖²` (`joint_cauchy_schwarz`), so a score
   of curvature `s` in its logits, reached through gains `‖A_ℓ v‖ ≤ κ‖v‖`, has
   `s‖Σ A_ℓ u_ℓ‖² ≤ |B| s κ² Σ ‖u_ℓ‖²` (`gauss_newton_curvature`).
7. **An active element's growth.** An element with `½‖s′‖² − ½‖b‖² ≤ ⟨½(b + s′), w⟩` (the reaction
   stage balance with its passive part dropped) and `‖w‖ ≤ ωc` has `‖s′‖ ≤ ‖b‖ + ωc`
   (`active_element_growth`); with `‖b‖, c ≤ r` and `ω ≥ 0`, `‖s′‖² ≤ (1 + ω)² r²` and
   `‖s′‖² − ‖b‖² ≤ (2ω + ω²) r²` (`active_energy_growth`).
8. **The factor families' certified step.** A factor family steps along its unit step `D = G/h'`,
   its descent covector read through its scalar metric `h' > 0`, with first-order decrease
   `a = ⟨G, D⟩ = |G|²/h' ≥ 0` (`factor_unit_step_alignment`). A square factor's output
   `B(x, x)` moves along its ray by `(t − s)(B(D, x) + B(x, D)) + (t² − s²) B(D, D)`
   (`square_ray_identity`, `square_ray_move`), with Jacobian `B(D, x + tD) + B(x + tD, D)`
   bounded at the ray's end, `2‖B‖ ‖D‖ (‖x‖ + η‖D‖)` on `[0, η]` (`square_ray_deriv`,
   `square_ray_deriv_bound`): the move `gauss_newton_curvature` reads. The transit's solve is a
   contraction at `m ⪰ 1` (`contracting_resolvent`), and its difference power is at most
   `(G/2h + ½(G/h)² c + ⅛ G² k) |δζ|²` (`transit_difference_power`); the loaded resonator is the
   case `G = 2Y`.
9. **The tightened certificate** (September 29). Families stepping together by `η_ℓ ≥ 0` with
   logit moves per unit step at most `m_ℓ` move the logits by at most `Σ η_ℓ m_ℓ`, so the joint
   curvature term is at most `s (Σ η_ℓ m_ℓ)²` (`joint_move_triangle`: the cross terms by
   Cauchy–Schwarz on the joint ray, in place of the count `|B|`); when it is at most
   `Σ η_ℓ a_ℓ` the score falls by at least `½ Σ η_ℓ a_ℓ` (`joint_step_descends`, through
   `certified_step_descends` with the joint curvature apportioned by decrease). A certified
   `μ I − Tᵀ T ⪰ 0` bounds `‖T x‖² ≤ μ ‖x‖²` (`gram_certificate_bound`), the smaller side's Gram
   suffices (`adjoint_gram_certificate_bound`), and a face whose entries are within `ε` moves a
   vector by at most `m n ε²` times its squared length (`entrywise_error_bound`): the readout's
   spectral bound that replaces its Schur test.
10. **The pumped medium's reach in the gain** (September 29). A difference carried over a span by a
   map of energy gain `a` (a pumped ring's reach, `HNN/Floquet.floquet_span_reach`) and a map of
   energy gain `b` (the medium's passive and contrast ticks) moves by at most `b a`
   (`span_transport_compose`). Moves `δ_τ` reaching the stations through span maps of energy gains
   `G_(jτ)` move the stacked logits by `Σ_j ‖Σ_τ Φ_(jτ) δ_τ‖² ≤ (Σ_j Σ_τ G_(jτ)) Σ_τ ‖δ_τ‖²`
   (`station_tick_gain`, Cauchy–Schwarz over the ticks): the gain `κ²` is the sum of the span
   gains. One injection re-entering at several ticks reaches a station with amplitudes that add,
   so `‖Σ_n Φ_n v‖² ≤ F (Σ_n a_n)² ‖v‖²` when each span's factor is at most `F`
   (`entry_span_gain`). A difference carried by several pumped rings within `s` ticks moves by at
   most `∏_r max_(s′ ≤ s) R_r(s′)` (`pumped_span_factor`, through `runningMax`, `le_runningMax`),
   which does not fall with `s` (`runningMax_mono`): the factor `F(s)` the machine reads.

[open] Owed in #62 ("The certified deposition step"): the model's own second-order terms when the
logits are not linear in the step (the bilinear coupling of a receiving map with a source port, a
contrast port acting on its own downstream contrast); the factor families' second-order terms along
their rays (the square's own `2B(D, D)` paired with the station covector, the element's resolvent
`(I − ½K)⁻¹` and the transit's `m⁻¹` differentiated twice, the ticks' products); the per-tick growth
of a word's executed ticks (the medium's `(1 + ω)²` a tick, the span gains that §10 composes into
`κ²` over the stations and re-entries, `station_tick_gain`, `entry_span_gain`); the Schur test `‖W‖₂² ≤ ‖W‖₁‖W‖_∞` and its composition into the per-family
moves (the readout reads the Gram certificate of §9 instead, whose inertia decision is the exact
congruence of `ratio::linear::inertia`); the station score's curvature bound `s = ½`; the
standing's fold: the lobe law and the lock's exact comparison are proved in `HNN/Normal` §6
(`lobe_of_step_bound`, `lobe_ray_keeps_class`, `lobe_move_is_null`, `lobe_deposit_descends`,
`lock_face_decides`, `lock_flip_descends`, `founding_off_node`), and what stays owed is the
carried lattice's reading of the lobe (the machine reads the carried successor exactly; the
statement that the carry's rounding keeps a halved ray in its lobe is not written) and the lock's
code enclosure as the realized score's (`ExactInterval` code lengths read as the Lean real
score); a declared boost's growth bound (its signed stiffness stores indefinite energy, so no gain is
certified through it; a step through it is refused); and ("The certified step reads the Floquet
reach", September 29) the pumped ring's loop within a span: §10 composes the ring's undriven reach
with the medium's ticks as a factorization of the span's transport, and the driven ring's
supply-rate certificate `E_G(x′) ≤ σ²E_G(x) + supply(e, s′)` that would discharge that
factorization through the field's return into the ring is owed, with the reach along a ring's own
gain ray (a tube of monodromies) and a modulated pump's passage-dependent schedule.
-/

noncomputable section

namespace Holonics.HolonCore

open Matrix

/-! ## 1. The commit balance -/

section Commit

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜] {σ μ : Type*} [Fintype σ] [Fintype μ]

/-- [proved-derived; formal-checked] The deposition work of a storage change at fixed state. -/
theorem deposition_work (Q Q' : Matrix σ σ 𝕜) (x : σ → 𝕜) :
    storageEnergy Q' x - storageEnergy Q x = (1 / 2) * (x ⬝ᵥ ((Q' - Q) *ᵥ x)) := by
  simp only [storageEnergy, sub_mulVec, dotProduct_sub]; ring

/-- [proved-derived; formal-checked] **The commit balance.** An implicit-midpoint word of
`q̇ = (J − R + L) Q q + B u` at the material `Q`, followed by the deposit `Q → Q'`:
`E(x⁺; Q') − E(x; Q) = −h⟨ē,Rē⟩ + h⟨ē,Lē⟩ + h⟨ē,Bu⟩ + ½⟨x⁺, (Q' − Q) x⁺⟩` with
`ē = Q (x + x⁺)/2`. -/
theorem commit_balance {Q J R L : Matrix σ σ 𝕜} (hQ : Qᵀ = Q) (hJ : Jᵀ = -J) (Q' : Matrix σ σ 𝕜)
    (B : Matrix σ μ 𝕜) (h : 𝕜) (x x' : σ → 𝕜) (u : μ → 𝕜)
    (hstep : x' - x = h • ((J - R + L) *ᵥ (Q *ᵥ ((1 / 2 : 𝕜) • (x + x'))) + B *ᵥ u)) :
    storageEnergy Q' x' - storageEnergy Q x =
      -(h * ((Q *ᵥ ((1 / 2 : 𝕜) • (x + x'))) ⬝ᵥ (R *ᵥ (Q *ᵥ ((1 / 2 : 𝕜) • (x + x')))))) +
        h * ((Q *ᵥ ((1 / 2 : 𝕜) • (x + x'))) ⬝ᵥ (L *ᵥ (Q *ᵥ ((1 / 2 : 𝕜) • (x + x'))))) +
        h * ((Q *ᵥ ((1 / 2 : 𝕜) • (x + x'))) ⬝ᵥ (B *ᵥ u)) +
        (1 / 2) * (x' ⬝ᵥ ((Q' - Q) *ᵥ x')) := by
  have hstep' : x' - x = h • ((J - (R - L)) *ᵥ (Q *ᵥ ((1 / 2 : 𝕜) • (x + x'))) + B *ᵥ u) := by
    rw [hstep]; congr 2; abel_nf
  have hw := midpoint_balance hQ hJ B h x x' u hstep'
  have hd := deposition_work Q Q' x'
  rw [show storageEnergy Q' x' - storageEnergy Q x =
      (storageEnergy Q' x' - storageEnergy Q x') + (storageEnergy Q x' - storageEnergy Q x) by ring,
    hd, hw]
  simp only [sub_mulVec, dotProduct_sub]
  ring

omit [CharZero 𝕜] in
/-- [proved-derived; formal-checked] The effort form of the learned rate: for `A = L Q` with `Q`
symmetric, `⟨x, (AᵀQ + QA) x⟩ = 2⟨Qx, L Qx⟩`. -/
theorem learned_rate_form {Q L : Matrix σ σ 𝕜} (hQ : Qᵀ = Q) (x : σ → 𝕜) :
    x ⬝ᵥ (((L * Q)ᵀ * Q + Q * (L * Q)) *ᵥ x) = 2 * ((Q *ᵥ x) ⬝ᵥ (L *ᵥ (Q *ᵥ x))) := by
  rw [add_mulVec, dotProduct_add, Matrix.transpose_mul, hQ]
  simp only [← mulVec_mulVec]
  rw [symm_dot hQ x, symm_dot hQ x, dotProduct_comm (Lᵀ *ᵥ _), transpose_dot,
    dotProduct_comm (L *ᵥ _)]
  ring

end Commit

/-! ### The continuous balance under learning -/

/-- [proved-derived; formal-checked] **The balance under learning and deposition.** Along
`ẋ = (J − R + L) Q(τ) x + B u` with `J` skew and `Q(τ)` symmetric,
`dE/dτ = −⟨e, R e⟩ + ⟨e, L e⟩ + ⟨e, B u⟩ + ½⟨x, Q̇ x⟩`, `e = Q(τ) x`.

This is the dynamical owner of the moving-metric energy law, in the Holon's quadratic port chart
and under exactly these hypotheses (differentiable `x`, `Q`; symmetric `Q`; skew `J`); it assigns
no energy to a statistical receiver. Its algebraic form, for any rate `A` and symmetric metric `G`
with rate `Ġ` and forcing `f`, is `Geometry/Motion.energy_rate_moving_metric` (read as turn and
boost by `energy_rate_moving_metric_boost`: the turn `JQ` does no work, the dissipation `−RQ` and
the learned relation's self-adjoint part boost). Its constant-metric readings are
`Foundation/CausalChord.rateForm_congruence` and `Transport/HolonicInteraction.port_storage_rate`. -/
theorem learned_energy_balance {σ μ : Type*} [Fintype σ] [Fintype μ] {J R L : Matrix σ σ ℝ}
    (hJ : Jᵀ = -J) (B : Matrix σ μ ℝ) (u : μ → ℝ) {x : ℝ → σ → ℝ} {Q : ℝ → Matrix σ σ ℝ}
    {Qd : Matrix σ σ ℝ} {t : ℝ}
    (hx : ∀ i, HasDerivAt (fun s => x s i)
      (((J - R + L) *ᵥ (Q t *ᵥ x t) + B *ᵥ u) i) t)
    (hQ : ∀ i j, HasDerivAt (fun s => Q s i j) (Qd i j) t) (hsymm : (Q t)ᵀ = Q t) :
    HasDerivAt (fun s => storageEnergy (Q s) (x s))
      (-((Q t *ᵥ x t) ⬝ᵥ (R *ᵥ (Q t *ᵥ x t))) + (Q t *ᵥ x t) ⬝ᵥ (L *ᵥ (Q t *ᵥ x t)) +
        (Q t *ᵥ x t) ⬝ᵥ (B *ᵥ u) + (1 / 2) * (x t ⬝ᵥ (Qd *ᵥ x t))) t := by
  refine (hasDerivAt_storageEnergy hx hQ hsymm).congr_deriv ?_
  set e := Q t *ᵥ x t
  have hskew : e ⬝ᵥ (J *ᵥ e) = 0 := by
    have := skew_dot hJ e e
    linarith
  rw [add_mulVec, sub_mulVec, dotProduct_add, dotProduct_add, dotProduct_sub, hskew]
  ring

/-! ## 2. Passivity-preserving deposition -/

section Bound

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- [proved-derived; formal-checked] **The abstract commit recurrence.** A passive word
(`W_k ≤ E_k`) followed by a deposit that scales storage by at most `1 + ε_k ≥ 0`
(`E_(k+1) ≤ (1 + ε_k) W_k`) gives `E_n ≤ ∏_(k<n) (1 + ε_k) · E_0`. -/
theorem energy_product_bound (E W ε : ℕ → 𝕜) (hW : ∀ k, W k ≤ E k)
    (hE : ∀ k, E (k + 1) ≤ (1 + ε k) * W k) (hε : ∀ k, 0 ≤ 1 + ε k) :
    ∀ n, E n ≤ (∏ k ∈ Finset.range n, (1 + ε k)) * E 0 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.prod_range_succ]
      calc E (n + 1) ≤ (1 + ε n) * W n := hE n
        _ ≤ (1 + ε n) * E n := mul_le_mul_of_nonneg_left (hW n) (hε n)
        _ ≤ (1 + ε n) * ((∏ k ∈ Finset.range n, (1 + ε k)) * E 0) :=
            mul_le_mul_of_nonneg_left ih (hε n)
        _ = _ := by ring

variable {σ : Type*} [Fintype σ]

/-- [proved-derived; formal-checked] **Passivity-preserving deposition.** Committed midpoint words
of `q̇ = (J_k − R_k + L_k) Q_k q` with `R_k ⪰ 0`, `⟨e, L_k e⟩ ≤ 0`, `h ≥ 0`, and deposits
`Q_(k+1) ⪯ (1 + ε_k) Q_k`, `1 + ε_k ≥ 0`: the committed energy obeys
`E(x_n; Q_n) ≤ ∏_(k<n) (1 + ε_k) E(x_0; Q_0)`. -/
theorem committed_energy_bound (x : ℕ → σ → 𝕜) (Q J R L : ℕ → Matrix σ σ 𝕜) (ε : ℕ → 𝕜)
    (h : 𝕜) (hh : 0 ≤ h) (hQ : ∀ k, (Q k)ᵀ = Q k) (hJ : ∀ k, (J k)ᵀ = -J k)
    (hR : ∀ k e, 0 ≤ e ⬝ᵥ (R k *ᵥ e)) (hL : ∀ k e, e ⬝ᵥ (L k *ᵥ e) ≤ 0)
    (hstep : ∀ k, x (k + 1) - x k =
      h • ((J k - R k + L k) *ᵥ (Q k *ᵥ ((1 / 2 : 𝕜) • (x k + x (k + 1))))))
    (hdep : ∀ k y, storageEnergy (Q (k + 1)) y ≤ (1 + ε k) * storageEnergy (Q k) y)
    (hε : ∀ k, 0 ≤ 1 + ε k) (n : ℕ) :
    storageEnergy (Q n) (x n) ≤
      (∏ k ∈ Finset.range n, (1 + ε k)) * storageEnergy (Q 0) (x 0) := by
  refine energy_product_bound (fun k => storageEnergy (Q k) (x k))
    (fun k => storageEnergy (Q k) (x (k + 1))) ε (fun k => ?_) (fun k => hdep k _) hε n
  have hstep' : x (k + 1) - x k =
      h • ((J k - (R k - L k)) *ᵥ (Q k *ᵥ ((1 / 2 : 𝕜) • (x k + x (k + 1)))) +
        (0 : Matrix σ (Fin 0) 𝕜) *ᵥ 0) := by
    rw [hstep k]; congr 1; simp only [zero_mulVec, add_zero]; congr 1; abel
  have hw := midpoint_balance (hQ k) (hJ k) 0 h (x k) (x (k + 1)) 0 hstep'
  set e := Q k *ᵥ ((1 / 2 : 𝕜) • (x k + x (k + 1)))
  have hRL : 0 ≤ e ⬝ᵥ ((R k - L k) *ᵥ e) := by
    rw [sub_mulVec, dotProduct_sub]; linarith [hR k e, hL k e]
  simp only [zero_mulVec, dotProduct_zero, mul_zero, add_zero] at hw
  have : 0 ≤ h * (e ⬝ᵥ ((R k - L k) *ᵥ e)) := mul_nonneg hh hRL
  show storageEnergy (Q k) (x (k + 1)) ≤ storageEnergy (Q k) (x k)
  linarith

end Bound

/-- [proved-derived; formal-checked] Over `ℝ`, `∏ (1 + ε_k) ≤ exp (Σ ε_k)` when every `1 + ε_k ≥ 0`:
the committed energy is bounded whenever `Σ ε_k` is. -/
theorem product_le_exp_sum (ε : ℕ → ℝ) (hε : ∀ k, 0 ≤ 1 + ε k) (n : ℕ) :
    ∏ k ∈ Finset.range n, (1 + ε k) ≤ Real.exp (∑ k ∈ Finset.range n, ε k) := by
  rw [Real.exp_sum]
  apply Finset.prod_le_prod (fun k _ => hε k)
  intro k _
  linarith [Real.add_one_le_exp (ε k)]

/-! ## 3. The divergence witness -/

/-- [definition] The indefinite bilinear block `diag(1, −1)`. -/
def indefiniteBlock : Matrix (Fin 2) (Fin 2) ℚ := !![1, 0; 0, -1]

/-- [definition] The divergent committed state `(3ⁿ, 0)`. -/
def divergentState (n : ℕ) : Fin 2 → ℚ := ![3 ^ n, 0]

/-- [counterexample; formal-checked] **Learning diverges through an indefinite normal-law block.**
With orthonormal features (`H = 1`), the normal law `W H = B` returns `W = B = diag(1, −1)`; the
learned rate form `WᵀQ + QW = 2W` (at `Q = 1`) is indefinite; with `J = R = 0`, `h = 1`, the state
`(3ⁿ, 0)` is a midpoint trajectory of `q̇ = W q`, and its energy is `9ⁿ/2`: it grows by `9` per
commit although the material `Q` never changes. -/
theorem normal_law_divergence_witness :
    indefiniteBlock * 1 = indefiniteBlock ∧
    (0 < (![1, 0] : Fin 2 → ℚ) ⬝ᵥ ((indefiniteBlockᵀ * 1 + 1 * indefiniteBlock) *ᵥ ![1, 0]) ∧
      (![0, 1] : Fin 2 → ℚ) ⬝ᵥ ((indefiniteBlockᵀ * 1 + 1 * indefiniteBlock) *ᵥ ![0, 1]) < 0) ∧
    (∀ n, divergentState (n + 1) - divergentState n =
      (1 : ℚ) • ((0 - 0 + indefiniteBlock) *ᵥ ((1 : Matrix (Fin 2) (Fin 2) ℚ) *ᵥ
        ((1 / 2 : ℚ) • (divergentState n + divergentState (n + 1)))))) ∧
    ∀ n, storageEnergy 1 (divergentState n) = 9 ^ n / 2 := by
  refine ⟨by simp, ⟨?_, ?_⟩, fun n => ?_, fun n => ?_⟩
  · simp [indefiniteBlock, mulVec, dotProduct, Fin.sum_univ_two]
  · simp [indefiniteBlock, mulVec, dotProduct, Fin.sum_univ_two]
  · ext i; fin_cases i
    · simp [divergentState, indefiniteBlock, pow_succ]
      ring
    · simp [divergentState, indefiniteBlock]
  · simp [storageEnergy, divergentState, dotProduct, Fin.sum_univ_two]
    rw [← mul_pow]; norm_num; ring

/-! ## 4. The passive projection -/

section Projection

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- [definition] Clip the positive eigenvalues of a symmetric matrix: `U diag(min(λ, 0)) Uᵀ`. -/
def clipNeg {S : Matrix n n ℝ} (hS : S.IsHermitian) : Matrix n n ℝ :=
  (hS.eigenvectorUnitary : Matrix n n ℝ) * diagonal (fun i => min (hS.eigenvalues i) 0) *
    (hS.eigenvectorUnitary : Matrix n n ℝ)ᵀ

omit [DecidableEq n] in
theorem quad_conj (U D : Matrix n n ℝ) (e : n → ℝ) :
    e ⬝ᵥ ((U * D * Uᵀ) *ᵥ e) = (Uᵀ *ᵥ e) ⬝ᵥ (D *ᵥ (Uᵀ *ᵥ e)) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose]

/-- [proved-derived; formal-checked] The clipped matrix is negative semidefinite. -/
theorem clipNeg_nonpos {S : Matrix n n ℝ} (hS : S.IsHermitian) (e : n → ℝ) :
    e ⬝ᵥ (clipNeg hS *ᵥ e) ≤ 0 := by
  rw [clipNeg, quad_conj]
  set y := (hS.eigenvectorUnitary : Matrix n n ℝ)ᵀ *ᵥ e
  simp only [dotProduct, mulVec_diagonal]
  apply Finset.sum_nonpos
  intro i _
  have := min_le_right (hS.eigenvalues i) 0
  nlinarith [sq_nonneg (y i)]

theorem spectral_real {S : Matrix n n ℝ} (hS : S.IsHermitian) :
    S = (hS.eigenvectorUnitary : Matrix n n ℝ) * diagonal hS.eigenvalues *
      (hS.eigenvectorUnitary : Matrix n n ℝ)ᵀ := by
  conv_lhs => rw [hS.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply]
  simp [Matrix.star_eq_conjTranspose]

/-- [proved-derived; formal-checked] Clipping fixes a negative semidefinite matrix. -/
theorem clipNeg_of_nonpos {S : Matrix n n ℝ} (hS : S.IsHermitian)
    (hneg : ∀ e, e ⬝ᵥ (S *ᵥ e) ≤ 0) : clipNeg hS = S := by
  have hlam : ∀ i, hS.eigenvalues i ≤ 0 := by
    intro i
    rw [hS.eigenvalues_eq]
    simpa using hneg _
  conv_rhs => rw [spectral_real hS]
  rw [clipNeg]
  congr 3
  funext i
  exact min_eq_left (hlam i)

/-- [definition] The symmetric part `(L + Lᵀ)/2`. -/
def symPart (L : Matrix n n ℝ) : Matrix n n ℝ := (1 / 2 : ℝ) • (L + Lᵀ)

omit [Fintype n] [DecidableEq n] in
theorem symPart_isHermitian (L : Matrix n n ℝ) : (symPart L).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, symPart,
    Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_transpose, add_comm]

omit [DecidableEq n] in
theorem quad_symPart (L : Matrix n n ℝ) (e : n → ℝ) :
    e ⬝ᵥ (symPart L *ᵥ e) = e ⬝ᵥ (L *ᵥ e) := by
  rw [symPart, smul_mulVec, add_mulVec, dotProduct_smul, dotProduct_add, dotProduct_mulVec e Lᵀ,
    ← mulVec_transpose, Matrix.transpose_transpose, dotProduct_comm (L *ᵥ e), smul_eq_mul]
  ring

/-- [definition] **The passive projection**: remove the positive part of the symmetric part,
keep the skew part. -/
def projectPassive (L : Matrix n n ℝ) : Matrix n n ℝ :=
  L - (symPart L - clipNeg (symPart_isHermitian L))

/-- [proved-derived; formal-checked] **The projected relation is passive**: `⟨e, L' e⟩ ≤ 0`. -/
theorem projectPassive_passive (L : Matrix n n ℝ) (e : n → ℝ) :
    e ⬝ᵥ (projectPassive L *ᵥ e) ≤ 0 := by
  rw [projectPassive, sub_mulVec, sub_mulVec, dotProduct_sub, dotProduct_sub, quad_symPart]
  linarith [clipNeg_nonpos (symPart_isHermitian L) e]

/-- [proved-derived; formal-checked] **The projection fixes passive relations.** -/
theorem projectPassive_of_passive (L : Matrix n n ℝ) (hL : ∀ e, e ⬝ᵥ (L *ᵥ e) ≤ 0) :
    projectPassive L = L := by
  have : clipNeg (symPart_isHermitian L) = symPart L :=
    clipNeg_of_nonpos _ fun e => by rw [quad_symPart]; exact hL e
  rw [projectPassive, this, sub_self, sub_zero]

/-- [proved-derived; formal-checked] **Projecting each update restores the bound.** Whatever the
learned updates `L_k`, the committed trajectory run with `projectPassive L_k` obeys
`E_n ≤ ∏ (1 + ε_k) E_0`. -/
theorem projected_committed_energy_bound (x : ℕ → n → ℝ) (Q J R L : ℕ → Matrix n n ℝ)
    (ε : ℕ → ℝ) (h : ℝ) (hh : 0 ≤ h) (hQ : ∀ k, (Q k)ᵀ = Q k) (hJ : ∀ k, (J k)ᵀ = -J k)
    (hR : ∀ k e, 0 ≤ e ⬝ᵥ (R k *ᵥ e))
    (hstep : ∀ k, x (k + 1) - x k =
      h • ((J k - R k + projectPassive (L k)) *ᵥ (Q k *ᵥ ((1 / 2 : ℝ) • (x k + x (k + 1))))))
    (hdep : ∀ k y, storageEnergy (Q (k + 1)) y ≤ (1 + ε k) * storageEnergy (Q k) y)
    (hε : ∀ k, 0 ≤ 1 + ε k) (m : ℕ) :
    storageEnergy (Q m) (x m) ≤
      (∏ k ∈ Finset.range m, (1 + ε k)) * storageEnergy (Q 0) (x 0) :=
  committed_energy_bound x Q J R (fun k => projectPassive (L k)) ε h hh hQ hJ hR
    (fun k e => projectPassive_passive (L k) e) hstep hdep hε m

/-- [proved-derived; formal-checked] The eigen-clip commutes with the matrix it clips (both are
diagonal in the same orthonormal eigenbasis). -/
theorem clipNeg_commute {S : Matrix n n ℝ} (hS : S.IsHermitian) : S * clipNeg hS = clipNeg hS * S := by
  have hU : ((hS.eigenvectorUnitary : Matrix n n ℝ))ᵀ * (hS.eigenvectorUnitary : Matrix n n ℝ) = 1 := by
    have := Unitary.coe_star_mul_self hS.eigenvectorUnitary
    rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hSU := spectral_real hS
  unfold clipNeg
  generalize (hS.eigenvectorUnitary : Matrix n n ℝ) = U at hU hSU ⊢
  generalize hS.eigenvalues = lam at hSU ⊢
  subst hSU
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc Uᵀ U, hU, Matrix.one_mul, ← Matrix.mul_assoc Uᵀ U, hU, Matrix.one_mul,
    ← Matrix.mul_assoc (diagonal lam), ← Matrix.mul_assoc (diagonal _),
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 3
  funext i; ring

end Projection

/-! ## 5. The certified-congruence projection (exact over `ℚ`) -/

section Congruence

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {n : Type*} [Fintype n] [DecidableEq n]

/-- [definition] **The congruence clip.** With a certified congruence `Pᵀ S P = diag d` and
`P⁻¹ = Pinv`, remove `P⁻ᵀ diag(d₊) P⁻¹`. -/
def congruenceClip (S Pinv : Matrix n n 𝕜) (d : n → 𝕜) : Matrix n n 𝕜 :=
  S - Pinvᵀ * diagonal (fun i => max (d i) 0) * Pinv

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [DecidableEq n] in
theorem quad_congr (A D : Matrix n n 𝕜) (e : n → 𝕜) :
    e ⬝ᵥ ((Aᵀ * D * A) *ᵥ e) = (A *ᵥ e) ⬝ᵥ (D *ᵥ (A *ᵥ e)) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]

omit [IsStrictOrderedRing 𝕜] in
/-- [proved-derived; formal-checked] Under the congruence, `S = P⁻ᵀ diag(d) P⁻¹` and the clip is
`P⁻ᵀ diag(min(d, 0)) P⁻¹`. -/
theorem congruenceClip_eq {S P Pinv : Matrix n n 𝕜} {d : n → 𝕜} (hP : P * Pinv = 1)
    (hD : Pᵀ * S * P = diagonal d) :
    congruenceClip S Pinv d = Pinvᵀ * diagonal (fun i => min (d i) 0) * Pinv := by
  have hS : S = Pinvᵀ * diagonal d * Pinv := by
    rw [← hD]
    have hT : Pinvᵀ * Pᵀ = 1 := by rw [← Matrix.transpose_mul, hP, Matrix.transpose_one]
    simp only [Matrix.mul_assoc]
    rw [hP, Matrix.mul_one, ← Matrix.mul_assoc, hT, Matrix.one_mul]
  rw [congruenceClip]
  conv_lhs => rw [hS]
  rw [← Matrix.sub_mul, ← Matrix.mul_sub, Matrix.diagonal_sub]
  congr 3
  funext i
  rcases le_total (d i) 0 with h | h
  · rw [max_eq_right h, min_eq_left h, sub_zero]
  · rw [max_eq_left h, min_eq_right h, sub_self]

/-- [proved-derived; formal-checked] **The congruence clip is negative semidefinite.** -/
theorem congruenceClip_nonpos {S P Pinv : Matrix n n 𝕜} {d : n → 𝕜} (hP : P * Pinv = 1)
    (hD : Pᵀ * S * P = diagonal d) (e : n → 𝕜) :
    e ⬝ᵥ (congruenceClip S Pinv d *ᵥ e) ≤ 0 := by
  rw [congruenceClip_eq hP hD, quad_congr]
  set y := Pinv *ᵥ e
  simp only [dotProduct, mulVec_diagonal]
  apply Finset.sum_nonpos
  intro i _
  have := min_le_right (d i) 0
  nlinarith [mul_self_nonneg (y i)]

omit [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- [proved-derived; formal-checked] A congruence reads its diagonal: `⟨P δ_i, S P δ_i⟩ = d_i`. -/
theorem congruence_diag {S P : Matrix n n 𝕜} {d : n → 𝕜} (hD : Pᵀ * S * P = diagonal d) (i : n) :
    (P *ᵥ Pi.single i 1) ⬝ᵥ (S *ᵥ (P *ᵥ Pi.single i 1)) = d i := by
  rw [← quad_congr, hD]
  simp

omit [IsStrictOrderedRing 𝕜] in
/-- [proved-derived; formal-checked] **The congruence clip fixes a negative semidefinite `S`**:
each `d_i = ⟨P δ_i, S P δ_i⟩ ≤ 0`, so `d₊ = 0`. -/
theorem congruenceClip_of_nonpos {S P Pinv : Matrix n n 𝕜} {d : n → 𝕜}
    (hD : Pᵀ * S * P = diagonal d) (hneg : ∀ e, e ⬝ᵥ (S *ᵥ e) ≤ 0) :
    congruenceClip S Pinv d = S := by
  have hd : ∀ i, d i ≤ 0 := fun i => by
    rw [← congruence_diag hD i]; exact hneg _
  rw [congruenceClip]
  have : (fun i => max (d i) 0) = fun _ => (0 : 𝕜) := funext fun i => max_eq_right (hd i)
  rw [this, Matrix.diagonal_zero, Matrix.mul_zero, Matrix.zero_mul, sub_zero]

/-- [definition] The symmetric part over a field of characteristic zero. -/
def symPartK (L : Matrix n n 𝕜) : Matrix n n 𝕜 := (1 / 2 : 𝕜) • (L + Lᵀ)

omit [DecidableEq n] in
theorem quad_symPartK (L : Matrix n n 𝕜) (e : n → 𝕜) :
    e ⬝ᵥ (symPartK L *ᵥ e) = e ⬝ᵥ (L *ᵥ e) := by
  rw [symPartK, smul_mulVec, add_mulVec, dotProduct_smul, dotProduct_add, dotProduct_mulVec e Lᵀ,
    ← mulVec_transpose, Matrix.transpose_transpose, dotProduct_comm (L *ᵥ e), smul_eq_mul]
  ring

/-- [definition] **The certified passive projection** of a learned relation: remove
`P⁻ᵀ diag(d₊) P⁻¹` for a congruence `Pᵀ (sym L) P = diag d`; the skew part is kept. -/
def projectPassiveCongruence (L Pinv : Matrix n n 𝕜) (d : n → 𝕜) : Matrix n n 𝕜 :=
  L - Pinvᵀ * diagonal (fun i => max (d i) 0) * Pinv

/-- [proved-derived; formal-checked] **The certified projection is passive.** -/
theorem projectPassiveCongruence_passive {L P Pinv : Matrix n n 𝕜} {d : n → 𝕜}
    (hP : P * Pinv = 1) (hD : Pᵀ * symPartK L * P = diagonal d) (e : n → 𝕜) :
    e ⬝ᵥ (projectPassiveCongruence L Pinv d *ᵥ e) ≤ 0 := by
  have h := congruenceClip_nonpos hP hD e
  rw [congruenceClip, sub_mulVec, dotProduct_sub, quad_symPartK] at h
  rw [projectPassiveCongruence, sub_mulVec, dotProduct_sub]
  exact h

/-- [proved-derived; formal-checked] It fixes an already passive relation. -/
theorem projectPassiveCongruence_of_passive {L P Pinv : Matrix n n 𝕜} {d : n → 𝕜}
    (hD : Pᵀ * symPartK L * P = diagonal d) (hL : ∀ e, e ⬝ᵥ (L *ᵥ e) ≤ 0) :
    projectPassiveCongruence L Pinv d = L := by
  have hd : ∀ i, d i ≤ 0 := fun i => by
    rw [← congruence_diag hD i, quad_symPartK]; exact hL _
  rw [projectPassiveCongruence]
  have : (fun i => max (d i) 0) = fun _ => (0 : 𝕜) := funext fun i => max_eq_right (hd i)
  rw [this, Matrix.diagonal_zero, Matrix.mul_zero, Matrix.zero_mul, sub_zero]

/-- [proved-derived; formal-checked] **The committed-energy bound under the certified
projection**, composing `committed_energy_bound`: whatever the raw learned updates `L_k`, with
certified congruences `P_kᵀ (sym L_k) P_k = diag d_k`, the committed energy obeys
`E_m ≤ ∏ (1 + ε_k) E_0`. -/
theorem certified_committed_energy_bound [CharZero 𝕜] (x : ℕ → n → 𝕜)
    (Q J R L P Pinv : ℕ → Matrix n n 𝕜) (d : ℕ → n → 𝕜) (ε : ℕ → 𝕜) (h : 𝕜) (hh : 0 ≤ h)
    (hQ : ∀ k, (Q k)ᵀ = Q k) (hJ : ∀ k, (J k)ᵀ = -J k) (hR : ∀ k e, 0 ≤ e ⬝ᵥ (R k *ᵥ e))
    (hP : ∀ k, P k * Pinv k = 1) (hD : ∀ k, (P k)ᵀ * symPartK (L k) * P k = diagonal (d k))
    (hstep : ∀ k, x (k + 1) - x k = h • ((J k - R k + projectPassiveCongruence (L k) (Pinv k) (d k))
      *ᵥ (Q k *ᵥ ((1 / 2 : 𝕜) • (x k + x (k + 1))))))
    (hdep : ∀ k y, storageEnergy (Q (k + 1)) y ≤ (1 + ε k) * storageEnergy (Q k) y)
    (hε : ∀ k, 0 ≤ 1 + ε k) (m : ℕ) :
    storageEnergy (Q m) (x m) ≤
      (∏ k ∈ Finset.range m, (1 + ε k)) * storageEnergy (Q 0) (x 0) :=
  committed_energy_bound x Q J R (fun k => projectPassiveCongruence (L k) (Pinv k) (d k)) ε h hh
    hQ hJ hR (fun k e => projectPassiveCongruence_passive (hP k) (hD k) e) hstep hdep hε m

end Congruence

/-! ### Witness: the certified clip is not the eigen-clip -/

/-- [definition] `S = [[1, 1], [1, 0]]`, congruence `P = [[1, −1], [0, 1]]`, `Pᵀ S P = diag(1, −1)`. -/
def wS : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 1, 0]
def wP : Matrix (Fin 2) (Fin 2) ℝ := !![1, -1; 0, 1]
def wPinv : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 0, 1]

/-- [counterexample; formal-checked] **The certified clip differs from the eigen-clip.** With the
non-orthogonal congruence `P`, the congruence clip is `diag(0, −1)`; the removed part
`[[1,1],[1,1]]` does not commute with `S`, whereas the eigen-clip commutes with `S`
(`clipNeg_commute`), so the two clips are different negative semidefinite matrices. -/
theorem congruence_vs_eigen_witness (hS : wS.IsHermitian) :
    wP * wPinv = 1 ∧ wPᵀ * wS * wP = diagonal ![1, -1] ∧
      congruenceClip wS wPinv ![1, -1] = !![0, 0; 0, -1] ∧
      congruenceClip wS wPinv ![1, -1] ≠ clipNeg hS := by
  have h1 : wP * wPinv = 1 := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [wP, wPinv, Matrix.mul_apply, Fin.sum_univ_two]
  have h2 : wPᵀ * wS * wP = diagonal ![1, -1] := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [wP, wS, Matrix.mul_apply, Fin.sum_univ_two, diagonal]
  have h3 : congruenceClip wS wPinv ![1, -1] = !![0, 0; 0, -1] := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [congruenceClip, wS, wPinv, Matrix.mul_apply, Fin.sum_univ_two, diagonal]
  refine ⟨h1, h2, h3, fun h => ?_⟩
  have hc := clipNeg_commute hS
  rw [← h, h3] at hc
  have := congrFun (congrFun hc 0) 1
  simp [wS, Matrix.mul_apply, Fin.sum_univ_two] at this

/-! ## 6. The certified step -/

section Step

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- [proved-derived; formal-checked] **The certified step descends.** Loci `ℓ ∈ B` stepping
together along their unit steps by `η_ℓ ≥ 0`, under the joint quadratic upper model
`φ ≤ φ₀ − Σ η_ℓ a_ℓ + ½ Σ η_ℓ² C_ℓ` (`a_ℓ` the unit step's first-order decrease, `C_ℓ` its
certified curvature), with `η_ℓ C_ℓ ≤ a_ℓ`, descend by at least half their first-order decrease. -/
theorem certified_step_descends {ι : Type*} (B : Finset ι) {φ₀ φη : 𝕜} {η a C : ι → 𝕜}
    (hmodel : φη ≤ φ₀ - ∑ ℓ ∈ B, η ℓ * a ℓ + (1 / 2) * ∑ ℓ ∈ B, η ℓ ^ 2 * C ℓ)
    (hη : ∀ ℓ ∈ B, 0 ≤ η ℓ) (hstep : ∀ ℓ ∈ B, η ℓ * C ℓ ≤ a ℓ) :
    φη ≤ φ₀ - (1 / 2) * ∑ ℓ ∈ B, η ℓ * a ℓ := by
  have h : ∑ ℓ ∈ B, η ℓ ^ 2 * C ℓ ≤ ∑ ℓ ∈ B, η ℓ * a ℓ := Finset.sum_le_sum fun ℓ hℓ => by
    have := mul_le_mul_of_nonneg_left (hstep ℓ hℓ) (hη ℓ hℓ)
    nlinarith [this]
  linarith

end Step

open Set in
/-- [proved-derived; formal-checked] **The quadratic upper model along a ray.** A score with slope
`−a` at `0` and curvature at most `C` on `[0, η]` obeys `φ(η) ≤ φ(0) − η a + ½ η² C`. -/
theorem quadratic_upper_model {φ φ' φ'' : ℝ → ℝ} {a C η : ℝ} (hη : 0 ≤ η)
    (hφ : ∀ t ∈ Icc 0 η, HasDerivAt φ (φ' t) t) (hφ' : ∀ t ∈ Icc 0 η, HasDerivAt φ' (φ'' t) t)
    (h0 : φ' 0 = -a) (hC : ∀ t ∈ Icc 0 η, φ'' t ≤ C) :
    φ η ≤ φ 0 - η * a + 1 / 2 * η ^ 2 * C := by
  have hslope : ∀ t ∈ Icc 0 η, φ' t ≤ -a + t * C := by
    intro t ht
    refine image_le_of_deriv_right_le_deriv_boundary (f := φ') (f' := φ'') (a := 0) (b := η)
      (B := fun t => -a + t * C) (B' := fun _ => C) ?_ ?_ ?_ ?_ ?_ ?_ ht
    · exact fun x hx => (hφ' x hx).continuousAt.continuousWithinAt
    · exact fun x hx => (hφ' x (Ico_subset_Icc_self hx)).hasDerivWithinAt
    · simp [h0]
    · exact (continuous_const.add (continuous_id.mul continuous_const)).continuousOn
    · intro x _
      have := ((hasDerivAt_id x).mul_const C).const_add (-a)
      simpa using this.hasDerivWithinAt
    · exact fun x hx => hC x (Ico_subset_Icc_self hx)
  refine image_le_of_deriv_right_le_deriv_boundary (f := φ) (f' := φ') (a := 0) (b := η)
    (B := fun t => φ 0 - t * a + 1 / 2 * t ^ 2 * C) (B' := fun t => -a + t * C)
    ?_ ?_ ?_ ?_ ?_ ?_ ⟨hη, le_rfl⟩
  · exact fun x hx => (hφ x hx).continuousAt.continuousWithinAt
  · exact fun x hx => (hφ x (Ico_subset_Icc_self hx)).hasDerivWithinAt
  · simp
  · fun_prop
  · intro x _
    have h := (((hasDerivAt_id' x).mul_const a).const_sub (φ 0)).add
      (((hasDerivAt_pow 2 x).const_mul (1 / 2 : ℝ)).mul_const C)
    refine (h.congr_deriv ?_).hasDerivWithinAt
    rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one]
    push_cast
    ring
  · exact fun x hx => hslope x (Ico_subset_Icc_self hx)

/-- [proved-derived; formal-checked] **The joint moves' Cauchy–Schwarz**: the moves of `|B|` loci
stepping together add, `‖Σ_(ℓ∈B) u_ℓ‖² ≤ |B| Σ ‖u_ℓ‖²`. -/
theorem joint_cauchy_schwarz {E : Type*} [SeminormedAddCommGroup E] {ι : Type*} (B : Finset ι)
    (u : ι → E) : ‖∑ ℓ ∈ B, u ℓ‖ ^ 2 ≤ B.card * ∑ ℓ ∈ B, ‖u ℓ‖ ^ 2 :=
  (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2).trans sq_sum_le_card_mul_sum_sq

/-- [proved-derived; formal-checked] **The curvature a linear locus reads** (Gauss–Newton): a
score of curvature `s` in its logits, reached by the loci's moves `u_ℓ` through gains
`‖A_ℓ v‖ ≤ κ‖v‖`, has second-order term `s‖Σ A_ℓ u_ℓ‖² ≤ |B| s κ² Σ ‖u_ℓ‖²`. -/
theorem gauss_newton_curvature {E F : Type*} [SeminormedAddCommGroup E]
    [SeminormedAddCommGroup F] {ι : Type*} (B : Finset ι) {s κ : ℝ} (hs : 0 ≤ s)
    (A : ι → E → F) (hA : ∀ ℓ v, ‖A ℓ v‖ ≤ κ * ‖v‖) (u : ι → E) :
    s * ‖∑ ℓ ∈ B, A ℓ (u ℓ)‖ ^ 2 ≤ B.card * s * κ ^ 2 * ∑ ℓ ∈ B, ‖u ℓ‖ ^ 2 := by
  have h1 := joint_cauchy_schwarz B (fun ℓ => A ℓ (u ℓ))
  have h2 : ∑ ℓ ∈ B, ‖A ℓ (u ℓ)‖ ^ 2 ≤ κ ^ 2 * ∑ ℓ ∈ B, ‖u ℓ‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun ℓ _ => ?_
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hA ℓ (u ℓ)) 2
  have h3 : ‖∑ ℓ ∈ B, A ℓ (u ℓ)‖ ^ 2 ≤ B.card * (κ ^ 2 * ∑ ℓ ∈ B, ‖u ℓ‖ ^ 2) :=
    h1.trans (mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _))
  calc s * ‖∑ ℓ ∈ B, A ℓ (u ℓ)‖ ^ 2 ≤ s * (B.card * (κ ^ 2 * ∑ ℓ ∈ B, ‖u ℓ‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left h3 hs
    _ = _ := by ring

section Active

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- [proved-derived; formal-checked] **An active element's growth.** An element whose storage
obeys `½‖s′‖² − ½‖b‖² ≤ ⟨½(b + s′), w⟩` (the reaction stage balance of `HNN/Word` with its passive
part dropped, `w = W_c c`) and `‖w‖ ≤ ωc` has `‖s′‖ ≤ ‖b‖ + ωc`. -/
theorem active_element_growth {b s' w : E} {ω c : ℝ}
    (hbal : (1 / 2 : ℝ) * ‖s'‖ ^ 2 - (1 / 2 : ℝ) * ‖b‖ ^ 2 ≤ inner ℝ ((1 / 2 : ℝ) • (b + s')) w)
    (hw : ‖w‖ ≤ ω * c) : ‖s'‖ ≤ ‖b‖ + ω * c := by
  have hin : inner ℝ ((1 / 2 : ℝ) • (b + s')) w ≤ (1 / 2 : ℝ) * (‖b‖ + ‖s'‖) * (ω * c) := by
    rw [real_inner_smul_left]
    have h1 := real_inner_le_norm (b + s') w
    have h2 := norm_add_le b s'
    have h3 := mul_le_mul h2 hw (norm_nonneg _) (by positivity)
    nlinarith [norm_nonneg w]
  have hk : 0 ≤ ω * c := (norm_nonneg w).trans hw
  by_contra hlt
  replace hlt := not_le.mp hlt
  have hs : 0 ≤ ‖b‖ := norm_nonneg b
  nlinarith [hbal, hin, hlt, hs, hk]

omit [InnerProductSpace ℝ E] in
/-- [proved-derived; formal-checked] **An active element's energy growth**: with `‖b‖, c ≤ r` and
`ω ≥ 0`, `‖s′‖² ≤ (1 + ω)² r²` and `‖s′‖² − ‖b‖² ≤ (2ω + ω²) r²`. -/
theorem active_energy_growth {b s' : E} {ω c r : ℝ} (hgrow : ‖s'‖ ≤ ‖b‖ + ω * c)
    (hω : 0 ≤ ω) (hc : 0 ≤ c) (hb : ‖b‖ ≤ r) (hcr : c ≤ r) :
    ‖s'‖ ^ 2 ≤ (1 + ω) ^ 2 * r ^ 2 ∧ ‖s'‖ ^ 2 - ‖b‖ ^ 2 ≤ (2 * ω + ω ^ 2) * r ^ 2 := by
  have hbn := norm_nonneg b
  have hsn := norm_nonneg s'
  have hwc : ω * c ≤ ω * r := mul_le_mul_of_nonneg_left hcr hω
  have hs : ‖s'‖ ≤ ‖b‖ + ω * r := hgrow.trans (by linarith)
  have hsq : ‖s'‖ ^ 2 ≤ (‖b‖ + ω * r) ^ 2 := pow_le_pow_left₀ hsn hs 2
  have hr : 0 ≤ r := hbn.trans hb
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hb hω]
  · nlinarith [mul_le_mul_of_nonneg_left hb (mul_nonneg hω hr)]

end Active

/-! ## 8. The factor families' certified step -/

section Factor

/-- [proved-derived; formal-checked] **The factor family's unit step is aligned.** The family's
descent covector `G`, read through its scalar metric `h' > 0` (the family's carried feature-energy
statistic), gives the unit step `D = G/h'`, whose first-order decrease is
`a = ⟨G, D⟩ = |G|²/h' ≥ 0`: the alignment is checked, never negative, at a positive metric. -/
theorem factor_unit_step_alignment {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (G : E) {h : ℝ} (hh : 0 < h) :
    inner ℝ G (h⁻¹ • G) = h⁻¹ * ‖G‖ ^ 2 ∧ 0 ≤ inner ℝ G (h⁻¹ • G) := by
  have ha : inner ℝ G (h⁻¹ • G) = h⁻¹ * ‖G‖ ^ 2 := by
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
  exact ⟨ha, by rw [ha]; positivity⟩

/-- [proved-derived; formal-checked] **The square's output along its ray.** A square factor's
output is the diagonal `x ↦ B(x, x)` of a bilinear map of the factor (the carriers `c cᵀ`, `b bᵀ`,
`F Fᵀ`, the passive factor `−f fᵀ`, a skew slice `u vᵀ − v uᵀ` in the pair `(u, v)`, a gain
`g² · base`). Along the ray `x + tD` it moves between `s` and `t` by
`(t − s)(B(D, x) + B(x, D)) + (t² − s²) B(D, D)`. -/
theorem square_ray_identity {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (B : E →L[ℝ] E →L[ℝ] F) (x D : E) (s t : ℝ) :
    B (x + t • D) (x + t • D) - B (x + s • D) (x + s • D) =
      (t - s) • (B D x + B x D) + (t ^ 2 - s ^ 2) • B D D := by
  simp only [map_add, map_smul, _root_.add_apply, _root_.smul_apply]
  module

/-- [proved-derived; formal-checked] **The square's output moves are Lipschitz along its ray**, with
the constant read at the ray's end:
`‖B(x + tD, x + tD) − B(x + sD, x + sD)‖ ≤ |t − s| ‖B‖ ‖D‖ (2‖x‖ + |t + s| ‖D‖)`. -/
theorem square_ray_move {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (B : E →L[ℝ] E →L[ℝ] F) (x D : E) (s t : ℝ) :
    ‖B (x + t • D) (x + t • D) - B (x + s • D) (x + s • D)‖ ≤
      |t - s| * (‖B‖ * ‖D‖ * (2 * ‖x‖ + |t + s| * ‖D‖)) := by
  rw [square_ray_identity, show (t ^ 2 - s ^ 2) • B D D = (t - s) • ((t + s) • B D D) by
    rw [smul_smul]; ring_nf, ← smul_add, norm_smul, Real.norm_eq_abs]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  have h1 := B.le_opNorm₂ D x
  have h2 := B.le_opNorm₂ x D
  have h3 := B.le_opNorm₂ D D
  calc ‖B D x + B x D + (t + s) • B D D‖ ≤ ‖B D x‖ + ‖B x D‖ + |t + s| * ‖B D D‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, Real.norm_eq_abs]
        linarith [norm_add_le (B D x) (B x D)]
    _ ≤ ‖B‖ * ‖D‖ * ‖x‖ + ‖B‖ * ‖x‖ * ‖D‖ + |t + s| * (‖B‖ * ‖D‖ * ‖D‖) := by gcongr
    _ = _ := by ring

/-- [proved-derived; formal-checked] **The square's Jacobian along its ray**:
`d/dt B(x + tD, x + tD) = B(D, x + tD) + B(x + tD, D)`. -/
theorem square_ray_deriv {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (B : E →L[ℝ] E →L[ℝ] F) (x D : E) (t : ℝ) :
    HasDerivAt (fun t : ℝ => B (x + t • D) (x + t • D)) (B D (x + t • D) + B (x + t • D) D) t := by
  have hγ : HasDerivAt (fun t : ℝ => x + t • D) D t := by
    simpa using ((hasDerivAt_id t).smul_const D).const_add x
  exact (B.hasDerivAt_of_bilinear (fun _ => hγ) (fun _ => hγ)).congr_deriv (add_comm _ _)

/-- [proved-derived; formal-checked] **The output's moves, bounded at the ray's end.** On the ray
`[0, η]` the square's Jacobian is at most `2‖B‖ ‖D‖ (‖x‖ + η‖D‖)`. This is the move `‖u_ℓ‖` that
`gauss_newton_curvature` reads: with `b` its square, `κ²` the gain from the output to the station
logits and `n` loci stepping together, the family's Gauss–Newton curvature is `C = n s κ² b`. -/
theorem square_ray_deriv_bound {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (B : E →L[ℝ] E →L[ℝ] F) (x D : E) {t η : ℝ}
    (ht : 0 ≤ t) (htη : t ≤ η) :
    ‖B D (x + t • D) + B (x + t • D) D‖ ≤ 2 * ‖B‖ * ‖D‖ * (‖x‖ + η * ‖D‖) := by
  have hy : ‖x + t • D‖ ≤ ‖x‖ + η * ‖D‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_of_nonneg ht]
    gcongr
  have h1 := B.le_opNorm₂ D (x + t • D)
  have h2 := B.le_opNorm₂ (x + t • D) D
  calc ‖B D (x + t • D) + B (x + t • D) D‖ ≤ ‖B D (x + t • D)‖ + ‖B (x + t • D) D‖ :=
        norm_add_le _ _
    _ ≤ ‖B‖ * ‖D‖ * ‖x + t • D‖ + ‖B‖ * ‖x + t • D‖ * ‖D‖ := add_le_add h1 h2
    _ = 2 * (‖B‖ * ‖D‖) * ‖x + t • D‖ := by ring
    _ ≤ 2 * (‖B‖ * ‖D‖) * (‖x‖ + η * ‖D‖) := by gcongr
    _ = _ := by ring

/-- [proved-derived; formal-checked] **The transit's solve is a contraction.** An operator `m ⪰ 1`
(`‖v‖² ≤ ⟨v, m v⟩`), as the transit's normalized `m_a = 1 + (G/2h)(2C + hD + (h²/2)K)` is for
positive semidefinite carriers, has `‖v‖ ≤ ‖m v‖`: the solve `m ζ = r` has `|ζ| ≤ |r|`. -/
theorem contracting_resolvent {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (M : E →L[ℝ] E) (hM : ∀ v, ‖v‖ ^ 2 ≤ inner ℝ v (M v)) (v : E) : ‖v‖ ≤ ‖M v‖ := by
  have h1 := (hM v).trans (real_inner_le_norm v (M v))
  by_contra hlt
  replace hlt := not_le.mp hlt
  nlinarith [norm_nonneg (M v), norm_nonneg v]

/-- [proved-derived; formal-checked] **The transit's difference power.** The transit's difference
state `δζ` moves the waves at its two ends by `δa = ∓ι δζ/h` (ends with `‖ι v‖ ≤ ‖v‖`), which
carry `(h/4) G |δa|²`, and the contact's states by `δw = (G/h) δζ` and `δu = (G/2) δζ`, which store
`½⟨δw, C δw⟩` and `½⟨δu, K δu⟩` under `⟨w, C w⟩ ≤ c|w|²` and `⟨u, K u⟩ ≤ k|u|²`. The whole is at
most `(G/2h + ½(G/h)² c + ⅛ G² k) |δζ|²`. The loaded resonator is the case `G = 2Y` with both
ends its one port of admittance `Y` (`ιg = ιh` the identity): its returned wave `(2/h) δζ` carries
`(h/4) Y |2δζ/h|² = (h/4)(2Y)(|δζ/h|² + |δζ/h|²)`, and its states move by `2δω = (G/h) δζ` and
`h δω = (G/2) δζ` at `δω = (Y/h) δζ`. -/
theorem transit_difference_power {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] (ιg ιh : E →L[ℝ] V)
    (hιg : ∀ v, ‖ιg v‖ ≤ ‖v‖) (hιh : ∀ v, ‖ιh v‖ ≤ ‖v‖) (C K : E →L[ℝ] E) {c k G h : ℝ}
    (hC : ∀ w, inner ℝ w (C w) ≤ c * ‖w‖ ^ 2) (hK : ∀ u, inner ℝ u (K u) ≤ k * ‖u‖ ^ 2)
    (hG : 0 < G) (hh : 0 < h) (v : E) :
    (h / 4) * G * (‖ιg ((1 / h) • v)‖ ^ 2 + ‖ιh ((1 / h) • v)‖ ^ 2) +
        (1 / 2) * inner ℝ ((G / h) • v) (C ((G / h) • v)) +
        (1 / 2) * inner ℝ ((G / 2) • v) (K ((G / 2) • v)) ≤
      (G / (2 * h) + (1 / 2) * (G / h) ^ 2 * c + (1 / 8) * G ^ 2 * k) * ‖v‖ ^ 2 := by
  have hn : ‖(1 / h) • v‖ = (1 / h) * ‖v‖ := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
  have hwave : ∀ ι : E →L[ℝ] V, (∀ v, ‖ι v‖ ≤ ‖v‖) →
      ‖ι ((1 / h) • v)‖ ^ 2 ≤ ((1 / h) * ‖v‖) ^ 2 := fun ι hι =>
    pow_le_pow_left₀ (norm_nonneg _) ((hι _).trans hn.le) 2
  have hw := hC ((G / h) • v)
  have hu := hK ((G / 2) • v)
  rw [norm_smul, Real.norm_of_nonneg (by positivity)] at hw hu
  have hwaves : (h / 4) * G * (‖ιg ((1 / h) • v)‖ ^ 2 + ‖ιh ((1 / h) • v)‖ ^ 2) ≤
      (h / 4) * G * (2 * ((1 / h) * ‖v‖) ^ 2) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    linarith [hwave ιg hιg, hwave ιh hιh]
  have heq : (h / 4) * G * (2 * ((1 / h) * ‖v‖) ^ 2) = G / (2 * h) * ‖v‖ ^ 2 := by
    field_simp; ring
  nlinarith [hwaves, heq, hw, hu]

end Factor

/-! ## 9. The tightened certificate -/

section Joint

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- [proved-derived; formal-checked] **The joint certificate descends, through
`certified_step_descends`.** Families `ℓ ∈ B` stepping together by `η_ℓ ≥ 0`, with first-order
decreases `a_ℓ ≥ 0`, under the joint model `φ ≤ φ₀ − Σ η_ℓ a_ℓ + ½ Q` whose curvature term is at
most the triangle's `s (Σ η_ℓ m_ℓ)²` (`joint_move_triangle`), descend by at least half their
first-order decrease when `s (Σ η_ℓ m_ℓ)² ≤ Σ η_ℓ a_ℓ`. The joint curvature apportioned to the
families by their decreases, `C_ℓ = s (Σ η m)² a_ℓ / (η_ℓ Σ η a)`, gives `η_ℓ C_ℓ ≤ a_ℓ` and
`Σ η_ℓ² C_ℓ = s (Σ η m)²`: the hypotheses of `certified_step_descends`, which concludes. -/
theorem joint_step_descends {ι : Type*} (B : Finset ι) {φ₀ φη Q s : 𝕜} {η a m : ι → 𝕜}
    (hmodel : φη ≤ φ₀ - ∑ ℓ ∈ B, η ℓ * a ℓ + (1 / 2) * Q)
    (hQ : Q ≤ s * (∑ ℓ ∈ B, η ℓ * m ℓ) ^ 2)
    (hjoint : s * (∑ ℓ ∈ B, η ℓ * m ℓ) ^ 2 ≤ ∑ ℓ ∈ B, η ℓ * a ℓ)
    (hη : ∀ ℓ ∈ B, 0 ≤ η ℓ) (ha : ∀ ℓ ∈ B, 0 ≤ a ℓ) :
    φη ≤ φ₀ - (1 / 2) * ∑ ℓ ∈ B, η ℓ * a ℓ := by
  set J := s * (∑ ℓ ∈ B, η ℓ * m ℓ) ^ 2
  set A := ∑ ℓ ∈ B, η ℓ * a ℓ
  have hA : 0 ≤ A := Finset.sum_nonneg fun ℓ hℓ => mul_nonneg (hη ℓ hℓ) (ha ℓ hℓ)
  let C : ι → 𝕜 := fun ℓ => if η ℓ = 0 then 0 else J / A * a ℓ / η ℓ
  have hterm : ∀ ℓ, η ℓ ^ 2 * C ℓ = J / A * (η ℓ * a ℓ) := by
    intro ℓ
    by_cases h : η ℓ = 0
    · simp [C, h]
    · simp only [C, h, if_false]
      field_simp
  refine certified_step_descends B (C := C) ?_ hη ?_
  · -- The apportioned curvature carries the whole joint term.
    have hsum : ∑ ℓ ∈ B, η ℓ ^ 2 * C ℓ = J / A * A := by
      rw [Finset.sum_congr rfl fun ℓ _ => hterm ℓ, ← Finset.mul_sum]
    rcases hA.lt_or_eq with hpos | hzero
    · have : J / A * A = J := div_mul_cancel₀ J hpos.ne'
      rw [hsum, this]
      linarith
    · have hJ : J ≤ 0 := hzero ▸ hjoint
      rw [hsum, ← hzero]
      simp only [mul_zero]
      linarith
  · intro ℓ hℓ
    by_cases h : η ℓ = 0
    · simp [C, h, ha ℓ hℓ]
    · have hηa : η ℓ * C ℓ = J / A * a ℓ := by
        simp only [C, h, if_false]
        field_simp
      rw [hηa]
      rcases hA.lt_or_eq with hpos | hzero
      · have hle : J / A ≤ 1 := (div_le_one hpos).mpr hjoint
        have := mul_le_mul_of_nonneg_right hle (ha ℓ hℓ)
        linarith
      · rw [← hzero, div_zero, zero_mul]
        exact ha ℓ hℓ

end Joint

/-- [proved-derived; formal-checked] **The joint moves' triangle** (Cauchy–Schwarz on the joint
ray's cross terms, `2 η_ℓ η_k ⟨u_ℓ, u_k⟩ ≤ 2 η_ℓ η_k m_ℓ m_k`): families stepping together by
`η_ℓ ≥ 0`, whose logit moves per unit step are at most `m_ℓ`, move the logits by at most
`Σ η_ℓ m_ℓ`, so a score of curvature `s ≥ 0` has joint term `s‖Σ η_ℓ u_ℓ‖² ≤ s (Σ η_ℓ m_ℓ)²`.
With `m_ℓ = κ_ℓ √b_ℓ` it is at most `gauss_newton_curvature`'s `|B| s Σ κ² b η²`, and far below it
when the families' moves differ. -/
theorem joint_move_triangle {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type*}
    (B : Finset ι) {η m : ι → ℝ} (u : ι → E) (hη : ∀ ℓ ∈ B, 0 ≤ η ℓ)
    (hu : ∀ ℓ ∈ B, ‖u ℓ‖ ≤ m ℓ) {s : ℝ} (hs : 0 ≤ s) :
    s * ‖∑ ℓ ∈ B, η ℓ • u ℓ‖ ^ 2 ≤ s * (∑ ℓ ∈ B, η ℓ * m ℓ) ^ 2 := by
  have htri : ‖∑ ℓ ∈ B, η ℓ • u ℓ‖ ≤ ∑ ℓ ∈ B, η ℓ * m ℓ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ℓ hℓ => ?_)
    rw [norm_smul, Real.norm_of_nonneg (hη ℓ hℓ)]
    exact mul_le_mul_of_nonneg_left (hu ℓ hℓ) (hη ℓ hℓ)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) htri 2) hs

section Gram

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ F]

/-- [proved-derived; formal-checked] **A Gram certificate bounds the map.** For `T` with adjoint
`S` (`⟨T x, y⟩ = ⟨x, S y⟩`), a certified `μ I − S T ⪰ 0` (`⟨x, S T x⟩ ≤ μ‖x‖²`, decided in the
machine by exact inertia) gives `‖T x‖² ≤ μ‖x‖²`: the spectral bound the readout's gain reads in
place of the Schur test. -/
theorem gram_certificate_bound (T : E →ₗ[ℝ] F) (S : F →ₗ[ℝ] E)
    (hadj : ∀ x y, inner ℝ (T x) y = inner ℝ x (S y)) {μ : ℝ}
    (hpsd : ∀ x, inner ℝ x (S (T x)) ≤ μ * ‖x‖ ^ 2) (x : E) : ‖T x‖ ^ 2 ≤ μ * ‖x‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, hadj]
  exact hpsd x

/-- [proved-derived; formal-checked] **The smaller side's Gram suffices.** A bound
`‖S y‖² ≤ μ‖y‖²` on the adjoint (its Gram `T S`, the smaller when `T` has fewer rows than
columns) bounds `T` by the same `μ ≥ 0`. -/
theorem adjoint_gram_certificate_bound (T : E →ₗ[ℝ] F) (S : F →ₗ[ℝ] E)
    (hadj : ∀ x y, inner ℝ (T x) y = inner ℝ x (S y)) {μ : ℝ} (hμ : 0 ≤ μ)
    (hS : ∀ y, ‖S y‖ ^ 2 ≤ μ * ‖y‖ ^ 2) (x : E) : ‖T x‖ ^ 2 ≤ μ * ‖x‖ ^ 2 := by
  have h1 : ‖T x‖ ^ 2 = inner ℝ x (S (T x)) := by
    rw [← real_inner_self_eq_norm_sq, hadj]
  have h2 : inner ℝ x (S (T x)) ≤ ‖x‖ * ‖S (T x)‖ := real_inner_le_norm _ _
  have h3 := hS (T x)
  set t := ‖T x‖ ^ 2 with ht
  have ht0 : 0 ≤ t := sq_nonneg _
  have hx := norm_nonneg x
  have hs := norm_nonneg (S (T x))
  -- `t ≤ ‖x‖ ‖S T x‖` and `‖S T x‖² ≤ μ t` give `t² ≤ μ ‖x‖² t`.
  have hsq : t ^ 2 ≤ μ * ‖x‖ ^ 2 * t := by
    have htx : t ≤ ‖x‖ * ‖S (T x)‖ := h1 ▸ h2
    have := pow_le_pow_left₀ ht0 htx 2
    calc t ^ 2 ≤ (‖x‖ * ‖S (T x)‖) ^ 2 := this
      _ = ‖x‖ ^ 2 * ‖S (T x)‖ ^ 2 := by ring
      _ ≤ ‖x‖ ^ 2 * (μ * ‖T x‖ ^ 2) := mul_le_mul_of_nonneg_left h3 (sq_nonneg _)
      _ = μ * ‖x‖ ^ 2 * t := by rw [ht]; ring
  rcases ht0.lt_or_eq with hpos | hzero
  · nlinarith
  · rw [← hzero]
    positivity

end Gram

/-- [proved-derived; formal-checked] **The face's entrywise error.** A matrix whose entries are at
most `ε` in magnitude (the readout read on a dyadic face, `|E_ij| ≤ 2^(e−1)`) moves a vector by at
most `m n ε²` times its squared length: `‖E v‖² ≤ m n ε² ‖v‖²` (Cauchy–Schwarz on each row). -/
theorem entrywise_error_bound {m n : Type*} [Fintype m] [Fintype n] (E : Matrix m n ℝ) {ε : ℝ}
    (hE : ∀ i j, |E i j| ≤ ε) (v : n → ℝ) :
    (E *ᵥ v) ⬝ᵥ (E *ᵥ v) ≤ Fintype.card m * Fintype.card n * ε ^ 2 * (v ⬝ᵥ v) := by
  have hrow : ∀ i, (E *ᵥ v) i * (E *ᵥ v) i ≤ Fintype.card n * ε ^ 2 * (v ⬝ᵥ v) := by
    intro i
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => E i j) v
    have hentries : ∑ j, E i j ^ 2 ≤ Fintype.card n * ε ^ 2 := by
      calc ∑ j, E i j ^ 2 ≤ ∑ _j : n, ε ^ 2 :=
            Finset.sum_le_sum fun j _ => by
              have := hE i j
              nlinarith [abs_nonneg (E i j), sq_abs (E i j)]
        _ = Fintype.card n * ε ^ 2 := by simp
    have hv : 0 ≤ ∑ j, v j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
    have hdot : v ⬝ᵥ v = ∑ j, v j ^ 2 := by simp [dotProduct, sq]
    calc (E *ᵥ v) i * (E *ᵥ v) i = (∑ j, E i j * v j) ^ 2 := by simp [Matrix.mulVec, dotProduct, sq]
      _ ≤ (∑ j, E i j ^ 2) * ∑ j, v j ^ 2 := hcs
      _ ≤ Fintype.card n * ε ^ 2 * ∑ j, v j ^ 2 := mul_le_mul_of_nonneg_right hentries hv
      _ = Fintype.card n * ε ^ 2 * (v ⬝ᵥ v) := by rw [hdot]
  calc (E *ᵥ v) ⬝ᵥ (E *ᵥ v) = ∑ i, (E *ᵥ v) i * (E *ᵥ v) i := rfl
    _ ≤ ∑ _i : m, Fintype.card n * ε ^ 2 * (v ⬝ᵥ v) := Finset.sum_le_sum fun i _ => hrow i
    _ = Fintype.card m * Fintype.card n * ε ^ 2 * (v ⬝ᵥ v) := by simp; ring

/-! ## 10. The pumped medium's reach in the gain -/

section Reach

variable {E F : Type*} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]

/-- [proved-derived; formal-checked] **A span's transport through two carriers**: a difference
carried for a span by a map `Λ` of energy gain `a` (the pumped ring's reach over the span,
`HNN/Floquet.floquet_span_reach`) and by a map `Ψ` of energy gain `b` (the medium's passive and
contrast ticks, `(1 + ω)^(2(s − 1))`) moves by at most `b a`: `‖Ψ(Λ v)‖² ≤ b a ‖v‖²`. -/
theorem span_transport_compose {G : Type*} [SeminormedAddCommGroup G] (Λ : E → F) (Ψ : F → G)
    {a b : ℝ} (hb : 0 ≤ b) (hΛ : ∀ v, ‖Λ v‖ ^ 2 ≤ a * ‖v‖ ^ 2)
    (hΨ : ∀ w, ‖Ψ w‖ ^ 2 ≤ b * ‖w‖ ^ 2) (v : E) : ‖Ψ (Λ v)‖ ^ 2 ≤ b * a * ‖v‖ ^ 2 := by
  calc ‖Ψ (Λ v)‖ ^ 2 ≤ b * ‖Λ v‖ ^ 2 := hΨ (Λ v)
    _ ≤ b * (a * ‖v‖ ^ 2) := mul_le_mul_of_nonneg_left (hΛ v) hb
    _ = b * a * ‖v‖ ^ 2 := by ring

/-- [proved-derived; formal-checked] **The gain over the stations and the ticks** (Cauchy–Schwarz
over the ticks): a locus's moves `δ_τ`, one a tick, reaching station `j`'s logits through span maps
of energy gains `‖Φ_(jτ) v‖² ≤ G_(jτ) ‖v‖²` (zero past the station), move the stacked logits by
`Σ_j ‖Σ_τ Φ_(jτ) δ_τ‖² ≤ (Σ_j Σ_τ G_(jτ)) Σ_τ ‖δ_τ‖²`: the gain `κ²` is the sum of the span gains,
the moves `b` the sum of the moves. With `G_(jτ) = c (1 + ω)^(2(T_j − τ − 1)) F(T_j − τ)` it is the
certified step's `κ²` through a pumped medium (`hnn::constitution`, "The pumped medium's reach"). -/
theorem station_tick_gain {J T : Type*} (stations : Finset J) (ticks : Finset T)
    (Φ : J → T → E → F) (G : J → T → ℝ) (hG : ∀ j τ, 0 ≤ G j τ)
    (hΦ : ∀ j τ v, ‖Φ j τ v‖ ^ 2 ≤ G j τ * ‖v‖ ^ 2) (δ : T → E) :
    ∑ j ∈ stations, ‖∑ τ ∈ ticks, Φ j τ (δ τ)‖ ^ 2 ≤
      (∑ j ∈ stations, ∑ τ ∈ ticks, G j τ) * ∑ τ ∈ ticks, ‖δ τ‖ ^ 2 := by
  have hamp : ∀ j τ v, ‖Φ j τ v‖ ≤ Real.sqrt (G j τ) * ‖v‖ := by
    intro j τ v
    have h := hΦ j τ v
    have hr : Real.sqrt (G j τ * ‖v‖ ^ 2) = Real.sqrt (G j τ) * ‖v‖ := by
      rw [Real.sqrt_mul (hG j τ), Real.sqrt_sq (norm_nonneg v)]
    rw [← hr]
    exact Real.le_sqrt_of_sq_le h
  have hstation : ∀ j, ‖∑ τ ∈ ticks, Φ j τ (δ τ)‖ ^ 2 ≤
      (∑ τ ∈ ticks, G j τ) * ∑ τ ∈ ticks, ‖δ τ‖ ^ 2 := by
    intro j
    have htri : ‖∑ τ ∈ ticks, Φ j τ (δ τ)‖ ≤ ∑ τ ∈ ticks, Real.sqrt (G j τ) * ‖δ τ‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun τ _ => hamp j τ (δ τ))
    have hsq := pow_le_pow_left₀ (norm_nonneg _) htri 2
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq ticks (fun τ => Real.sqrt (G j τ))
      (fun τ => ‖δ τ‖)
    have hroot : ∑ τ ∈ ticks, Real.sqrt (G j τ) ^ 2 = ∑ τ ∈ ticks, G j τ :=
      Finset.sum_congr rfl fun τ _ => Real.sq_sqrt (hG j τ)
    rw [hroot] at hcs
    exact hsq.trans hcs
  calc ∑ j ∈ stations, ‖∑ τ ∈ ticks, Φ j τ (δ τ)‖ ^ 2
      ≤ ∑ j ∈ stations, (∑ τ ∈ ticks, G j τ) * ∑ τ ∈ ticks, ‖δ τ‖ ^ 2 :=
        Finset.sum_le_sum fun j _ => hstation j
    _ = (∑ j ∈ stations, ∑ τ ∈ ticks, G j τ) * ∑ τ ∈ ticks, ‖δ τ‖ ^ 2 := by
        rw [Finset.sum_mul]

/-- [proved-derived; formal-checked] **One station's re-entries** (the triangle on their
amplitudes): the same injection re-entering at the ticks `T_n` reaches the station through span
maps with `‖Φ_n v‖² ≤ a_n² F_n ‖v‖²` and `0 ≤ F_n ≤ F`, so
`‖Σ_n Φ_n v‖² ≤ F (Σ_n a_n)² ‖v‖²`: the pumped factor at the longest span multiplies the passive
entry gain `(Σ_n (1 + ω)^(T_j − T_n))²`. -/
theorem entry_span_gain {ι : Type*} (entries : Finset ι) (Φ : ι → E → F) (a f : ι → ℝ)
    {Fmax : ℝ} (hF : 0 ≤ Fmax) (ha : ∀ n ∈ entries, 0 ≤ a n)
    (hf : ∀ n ∈ entries, 0 ≤ f n ∧ f n ≤ Fmax)
    (hΦ : ∀ n ∈ entries, ∀ v, ‖Φ n v‖ ^ 2 ≤ a n ^ 2 * f n * ‖v‖ ^ 2) (v : E) :
    ‖∑ n ∈ entries, Φ n v‖ ^ 2 ≤ Fmax * (∑ n ∈ entries, a n) ^ 2 * ‖v‖ ^ 2 := by
  have hamp : ∀ n ∈ entries, ‖Φ n v‖ ≤ Real.sqrt Fmax * a n * ‖v‖ := by
    intro n hn
    have h := hΦ n hn v
    have hbound : a n ^ 2 * f n * ‖v‖ ^ 2 ≤ (Real.sqrt Fmax * a n * ‖v‖) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hF]
      have := (hf n hn).2
      have hav : 0 ≤ a n ^ 2 * ‖v‖ ^ 2 := by positivity
      nlinarith
    have hnn : 0 ≤ Real.sqrt Fmax * a n * ‖v‖ :=
      mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (ha n hn)) (norm_nonneg v)
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hnn two_ne_zero).mp (h.trans hbound)
  have htri : ‖∑ n ∈ entries, Φ n v‖ ≤ Real.sqrt Fmax * (∑ n ∈ entries, a n) * ‖v‖ := by
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hamp).trans (le_of_eq ?_))
    rw [Finset.mul_sum, Finset.sum_mul]
  have hsq := pow_le_pow_left₀ (norm_nonneg _) htri 2
  calc ‖∑ n ∈ entries, Φ n v‖ ^ 2 ≤ (Real.sqrt Fmax * (∑ n ∈ entries, a n) * ‖v‖) ^ 2 := hsq
    _ = Fmax * (∑ n ∈ entries, a n) ^ 2 * ‖v‖ ^ 2 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hF]

end Reach

/-- [definition] **The running maximum** of a span's reach, `max_(s′ ≤ s) R(s′)`: the factor over
every span a difference can be carried by one pumped ring within `s` ticks. -/
def runningMax (R : ℕ → ℝ) (s : ℕ) : ℝ := (Finset.range (s + 1)).sup' Finset.nonempty_range_add_one R

/-- [proved-derived; formal-checked] The running maximum bounds every shorter span's reach. -/
theorem le_runningMax (R : ℕ → ℝ) {s' s : ℕ} (h : s' ≤ s) : R s' ≤ runningMax R s :=
  Finset.le_sup' R (Finset.mem_range.mpr (Nat.lt_succ_of_le h))

/-- [proved-derived; formal-checked] The running maximum does not fall as the span grows. -/
theorem runningMax_mono (R : ℕ → ℝ) : Monotone (runningMax R) := by
  intro s t hst
  refine Finset.sup'_le _ _ fun s' hs' => le_runningMax R ?_
  exact (Nat.lt_succ_iff.mp (Finset.mem_range.mp hs')).trans hst

/-- [proved-derived; formal-checked] **The pumped medium's span factor**: a difference whose span of
`s` ticks passes through several pumped rings, carried by ring `r` for `s_r ≤ s` ticks with reach
`R_r(s_r) ≥ 0`, moves by at most `∏_r R_r(s_r) ≤ ∏_r max_(s′ ≤ s) R_r(s′)`, the factor
`F(s) = ∏_r runningMax R_r s` the certified step reads, which does not fall with `s`. -/
theorem pumped_span_factor {ι : Type*} (rings : Finset ι) (R : ι → ℕ → ℝ)
    (hR : ∀ r ∈ rings, ∀ s, 0 ≤ R r s) (span : ι → ℕ) {s : ℕ}
    (hspan : ∀ r ∈ rings, span r ≤ s) :
    ∏ r ∈ rings, R r (span r) ≤ ∏ r ∈ rings, runningMax (R r) s :=
  Finset.prod_le_prod (fun r hr => hR r hr (span r)) fun r hr => le_runningMax (R r) (hspan r hr)

end Holonics.HolonCore
