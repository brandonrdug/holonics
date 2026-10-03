import Holonics.HNN.Ring

/-!
# HNN.DepositHold: the deposit holds `(u, π)`, and the source mass is the imposed storage's inertia

[definition] The deposit record
(`research/records/2026-10-03_THE_DEPOSIT_HOLDS_THE_CARRIED_MOMENTUM_AND_THE_ACCRETED_MASS_IS_THE_THROWS_DAMPING.md`,
Answer 2, 3 and 7, §6 items 1 and 3; #62). A contact's ring ticks by the midpoint (Cayley) law in
descriptor form, `(2C + (h²/2) K) ω = 2C w − h K u`, `u′ = u + hω`, `w′ = 2ω − w`
(`HNN/Ring.{closedOperator, ring_descriptor_tick_conserves}`); a deposit changes `(C, K)` between
two ticks. The source port's map `E` moves with the Gram `H` of its returns for its mass.

[proved-derived; formal-checked] What is proved.

1. **The tick is the midpoint law on `(u, π = C w)`** (§1). For any `ω`,
   `C(u′ − u) = (h/2)(π + π′)` (`tick_canonical_position`); at the closed solve,
   `π′ − π = −(h/2) K (u + u′)` (`tick_canonical_momentum`). So the tick reads the rate only
   through `π`: two rates with one momentum give one successor `(u′, π′)`
   (`tick_reads_momentum`), and `w` modulo `ker C` is read by no later tick.
2. **A deposit at held `(u, π)` moves the energy by exactly its deposit term** (§2). With
   `C′ w′ = C w` and `C` symmetric (no sign, no invertibility),
   `E_(C′,K′)(u, w′) − E_(C,K)(u, w) = −½⟨w′, (C′ − C) w′⟩ − ½⟨w − w′, C (w − w′)⟩ + ½⟨u, (K′ − K) u⟩`
   (`hold_energy`, `depositTerm`): `MoveDirection.held_momentum_loss`'s identity on the contact's
   operators, plus the stiffness part at the held position. So the reception's balance across
   tick, deposit, tick is the two ticks' port, dissipation and chart terms plus the deposit term
   (`reception_hold_balance`); with closed ticks it is the deposit term alone
   (`closed_reception_hold_balance`).
3. **The hold is the limit of every ramp** (§3). Let the deposit take `m` sub-ticks of step `s`
   (ramp time `τ = m s`), each sub-tick the midpoint law on `(u, π)` with its own `(C_j, K_j)` and a
   left inverse `X_j C_j = 1`. If the state stays within `U`, `P` and the parameters within
   `‖K_j‖∞ ≤ κ`, `‖X_j‖∞ ≤ γ`, then every coordinate moves by at most
   `|π_m − π_0| ≤ τ κ U` and `|u_m − u_0| ≤ τ γ P` (`ramp_moves_by_at_most`), whatever the jump of
   the parameters. So `(u, π)` is continuous as `τ → 0`, and the rate after the ramp is within
   `γ τ κ U` of the held-momentum rate `X_m π_0` (`ramp_rate_near_held`), the solution of
   `C′ w′ = C w` of item 2. The rate itself jumps by `(X_m − X_0) π_0`, which does not vanish with
   `τ`. This is the sudden-change law of the Hamiltonian `½⟨π, C⁻¹ π⟩ + ½⟨u, K u⟩` (Answer 3), on
   the scheme the tick executes.
4. **The source mass is the imposed storage's inertia, less the prior** (§4). With the carried
   Gram `H = H₀ + Σ_t w_t f_t f_tᵀ` (`hnn::constitution::NormalLaw`: the prior `H₀ = 2^k I`, each
   return's weight and feature) and the storage `S(E) = Σ_t (w_t/2)|E f_t|²` that `E` imposes on
   the returns' features, `½⟨ΔE H, ΔE⟩ = ½⟨ΔE H₀, ΔE⟩ + S(ΔE)` (`kinetic_gram`), and
   `S(E + ΔE) = S(E) + Σ_t w_t ⟨E f_t, ΔE f_t⟩ + S(ΔE)` (`imposed_storage_expand`). So
   `½⟨ΔE H, ΔE⟩` is the prior's reading plus exactly the second-order part of the imposed storage's
   change (`kinetic_is_imposed_curvature`); along `E + τV` the imposed storage's power at `τ` is
   `Σ_t w_t ⟨(E + τV) f_t, V f_t⟩` and its second derivative is `2 S(V)`
   (`imposed_storage_along_line`). The record's reading "½⟨ΔE H, ΔE⟩ is the imposed storage power"
   holds for `H − H₀`, not for `H`: under a positive prior `c I` the prior's reading
   `½ c Σ|ΔE|²` is positive for every nonzero move (`prior_reading_pos`), and it is no imposed
   storage of any return. Two readings remain the record's: that the source port imposes
   `s_t = E f_t`, and that the returns' weights `w_t` are the source rings' storage weights
   (`E_S` reads `(h/4) Y_g`); the identity is exact once both are declared.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.HNN.DepositHold

open Matrix
open Holonics.HNN.Propagation
open Holonics.HNN.Ring
open scoped BigOperators

/-! ## 1. The tick is the midpoint law on `(u, π)` -/

section Canonical

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- [proved-derived; formal-checked] **The tick's position is the midpoint of the momenta.** For any
rate `ω`, the successor `(u + hω, 2ω − w)` satisfies `C(u′ − u) = (h/2)(C w + C w′)`. -/
theorem tick_canonical_position (C : E →L[ℝ] E) (h : ℝ) (u w ω : E) :
    C ((u + h • ω) - u) = (h / 2) • (C w + C ((2 : ℝ) • ω - w)) := by
  simp only [add_sub_cancel_left, map_smul, map_sub]
  module

/-- [proved-derived; formal-checked] **The tick's momentum is the midpoint of the forces.** At the
closed solve `(2C + (h²/2)K) ω = 2C w − h K u`, the momentum `π = C w` moves by
`C w′ − C w = −(h/2) K (u + u′)`. -/
theorem tick_canonical_momentum (C K : E →L[ℝ] E) {h : ℝ} {u w ω : E}
    (hsolve : closedOperator C K h ω = (2 : ℝ) • C w - h • K u) :
    C ((2 : ℝ) • ω - w) - C w = -(h / 2) • K (u + (u + h • ω)) := by
  simp only [closedOperator, _root_.add_apply, _root_.smul_apply] at hsolve
  simp only [map_sub, map_smul, map_add]
  linear_combination (norm := module) hsolve

/-- [proved-derived; formal-checked] **The tick reads the rate only through its momentum.** Two
rates with one momentum, `C w₁ = C w₂`, solved by an injective closed operator, give one rate `ω`
and one successor momentum: `w` modulo `ker C` is read by no later tick. -/
theorem tick_reads_momentum (C K : E →L[ℝ] E) {h : ℝ}
    (hinj : Function.Injective (closedOperator C K h)) {u w₁ w₂ ω₁ ω₂ : E} (hπ : C w₁ = C w₂)
    (h₁ : closedOperator C K h ω₁ = (2 : ℝ) • C w₁ - h • K u)
    (h₂ : closedOperator C K h ω₂ = (2 : ℝ) • C w₂ - h • K u) :
    ω₁ = ω₂ ∧ C ((2 : ℝ) • ω₁ - w₁) = C ((2 : ℝ) • ω₂ - w₂) := by
  have hω : ω₁ = ω₂ := hinj (by rw [h₁, h₂, hπ])
  refine ⟨hω, ?_⟩
  rw [map_sub, map_sub, hω, hπ]

end Canonical

/-! ## 2. The deposit's energy at held `(u, π)` and the reception's balance -/

section Hold

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- [definition] **The deposit term** at held `(u, π)`: the mass part
`−½⟨w′, (C′ − C) w′⟩ − ½⟨w − w′, C (w − w′)⟩` (the accreted mass at the new rate and the rate's
jump in the old mass) plus the stiffness part `½⟨u, (K′ − K) u⟩`. -/
noncomputable def depositTerm (C C' K K' : E →L[ℝ] E) (u w w' : E) : ℝ :=
  -((1 / 2) * inner ℝ w' ((C' - C) w') + (1 / 2) * inner ℝ (w - w') (C (w - w'))) +
    (1 / 2) * inner ℝ u ((K' - K) u)

/-- [proved-derived; formal-checked] **A deposit at held `(u, π)` moves the energy by its deposit
term.** With `C′ w′ = C w` and `C` symmetric, for any `C′`, `K`, `K′` (no sign, no invertibility):
`E_(C′,K′)(u, w′) − E_(C,K)(u, w) = depositTerm`. -/
theorem hold_energy (C C' K K' : E →L[ℝ] E) (hC : ∀ x y, inner ℝ (C x) y = inner ℝ x (C y))
    (u w w' : E) (hheld : C' w' = C w) :
    contactEnergy C' K' u w' - contactEnergy C K u w = depositTerm C C' K K' u w w' := by
  have hs : inner ℝ w (C w') = inner ℝ w' (C w) := by rw [← hC, real_inner_comm]
  have e : inner ℝ w' (C' w') = inner ℝ w' (C w) := by rw [hheld]
  simp only [contactEnergy, depositTerm, _root_.sub_apply, map_sub, inner_sub_left,
    inner_sub_right]
  rw [e, hs]
  ring

/-- [proved-derived; formal-checked] **The reception's balance with the deposit term.** A tick at
`(C, D, K)` with any executed rate `ω`, a deposit holding `(u₁, π₁)` (`C′ w₁′ = C w₁`), and a tick at
`(C′, D′, K′)` with any executed rate `ω′`: the energy moves by the two ticks' port work less their
dissipation plus their chart defects (`HNN/Ring.ring_tick_port_balance`), plus the deposit term. -/
theorem reception_hold_balance (C D K C' D' K' : E →L[ℝ] E)
    (hC : ∀ x y, inner ℝ (C x) y = inner ℝ x (C y)) (hK : ∀ x y, inner ℝ (K x) y = inner ℝ x (K y))
    (hC' : ∀ x y, inner ℝ (C' x) y = inner ℝ x (C' y))
    (hK' : ∀ x y, inner ℝ (K' x) y = inner ℝ x (K' y))
    {Y h : ℝ} (hY : Y ≠ 0) (u w β β' ω ω' w₁' : E)
    (hheld : C' w₁' = C ((2 : ℝ) • ω - w)) :
    contactEnergy C' K' ((u + h • ω) + h • ω') ((2 : ℝ) • ω' - w₁') - contactEnergy C K u w =
      (h * Y / 4 * (‖β‖ ^ 2 - ‖ringOut Y β ω‖ ^ 2) - h * inner ℝ ω (D ω) +
          inner ℝ ω (ringOperator C D K Y h ω - ringRight C K h u w β)) +
        depositTerm C C' K K' (u + h • ω) ((2 : ℝ) • ω - w) w₁' +
        (h * Y / 4 * (‖β'‖ ^ 2 - ‖ringOut Y β' ω'‖ ^ 2) - h * inner ℝ ω' (D' ω') +
          inner ℝ ω' (ringOperator C' D' K' Y h ω' - ringRight C' K' h (u + h • ω) w₁' β')) := by
  have t₁ := ring_tick_port_balance C D K hC hK (h := h) hY u w β ω
  have t₂ := ring_tick_port_balance C' D' K' hC' hK' (h := h) hY (u + h • ω) w₁' β' ω'
  have d := hold_energy C C' K K' hC (u + h • ω) ((2 : ℝ) • ω - w) w₁' hheld
  linarith

/-- [proved-derived; formal-checked] **With closed ticks the reception's balance is the deposit
term alone**: each closed lossless tick conserves its energy
(`HNN/Ring.ring_descriptor_tick_conserves`), so across tick, deposit at held `(u, π)`, tick the
energy moves by exactly `depositTerm`. -/
theorem closed_reception_hold_balance (C K C' K' : E →L[ℝ] E)
    (hC : ∀ x y, inner ℝ (C x) y = inner ℝ x (C y)) (hK : ∀ x y, inner ℝ (K x) y = inner ℝ x (K y))
    (hC' : ∀ x y, inner ℝ (C' x) y = inner ℝ x (C' y))
    (hK' : ∀ x y, inner ℝ (K' x) y = inner ℝ x (K' y))
    {h : ℝ} {u w ω ω' w₁' : E}
    (hsolve : closedOperator C K h ω = (2 : ℝ) • C w - h • K u)
    (hheld : C' w₁' = C ((2 : ℝ) • ω - w))
    (hsolve' : closedOperator C' K' h ω' = (2 : ℝ) • C' w₁' - h • K' (u + h • ω)) :
    contactEnergy C' K' ((u + h • ω) + h • ω') ((2 : ℝ) • ω' - w₁') =
      contactEnergy C K u w + depositTerm C C' K K' (u + h • ω) ((2 : ℝ) • ω - w) w₁' := by
  have t₁ := ring_descriptor_tick_conserves C K hC hK hsolve
  have t₂ := ring_descriptor_tick_conserves C' K' hC' hK' hsolve'
  have d := hold_energy C C' K K' hC (u + h • ω) ((2 : ℝ) • ω - w) w₁' hheld
  linarith

end Hold

/-! ## 3. The hold is the limit of every ramp -/

section Ramp

open Holonics.HNN.LatticeWord (rowNorm)

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- [proved-derived; formal-checked] One sub-tick moves the momentum by at most `s κ U`. -/
theorem ramp_momentum_step {s U κ : ℚ} (hs : 0 ≤ s) (hU : 0 ≤ U) (K : Matrix n n ℚ)
    (hK : rowNorm K ≤ κ) {u₀ u₁ π₀ π₁ : n → ℚ}
    (hmom : π₁ - π₀ = -(s / 2) • (K *ᵥ (u₀ + u₁)))
    (hu₀ : ∀ i, |u₀ i| ≤ U) (hu₁ : ∀ i, |u₁ i| ≤ U) (i : n) :
    |π₁ i - π₀ i| ≤ s * κ * U := by
  have hv : ∀ j, |(u₀ + u₁) j| ≤ 2 * U := fun j => by
    simp only [Pi.add_apply]
    linarith [abs_add_le (u₀ j) (u₁ j), hu₀ j, hu₁ j]
  have hb := abs_mulVec_le_rowNorm K (u₀ + u₁) (by linarith) hv i
  have e : π₁ i - π₀ i = -(s / 2) * (K *ᵥ (u₀ + u₁)) i := by
    rw [← Pi.sub_apply, hmom]; rfl
  rw [e, abs_mul, abs_neg, abs_of_nonneg (by linarith : 0 ≤ s / 2)]
  have hK2 : rowNorm K * (2 * U) ≤ κ * (2 * U) := mul_le_mul_of_nonneg_right hK (by linarith)
  nlinarith

/-- [proved-derived; formal-checked] One sub-tick moves the position by at most `s γ P`: the
descriptor form `C(u₁ − u₀) = (s/2)(π₀ + π₁)` with a left inverse `X C = 1` is
`u₁ − u₀ = (s/2) X (π₀ + π₁)`. -/
theorem ramp_position_step {s P γ : ℚ} (hs : 0 ≤ s) (hP : 0 ≤ P) (C X : Matrix n n ℚ)
    (hX : X * C = 1) (hXb : rowNorm X ≤ γ) {u₀ u₁ π₀ π₁ : n → ℚ}
    (hpos : C *ᵥ (u₁ - u₀) = (s / 2) • (π₀ + π₁))
    (hπ₀ : ∀ i, |π₀ i| ≤ P) (hπ₁ : ∀ i, |π₁ i| ≤ P) (i : n) :
    |u₁ i - u₀ i| ≤ s * γ * P := by
  have hv : ∀ j, |(π₀ + π₁) j| ≤ 2 * P := fun j => by
    simp only [Pi.add_apply]
    linarith [abs_add_le (π₀ j) (π₁ j), hπ₀ j, hπ₁ j]
  have hb := abs_mulVec_le_rowNorm X (π₀ + π₁) (by linarith) hv i
  have hsolve : u₁ - u₀ = (s / 2) • (X *ᵥ (π₀ + π₁)) := by
    rw [← mulVec_smul, ← hpos, mulVec_mulVec, hX, one_mulVec]
  have e : u₁ i - u₀ i = (s / 2) * (X *ᵥ (π₀ + π₁)) i := by
    rw [← Pi.sub_apply, hsolve]; rfl
  rw [e, abs_mul, abs_of_nonneg (by linarith : 0 ≤ s / 2)]
  have hX2 : rowNorm X * (2 * P) ≤ γ * (2 * P) := mul_le_mul_of_nonneg_right hXb (by linarith)
  nlinarith

/-- [proved-derived; formal-checked] **The ramp moves `(u, π)` by at most the ramp time's
bounds.** Over `m` sub-ticks of step `s`, each the midpoint law on `(u, π)` with its own
`(C_j, K_j)` and left inverse `X_j`, with the state within `U`, `P` and the parameters within
`‖K_j‖∞ ≤ κ`, `‖X_j‖∞ ≤ γ`: every coordinate satisfies `|π_m − π_0| ≤ m s κ U` and
`|u_m − u_0| ≤ m s γ P`, uniformly in the parameters' jump. -/
theorem ramp_moves_by_at_most (m : ℕ) {s U P κ γ : ℚ} (hs : 0 ≤ s) (hU : 0 ≤ U) (hP : 0 ≤ P)
    (u π : ℕ → n → ℚ) (C K X : ℕ → Matrix n n ℚ)
    (hpos : ∀ j < m, C j *ᵥ (u (j + 1) - u j) = (s / 2) • (π j + π (j + 1)))
    (hmom : ∀ j < m, π (j + 1) - π j = -(s / 2) • (K j *ᵥ (u j + u (j + 1))))
    (hX : ∀ j < m, X j * C j = 1)
    (hKb : ∀ j < m, rowNorm (K j) ≤ κ) (hXb : ∀ j < m, rowNorm (X j) ≤ γ)
    (hub : ∀ j ≤ m, ∀ i, |u j i| ≤ U) (hπb : ∀ j ≤ m, ∀ i, |π j i| ≤ P) (i : n) :
    |π m i - π 0 i| ≤ m * s * κ * U ∧ |u m i - u 0 i| ≤ m * s * γ * P := by
  have key : ∀ k ≤ m, |π k i - π 0 i| ≤ k * s * κ * U ∧ |u k i - u 0 i| ≤ k * s * γ * P := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      obtain ⟨ihπ, ihu⟩ := ih (by omega)
      have hj : k < m := by omega
      have sπ := ramp_momentum_step hs hU (K k) (hKb k hj) (hmom k hj) (hub k (by omega))
        (hub (k + 1) hk) i
      have su := ramp_position_step hs hP (C k) (X k) (hX k hj) (hXb k hj) (hpos k hj)
        (hπb k (by omega)) (hπb (k + 1) hk) i
      push_cast
      constructor
      · calc |π (k + 1) i - π 0 i| = |(π (k + 1) i - π k i) + (π k i - π 0 i)| := by ring_nf
          _ ≤ |π (k + 1) i - π k i| + |π k i - π 0 i| := abs_add_le _ _
          _ ≤ s * κ * U + k * s * κ * U := add_le_add sπ ihπ
          _ = (k + 1) * s * κ * U := by ring
      · calc |u (k + 1) i - u 0 i| = |(u (k + 1) i - u k i) + (u k i - u 0 i)| := by ring_nf
          _ ≤ |u (k + 1) i - u k i| + |u k i - u 0 i| := abs_add_le _ _
          _ ≤ s * γ * P + k * s * γ * P := add_le_add su ihu
          _ = (k + 1) * s * γ * P := by ring
  exact key m le_rfl

/-- [proved-derived; formal-checked] **The rate after the ramp is the held-momentum rate, up to the
ramp time.** With the end's left inverse `X_m` (`‖X_m‖∞ ≤ γ`), the rate `X_m π_m` is within
`γ · m s κ U` of `X_m π_0`, the rate that holds the momentum at the new mass. -/
theorem ramp_rate_near_held (m : ℕ) {s U P κ γ : ℚ} (hs : 0 ≤ s) (hU : 0 ≤ U) (hP : 0 ≤ P)
    (hκ : 0 ≤ κ) (u π : ℕ → n → ℚ) (C K X : ℕ → Matrix n n ℚ)
    (hpos : ∀ j < m, C j *ᵥ (u (j + 1) - u j) = (s / 2) • (π j + π (j + 1)))
    (hmom : ∀ j < m, π (j + 1) - π j = -(s / 2) • (K j *ᵥ (u j + u (j + 1))))
    (hX : ∀ j < m, X j * C j = 1)
    (hKb : ∀ j < m, rowNorm (K j) ≤ κ) (hXb : ∀ j < m, rowNorm (X j) ≤ γ)
    (hub : ∀ j ≤ m, ∀ i, |u j i| ≤ U) (hπb : ∀ j ≤ m, ∀ i, |π j i| ≤ P)
    (Xm : Matrix n n ℚ) (hXm : rowNorm Xm ≤ γ) (i : n) :
    |(Xm *ᵥ π m) i - (Xm *ᵥ π 0) i| ≤ γ * (m * s * κ * U) := by
  have hd : ∀ j, |(π m - π 0) j| ≤ m * s * κ * U := fun j =>
    (ramp_moves_by_at_most m hs hU hP u π C K X hpos hmom hX hKb hXb hub hπb j).1
  have hc : 0 ≤ (m : ℚ) * s * κ * U := by positivity
  have hb := abs_mulVec_le_rowNorm Xm (π m - π 0) hc hd i
  rw [mulVec_sub] at hb
  calc |(Xm *ᵥ π m) i - (Xm *ᵥ π 0) i| = |(Xm *ᵥ π m - Xm *ᵥ π 0) i| := rfl
    _ ≤ rowNorm Xm * (m * s * κ * U) := hb
    _ ≤ γ * (m * s * κ * U) := mul_le_mul_of_nonneg_right hXm hc

end Ramp

/-! ## 4. The source mass is the imposed storage's inertia, less the prior -/

section Imposed

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {m n ι : Type*} [Fintype m] [Fintype n] [Fintype ι]

/-- [definition] **The carried Gram** `H = H₀ + Σ_t w_t f_t f_tᵀ`: the prior and every return's
weighted feature (`hnn::constitution::NormalLaw::prepare`, `ΔH = Σ w f fᵀ`). -/
def gram (H₀ : Matrix n n K) (w : ι → K) (f : ι → n → K) : Matrix n n K :=
  H₀ + ∑ t, w t • vecMulVec (f t) (f t)

/-- [definition] **The move's kinetic reading** `½⟨ΔE H, ΔE⟩`, row by row. -/
def kinetic (H : Matrix n n K) (V : Matrix m n K) : K :=
  (1 / 2) * ∑ r, V r ⬝ᵥ (H *ᵥ V r)

/-- [definition] **The storage the map imposes on the returns' features**,
`S(E) = Σ_t (w_t/2) |E f_t|²`. -/
def imposedStorage (w : ι → K) (f : ι → n → K) (E : Matrix m n K) : K :=
  ∑ t, w t / 2 * ((E *ᵥ f t) ⬝ᵥ (E *ᵥ f t))

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- `|V f|² = Σ_r (f · V_r)²`, row by row. -/
theorem mulVec_dot_self (V : Matrix m n K) (a : n → K) :
    (V *ᵥ a) ⬝ᵥ (V *ᵥ a) = ∑ r, (a ⬝ᵥ V r) * (a ⬝ᵥ V r) := by
  simp only [dotProduct, mulVec]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [mul_comm (V r _)]

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- [proved-derived; formal-checked] **The kinetic reading is the prior's plus the imposed
storage's**: `½⟨ΔE H, ΔE⟩ = ½⟨ΔE H₀, ΔE⟩ + S(ΔE)`. -/
theorem kinetic_gram (H₀ : Matrix n n K) (w : ι → K) (f : ι → n → K) (V : Matrix m n K) :
    kinetic (gram H₀ w f) V = kinetic H₀ V + imposedStorage w f V := by
  have hrow : ∀ r, V r ⬝ᵥ (gram H₀ w f *ᵥ V r) =
      V r ⬝ᵥ (H₀ *ᵥ V r) + ∑ t, w t * ((f t ⬝ᵥ V r) * (f t ⬝ᵥ V r)) := by
    intro r
    simp only [gram, add_mulVec, sum_mulVec, smul_mulVec, vecMulVec_mulVec, dotProduct_add,
      dotProduct_sum, dotProduct_smul, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op]
    congr 1
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [dotProduct_comm (V r) (f t)]
  simp only [kinetic, imposedStorage, hrow, Finset.sum_add_distrib, mul_add, mulVec_dot_self]
  congr 1
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun r _ => ?_
  ring

/-- [proved-derived; formal-checked] **The imposed storage's change along a move**:
`S(E + ΔE) = S(E) + Σ_t w_t ⟨E f_t, ΔE f_t⟩ + S(ΔE)`. -/
theorem imposed_storage_expand (w : ι → K) (f : ι → n → K) (E V : Matrix m n K) :
    imposedStorage w f (E + V) =
      imposedStorage w f E + ∑ t, w t * ((E *ᵥ f t) ⬝ᵥ (V *ᵥ f t)) + imposedStorage w f V := by
  simp only [imposedStorage, add_mulVec, dotProduct_add, add_dotProduct, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [dotProduct_comm (V *ᵥ f t) (E *ᵥ f t)]
  ring

/-- [proved-derived; formal-checked] **The kinetic reading is the prior's plus the imposed
storage's second-order change**: `½⟨ΔE H, ΔE⟩ = ½⟨ΔE H₀, ΔE⟩ + (S(E + ΔE) − S(E) − DS(E)·ΔE)`. -/
theorem kinetic_is_imposed_curvature (H₀ : Matrix n n K) (w : ι → K) (f : ι → n → K)
    (E V : Matrix m n K) :
    kinetic (gram H₀ w f) V = kinetic H₀ V +
      (imposedStorage w f (E + V) - imposedStorage w f E -
        ∑ t, w t * ((E *ᵥ f t) ⬝ᵥ (V *ᵥ f t))) := by
  rw [kinetic_gram, imposed_storage_expand]
  ring

/-- [proved-derived; formal-checked] **Along a line the imposed storage is a quadratic** whose
power at `τ` is `Σ_t w_t ⟨(E + τV) f_t, V f_t⟩` and whose curvature is `2 S(V)`:
`S(E + τV) = S(E) + τ Σ_t w_t ⟨E f_t, V f_t⟩ + τ² S(V)`. -/
theorem imposed_storage_along_line (w : ι → K) (f : ι → n → K) (E V : Matrix m n K) (τ : K) :
    imposedStorage w f (E + τ • V) =
      imposedStorage w f E + τ * ∑ t, w t * ((E *ᵥ f t) ⬝ᵥ (V *ᵥ f t)) +
        τ ^ 2 * imposedStorage w f V := by
  rw [imposed_storage_expand]
  simp only [imposedStorage, smul_mulVec, dotProduct_smul, smul_dotProduct, smul_eq_mul,
    Finset.mul_sum]
  congr 1
  · congr 1
    refine Finset.sum_congr rfl fun t _ => ?_
    ring
  · refine Finset.sum_congr rfl fun t _ => ?_
    ring

/-- [proved-derived; formal-checked] **The prior's reading is no imposed storage.** Under a
positive prior `H₀ = c I`, every nonzero move reads `½⟨ΔE H₀, ΔE⟩ > 0`; so `½⟨ΔE H, ΔE⟩` exceeds the
imposed storage `S(ΔE)` for every nonzero move, and the identity holds for `H − H₀`. -/
theorem prior_reading_pos [DecidableEq n] {c : K} (hc : 0 < c) {V : Matrix m n K} (hV : V ≠ 0) :
    0 < kinetic (c • (1 : Matrix n n K)) V := by
  obtain ⟨r, i, hri⟩ : ∃ r i, V r i ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hV (Matrix.ext hall)
  have hrow : ∀ r', V r' ⬝ᵥ ((c • (1 : Matrix n n K)) *ᵥ V r') = c * ∑ j, V r' j * V r' j := by
    intro r'
    rw [smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul]
    rfl
  have hsq : ∀ r', 0 ≤ ∑ j, V r' j * V r' j := fun r' =>
    Finset.sum_nonneg fun j _ => mul_self_nonneg _
  have hpos : 0 < ∑ j, V r j * V r j :=
    lt_of_lt_of_le (mul_self_pos.mpr hri)
      (Finset.single_le_sum (fun j _ => mul_self_nonneg (V r j)) (Finset.mem_univ i))
  unfold kinetic
  simp only [hrow]
  have hsum : 0 < ∑ r', c * ∑ j, V r' j * V r' j :=
    lt_of_lt_of_le (mul_pos hc hpos)
      (Finset.single_le_sum (fun r' _ => mul_nonneg hc.le (hsq r')) (Finset.mem_univ r))
  positivity

/-- [proved-derived; formal-checked] **The literal reading fails under the prior**: for `c > 0` and
every nonzero move, `½⟨ΔE H, ΔE⟩ ≠ S(ΔE)` with `H = c I + Σ_t w_t f_t f_tᵀ`. -/
theorem kinetic_ne_imposed [DecidableEq n] {c : K} (hc : 0 < c) (w : ι → K) (f : ι → n → K)
    {V : Matrix m n K} (hV : V ≠ 0) :
    kinetic (gram (c • (1 : Matrix n n K)) w f) V ≠ imposedStorage w f V := by
  rw [kinetic_gram]
  have := prior_reading_pos (m := m) hc hV
  intro h
  linarith

end Imposed

section Audit

#print axioms tick_canonical_position
#print axioms tick_canonical_momentum
#print axioms tick_reads_momentum
#print axioms hold_energy
#print axioms reception_hold_balance
#print axioms closed_reception_hold_balance
#print axioms ramp_moves_by_at_most
#print axioms ramp_rate_near_held
#print axioms kinetic_gram
#print axioms imposed_storage_expand
#print axioms kinetic_is_imposed_curvature
#print axioms imposed_storage_along_line
#print axioms prior_reading_pos
#print axioms kinetic_ne_imposed

end Audit

end Holonics.HNN.DepositHold
