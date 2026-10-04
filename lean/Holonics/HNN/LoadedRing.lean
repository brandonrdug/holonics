import Holonics.HNN.Ring
import Holonics.HNN.TickFamily
import Holonics.HNN.CarriedMotion

/-!
# HNN.LoadedRing: the resonator's operand on the loaded ring's element edge `g → g`

[definition] #62 (5975321323, item 2, the locus `Resonator(g)`; `HNN/TickFamily`'s [open]). A
declared resonator sits on its ring's element port. Inside a word the junction sends the ring's
storage wave and contrast to the element; its output `e` drives the resonator, which returns
`s′ = e − (2/Y) ω` as the ring's next storage (`hnn::word`, "The loaded field balance";
`hnn::ring::ResonatorOperands::step`). Under the exact law (no lattice split), one tick at pump
phase `j` is

```text
r = 2C w + h e − h K_j u ,   ω = M_j⁻¹ r ,   M_j = 2C + (h/Y) I + h D + (h²/2) K_j
(u, w) ↦ (u + h ω, 2ω − w) ,   s′ = e − (2/Y) ω
j = t mod P at the field's elapsed tick t       (ResonatorOperands::phase_at, a schedule's period P)
```

Everything the element edge reads is the ring's own block (its storage, its arrivals and the
resonator's state), so the resonator is an operand of the edge `g → g` alone, and the pump moves
that edge with the tick.

[proved-derived; formal-checked] What is proved.

1. **The tick is one linear operand** (`rateMap`, `stepMap`, `stepMap_apply`,
   `resonator_rate_solves`): `((u, w), e) ↦ ((u + hω, 2ω − w), s′)` is a continuous linear map for
   any executed solve `M_j⁻¹`, and at a right inverse of `M_j` the rate solves the ring's
   one-port equation.
2. **Its exact balance** (`resonator_tick_balance`; `ResonatorStep::closes` with zero chart and
   split): `E_(K_j)(u′, w′) − E_(K_prev)(u, w) = ½⟨u, (K_j − K_prev) u⟩ + (hY/4)(|e|² − |s′|²) −
   h⟨ω, D ω⟩`, the pump's storage change, the port work and the dissipation, each stated
   (`HNN/Ring.ring_tick_executed_energy_balance` at its solve).
3. **The word's balance telescopes** (`resonance`, `resonance_word_balance`;
   `hnn::word::ResonatorBalance::{of, closes}`). Opened at the field's tick `τ`, the energy before
   tick `t` is read at the stiffness of phase `(t − 1) mod P` and after it at phase `t mod P`, where
   `t − 1` stops at zero as the Rust's `previous` does at tick zero; so after `n` ticks
   `E_end − E_open` is the sum of the ticks' pump, port and dissipation terms. On an unpumped ring
   (`P = 1`) every pump term is zero (`stiffAt_one`).
4. **The pump continues across receptions** (`resonance_shift`, `shiftOp_phaseFamily`,
   `phaseFamily_continues`): a word opened at `τ` and run `s + n` ticks is the word opened at
   `τ + s` on the state the first `s` ticks left, for the resonator and for any block family
   `k ↦ A_((τ + k) mod P)` (`phaseFamily`). **One period is the monodromy**
   (`phaseFamily_add_mul`, `trajectoryAt_monodromy`): `n` periods of the word are the `n`-th
   iterate of one period's map, the period being the pump's cycle
   (`HNN/Ring.pump_period_is_cycle`).
5. **The Rust's resonator rule is the self-edge's diamond** (`resonatorRule_iff`,
   `resonator_release_past_diamond`, `resonator_continuing_iff`, `resonator_release_on_walk`).
   `Diamond::retains(Resonator(g))` is `element(g)`, `r_g + 1 + o_g ≤ e_last`, which is
   `InDiamond` of the edge `g → g`. A pumped family moves only on loaded diagonals
   (`MovesOnLoaded`, `sparse_of_movesOnLoaded`). Two constitutions whose static operators agree on
   the diamond and whose resonators agree where the rule retains them give every admitted reading
   at every epoch `t ≤ e_last` the same value, at every pump phase; at the continuing diamond
   (`e_last = 2|B|`) the rule is the walk through `g`, and the readings agree with no bound on the
   word's length.
6. **The resonator's motion release** (`resonator_motion_release_agrees`,
   `resonator_release_indistinguishable`; `CarriedMotion`'s resonator paragraph, #310
   `ReceptionCarry::released`).
   A released resonator's ring is not both reached and observing at the continuing diamond, so
   zeroing its state, phase and momentum agrees on every observing block, and together with its
   material release changes no admitted reading of the tick-indexed word.
7. **The loaded edge** (`loadedEdge`, `loadedEdge_apply`, `loadedEdge_balance`): on a ring block
   `X × (E × E)` the edge `g → g` sends `(x, (u, w))` to `(rest x + store s′, (u′, w′))` with drive
   `e = elem x`, where `rest + store ∘ elem` is the unloaded edge; its resonator part closes by 2.

`Word.Medium` carries no resonator: `HNN/TickBlocks` writes the unloaded ring block
`V r × (Port r → V r)`. The loaded block family on the whole medium is `HNN/LoadedMedium`, which
adds the resonator's state to each ring block and loads its element edge by `loadedEdge`. [open]
The resonator's held momentum across a deposit (5975646405 item 2) is a parameter there (`cross`).
The executed split and chart terms of the lattice word are `HNN/Ring`'s and `HNN/LatticeWord`'s,
not restated here.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.HNN.LoadedRing

open Holonics.HNN.Propagation Holonics.HNN.Retention Holonics.HNN.Ring Holonics.HNN.TickFamily
open scoped BigOperators

/-! ## 1. The resonator's tick as one linear operand -/

section Tick

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- [definition] **The resonator's rate** at stiffness `K` through the executed solve `Minv`:
`ω = Minv (2C w + h e − h K u)`, linear in `((u, w), e)`. -/
def rateMap (C K Minv : E →L[ℝ] E) (h : ℝ) : (E × E) × E →L[ℝ] E :=
  Minv.comp ((2 : ℝ) • C.comp ((ContinuousLinearMap.snd ℝ E E).comp
      (ContinuousLinearMap.fst ℝ (E × E) E)) +
    h • ContinuousLinearMap.snd ℝ (E × E) E -
    h • K.comp ((ContinuousLinearMap.fst ℝ E E).comp (ContinuousLinearMap.fst ℝ (E × E) E)))

theorem rateMap_apply (C K Minv : E →L[ℝ] E) (h : ℝ) (u w e : E) :
    rateMap C K Minv h ((u, w), e) = Minv (ringRight C K h u w e) := by
  simp [rateMap, ringRight]

/-- [definition] **One resonator tick**: `((u, w), e) ↦ ((u + hω, 2ω − w), e − (2/Y) ω)`, the new
state and the returned storage wave (`ResonatorOperands::step` under the exact law). -/
def stepMap (C K Minv : E →L[ℝ] E) (Y h : ℝ) : (E × E) × E →L[ℝ] (E × E) × E :=
  (((ContinuousLinearMap.fst ℝ E E).comp (ContinuousLinearMap.fst ℝ (E × E) E) +
        h • rateMap C K Minv h).prod
      ((2 : ℝ) • rateMap C K Minv h -
        (ContinuousLinearMap.snd ℝ E E).comp (ContinuousLinearMap.fst ℝ (E × E) E))).prod
    (ContinuousLinearMap.snd ℝ (E × E) E - (2 / Y) • rateMap C K Minv h)

theorem stepMap_apply (C K Minv : E →L[ℝ] E) (Y h : ℝ) (u w e : E) :
    stepMap C K Minv Y h ((u, w), e) =
      ((u + h • Minv (ringRight C K h u w e), (2 : ℝ) • Minv (ringRight C K h u w e) - w),
        ringOut Y e (Minv (ringRight C K h u w e))) := by
  simp [stepMap, rateMap_apply, ringOut]

/-- [proved-derived; formal-checked] At a right inverse of `M = ringOperator C D K Y h` the rate
solves the ring's one-port equation `M ω = r`. -/
theorem resonator_rate_solves (C D K Minv : E →L[ℝ] E) {Y h : ℝ}
    (hM : ∀ v, ringOperator C D K Y h (Minv v) = v) (u w e : E) :
    ringOperator C D K Y h (rateMap C K Minv h ((u, w), e)) = ringRight C K h u w e := by
  rw [rateMap_apply, hM]

/-- [proved-derived; formal-checked] **The resonator tick's exact balance** (`ResonatorStep::closes`
with zero chart and split). The energy before is read at the previous phase's stiffness `K`, after
at this phase's `K′`: `E_(K′)(u′, w′) − E_K(u, w) = ½⟨u, (K′ − K) u⟩ + (hY/4)(|e|² − |s′|²) −
h⟨ω, D ω⟩`. -/
theorem resonator_tick_balance (C D K K' Minv : E →L[ℝ] E)
    (hC : ∀ x y, inner ℝ (C x) y = inner ℝ x (C y))
    (hK' : ∀ x y, inner ℝ (K' x) y = inner ℝ x (K' y)) {Y h : ℝ} (hY : Y ≠ 0)
    (hM : ∀ v, ringOperator C D K' Y h (Minv v) = v) (p : E × E) (e : E) :
    contactEnergy C K' (stepMap C K' Minv Y h (p, e)).1.1 (stepMap C K' Minv Y h (p, e)).1.2 -
        contactEnergy C K p.1 p.2 =
      (1 / 2 : ℝ) * inner ℝ p.1 ((K' - K) p.1) +
        h * Y / 4 * (‖e‖ ^ 2 - ‖(stepMap C K' Minv Y h (p, e)).2‖ ^ 2) -
        h * inner ℝ (Minv (ringRight C K' h p.1 p.2 e))
          (D (Minv (ringRight C K' h p.1 p.2 e))) := by
  obtain ⟨u, w⟩ := p
  set ω := Minv (ringRight C K' h u w e) with hω
  have hb := ring_tick_executed_energy_balance C D K K' hC hK' (h := h) hY u w e ω (u + h • ω)
    ((2 : ℝ) • ω - w)
  rw [stepMap_apply]
  simp only [← hω]
  rw [hb, hω, hM, sub_self, inner_zero_right, sub_self]
  ring

end Tick

/-! ## 2. The word's resonance: the pump's phase and the telescoped balance -/

section Word

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- [definition] **The pump phase at the field's tick `t`**: `t mod P`
(`ResonatorOperands::phase_at`; a declared pump's clock reads the same torus point). -/
def phaseAt (P t : ℕ) : ℕ := t % P

theorem phaseAt_add_mul (P t n : ℕ) : phaseAt P (t + n * P) = phaseAt P t :=
  Nat.add_mul_mod_self_right t n P

theorem phaseAt_lt {P : ℕ} (hP : 0 < P) (t : ℕ) : phaseAt P t < P := Nat.mod_lt _ hP

/-- [definition] The stiffness at the field's tick `t`: the phase's `K_j`. -/
def stiffAt (Kp : ℕ → E →L[ℝ] E) (P t : ℕ) : E →L[ℝ] E := Kp (phaseAt P t)

/-- An unpumped ring has the one phase. -/
theorem stiffAt_one (Kp : ℕ → E →L[ℝ] E) (t : ℕ) : stiffAt Kp 1 t = Kp 0 := by
  rw [stiffAt, phaseAt, Nat.mod_one]

/-- [definition] **The resonator's states over a word** opened at the field's tick `τ` on `x₀`,
driven by the element outputs `e k`. -/
def resonance (C : E →L[ℝ] E) (Kp Minvp : ℕ → E →L[ℝ] E) (Y h : ℝ) (P τ : ℕ) (e : ℕ → E)
    (x₀ : E × E) : ℕ → E × E
  | 0 => x₀
  | k + 1 => (stepMap C (Kp (phaseAt P (τ + k))) (Minvp (phaseAt P (τ + k))) Y h
      (resonance C Kp Minvp Y h P τ e x₀ k, e k)).1

/-- [definition] The rate of the word's tick `k`. -/
def resonanceRate (C : E →L[ℝ] E) (Kp Minvp : ℕ → E →L[ℝ] E) (Y h : ℝ) (P τ : ℕ) (e : ℕ → E)
    (x₀ : E × E) (k : ℕ) : E :=
  Minvp (phaseAt P (τ + k)) (ringRight C (Kp (phaseAt P (τ + k))) h
    (resonance C Kp Minvp Y h P τ e x₀ k).1 (resonance C Kp Minvp Y h P τ e x₀ k).2 (e k))

/-- [definition] The storage wave the word's tick `k` returns, `s′_k = e_k − (2/Y) ω_k`. -/
def resonanceOut (C : E →L[ℝ] E) (Kp Minvp : ℕ → E →L[ℝ] E) (Y h : ℝ) (P τ : ℕ) (e : ℕ → E)
    (x₀ : E × E) (k : ℕ) : E :=
  (stepMap C (Kp (phaseAt P (τ + k))) (Minvp (phaseAt P (τ + k))) Y h
    (resonance C Kp Minvp Y h P τ e x₀ k, e k)).2

/-- [proved-derived; formal-checked] **The pump continues across receptions**: a word opened at `τ`
and run `s + n` ticks is the word opened at `τ + s` on the state the first `s` ticks left, driven by
the later outputs. -/
theorem resonance_shift (C : E →L[ℝ] E) (Kp Minvp : ℕ → E →L[ℝ] E) (Y h : ℝ) (P τ : ℕ)
    (e : ℕ → E) (x₀ : E × E) (s n : ℕ) :
    resonance C Kp Minvp Y h P τ e x₀ (s + n) =
      resonance C Kp Minvp Y h P (τ + s) (fun k => e (s + k))
        (resonance C Kp Minvp Y h P τ e x₀ s) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (stepMap C (Kp (phaseAt P (τ + (s + n)))) (Minvp (phaseAt P (τ + (s + n)))) Y h
        (resonance C Kp Minvp Y h P τ e x₀ (s + n), e (s + n))).1 =
      (stepMap C (Kp (phaseAt P (τ + s + n))) (Minvp (phaseAt P (τ + s + n))) Y h
        (resonance C Kp Minvp Y h P (τ + s) (fun k => e (s + k))
          (resonance C Kp Minvp Y h P τ e x₀ s) n, e (s + n))).1
    rw [ih, Nat.add_assoc]

/-- [proved-derived; formal-checked] **The word's resonator balance telescopes**
(`ResonatorBalance::{of, closes}` under the exact law). Opened at the field's tick `τ`, the open
energy is read at the phase of `τ − 1` (at `τ = 0`, its own: the Rust's `previous`) and the end
energy at the phase of the last tick; their difference is the sum of every tick's pump, port and
dissipation terms. -/
theorem resonance_word_balance (C D : E →L[ℝ] E) (Kp Minvp : ℕ → E →L[ℝ] E)
    (hC : ∀ x y, inner ℝ (C x) y = inner ℝ x (C y))
    (hK : ∀ j x y, inner ℝ (Kp j x) y = inner ℝ x (Kp j y)) {Y h : ℝ} (hY : Y ≠ 0)
    (hM : ∀ j v, ringOperator C D (Kp j) Y h (Minvp j v) = v) (P τ : ℕ) (e : ℕ → E)
    (x₀ : E × E) (n : ℕ) :
    contactEnergy C (stiffAt Kp P (τ + n - 1)) (resonance C Kp Minvp Y h P τ e x₀ n).1
        (resonance C Kp Minvp Y h P τ e x₀ n).2 -
        contactEnergy C (stiffAt Kp P (τ - 1)) x₀.1 x₀.2 =
      ∑ k ∈ Finset.range n,
        ((1 / 2 : ℝ) * inner ℝ (resonance C Kp Minvp Y h P τ e x₀ k).1
            ((stiffAt Kp P (τ + k) - stiffAt Kp P (τ + k - 1))
              (resonance C Kp Minvp Y h P τ e x₀ k).1) +
          h * Y / 4 * (‖e k‖ ^ 2 - ‖resonanceOut C Kp Minvp Y h P τ e x₀ k‖ ^ 2) -
          h * inner ℝ (resonanceRate C Kp Minvp Y h P τ e x₀ k)
            (D (resonanceRate C Kp Minvp Y h P τ e x₀ k))) := by
  induction n with
  | zero =>
    simp only [Finset.sum_range_zero, Nat.add_zero]
    exact sub_self _
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih, show τ + (n + 1) - 1 = τ + n by omega]
    have ht := resonator_tick_balance C D (stiffAt Kp P (τ + n - 1)) (Kp (phaseAt P (τ + n)))
      (Minvp (phaseAt P (τ + n))) hC (hK _) hY (hM _) (resonance C Kp Minvp Y h P τ e x₀ n) (e n)
    change contactEnergy C (stiffAt Kp P (τ + n))
        (stepMap C (Kp (phaseAt P (τ + n))) (Minvp (phaseAt P (τ + n))) Y h
          (resonance C Kp Minvp Y h P τ e x₀ n, e n)).1.1
        (stepMap C (Kp (phaseAt P (τ + n))) (Minvp (phaseAt P (τ + n))) Y h
          (resonance C Kp Minvp Y h P τ e x₀ n, e n)).1.2 - _ = _
    simp only [resonanceOut, resonanceRate, stiffAt] at ht ⊢
    linear_combination ht

end Word

/-! ## 3. A phase family of block operators: continuation and monodromy -/

section Family

variable {B : Type*} [Fintype B] {adj : B → B → Prop}
variable {K : Type*} [Field K] {M : B → Type*} [∀ b, AddCommGroup (M b)] [∀ b, Module K (M b)]

/-- [definition] **The word opened at the field's tick `τ`** under a pump of period `P`: tick `k`
runs the operator of phase `(τ + k) mod P`. -/
def phaseFamily (A : ℕ → BlockOp K M) (P τ : ℕ) : ℕ → BlockOp K M := fun k => A ((τ + k) % P)

omit [Fintype B] in
/-- [proved-derived; formal-checked] The family read from tick `s` on is the word opened at
`τ + s`. -/
theorem shiftOp_phaseFamily (A : ℕ → BlockOp K M) (P τ s : ℕ) :
    shiftOp (phaseFamily A P τ) s = phaseFamily A P (τ + s) := by
  funext k
  simp [shiftOp, phaseFamily, Nat.add_assoc]

/-- [proved-derived; formal-checked] **The pump continues across receptions**: running `s + n`
ticks from `τ` is running `n` ticks of the word opened at `τ + s` on the state the first `s`
left. -/
theorem phaseFamily_continues (A : ℕ → BlockOp K M) (P τ : ℕ) (x : (b : B) → M b) (s n : ℕ) :
    trajectoryAt (phaseFamily A P τ) x (s + n) =
      trajectoryAt (phaseFamily A P (τ + s)) (trajectoryAt (phaseFamily A P τ) x s) n := by
  rw [← shiftOp_phaseFamily, trajectoryAt_shift]

omit [Fintype B] in
/-- [proved-derived; formal-checked] Whole periods do not move the phase. -/
theorem phaseFamily_add_mul (A : ℕ → BlockOp K M) (P τ n : ℕ) :
    phaseFamily A P (τ + n * P) = phaseFamily A P τ := by
  funext k
  simp only [phaseFamily]
  rw [show τ + n * P + k = τ + k + n * P by ring, Nat.add_mul_mod_self_right]

/-- [proved-derived; formal-checked] **One period is the monodromy**: `n` periods of the word are
the `n`-th iterate of one period's map. -/
theorem trajectoryAt_monodromy (A : ℕ → BlockOp K M) (P τ : ℕ) (x : (b : B) → M b) (n : ℕ) :
    trajectoryAt (phaseFamily A P τ) x (n * P) =
      (fun y => trajectoryAt (phaseFamily A P τ) y P)^[n] x := by
  induction n with
  | zero => simp [trajectoryAt]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ← ih, add_mul, one_mul, phaseFamily_continues,
      phaseFamily_add_mul]

omit [Fintype B] in
theorem phaseFamily_sparse {A : ℕ → BlockOp K M} (hA : ∀ j, Sparse adj (A j)) (P τ k : ℕ) :
    Sparse adj (phaseFamily A P τ k) :=
  hA _

/-! ## 4. The resonator's rule is the self-edge's diamond -/

/-- [definition] **A pumped family moves only on the loaded rings' element edges**: off the
diagonal `g → g` of the loaded set `L` every phase runs the static operator `A₀`. -/
def MovesOnLoaded (A : ℕ → BlockOp K M) (A₀ : BlockOp K M) (L : Set B) : Prop :=
  ∀ j y z, ¬ (y = z ∧ y ∈ L) → A j y z = A₀ y z

omit [Fintype B] in
/-- [proved-derived; formal-checked] A family that moves only on loaded diagonals, which are edges
of the block graph, is sparse at every phase. -/
theorem sparse_of_movesOnLoaded {A : ℕ → BlockOp K M} {A₀ : BlockOp K M} {L : Set B}
    (hA₀ : Sparse adj A₀) (hL : ∀ b ∈ L, adj b b) (h : MovesOnLoaded A A₀ L) (j : ℕ) :
    Sparse adj (A j) := by
  intro y z hyz
  by_cases hd : y = z ∧ y ∈ L
  · obtain ⟨rfl, hy⟩ := hd
    exact absurd (hL y hy) hyz
  · rw [h j y z hd]
    exact hA₀ y z hyz

omit [Fintype B] [Field K] [∀ b, AddCommGroup (M b)] [∀ b, Module K (M b)] in
/-- [proved-derived; formal-checked] **The Rust's resonator rule** `Diamond::retains(Resonator(g))
= element(g)`, `r_g + 1 + o_g ≤ e_last`, is the causal diamond of the edge `g → g`. -/
theorem resonatorRule_iff {S R : Set B} {eLast : ℕ} {b : B} :
    InDiamond adj S R eLast b b ↔
      ∃ j m, b ∈ reachWithin adj S j ∧ Observes adj R b m ∧ j + 1 + m ≤ eLast :=
  Iff.rfl

/-- [proved-derived; formal-checked] **Releasing a resonator past its rule changes no admitted
reading.** Two constitutions whose pumped families move only on the loaded diagonals, whose
static operators agree on the diamond and whose resonators agree at every phase where the rule
retains them, give every reading on the receivers the same value at every epoch `t ≤ e_last`, for
the word opened at any tick of any pump period. -/
theorem resonator_release_past_diamond {A A' : ℕ → BlockOp K M} {A₀ A₀' : BlockOp K M}
    {L : Set B} (hA₀ : Sparse adj A₀) (hA₀' : Sparse adj A₀') (hL : ∀ b ∈ L, adj b b)
    (hA : MovesOnLoaded A A₀ L) (hA' : MovesOnLoaded A' A₀' L) {S R : Set B} {eLast t : ℕ}
    (ht : t ≤ eLast) (hstatic : ∀ y z, InDiamond adj S R eLast z y → A₀' y z = A₀ y z)
    (hres : ∀ j b, b ∈ L → InDiamond adj S R eLast b b → A' j b b = A j b b) (P τ : ℕ)
    {x₀ : (b : B) → M b} (hx : SupportedIn x₀ S) {G : (b : B) → Module.Dual K (M b)}
    (hG : SupportedIn G R) :
    pair G (trajectoryAt (phaseFamily A' P τ) x₀ t) =
      pair G (trajectoryAt (phaseFamily A P τ) x₀ t) := by
  refine release_past_diamond_static
    (phaseFamily_sparse (sparse_of_movesOnLoaded hA₀ hL hA) P τ)
    (phaseFamily_sparse (sparse_of_movesOnLoaded hA₀' hL hA') P τ) hx hG ht
    fun k _ y z hd => ?_
  by_cases hyz : y = z ∧ y ∈ L
  · obtain ⟨rfl, hy⟩ := hyz
    exact hres _ y hy hd
  · simp only [phaseFamily]
    rw [hA' _ y z hyz, hA _ y z hyz]
    exact hstatic y z hd

omit [Field K] [∀ b, AddCommGroup (M b)] [∀ b, Module K (M b)] in
/-- [proved-derived; formal-checked] **At the continuing diamond the resonator rule is the walk
through its ring**: `r_g + 1 + o_g ≤ 2|B|` exactly when `g` is reached from a source and observes
a receiver. -/
theorem resonator_continuing_iff (S R : Set B) (b : B) :
    InDiamond adj S R (2 * Fintype.card B) b b ↔ b ∈ reachAll adj S ∧ ObservesAll adj R b :=
  inDiamond_continuing_iff S R b b

/-- [proved-derived; formal-checked] **The walk version**, with no bound on the word's length: two
constitutions whose static operators agree on every walk edge and whose resonators agree on every
ring a walk passes give the same readings at every epoch, from changes on the reached blocks that
agree on the observing ones. -/
theorem resonator_release_on_walk {A A' : ℕ → BlockOp K M} {A₀ A₀' : BlockOp K M}
    {L : Set B} (hA₀ : Sparse adj A₀) (hA₀' : Sparse adj A₀') (hL : ∀ b ∈ L, adj b b)
    (hA : MovesOnLoaded A A₀ L) (hA' : MovesOnLoaded A' A₀' L) {S R : Set B}
    (hstatic : ∀ y z, OnWalk adj S R z y → A₀ y z = A₀' y z)
    (hres : ∀ j b, b ∈ L → OnWalk adj S R b b → A j b b = A' j b b) (P τ : ℕ)
    {x x' : (b : B) → M b} (hx : SupportedIn x (reachAll adj S))
    (hx' : SupportedIn x' (reachAll adj S)) (hxx : ∀ b, ObservesAll adj R b → x b = x' b)
    {G : (b : B) → Module.Dual K (M b)} (hG : SupportedIn G R) (t : ℕ) :
    pair G (trajectoryAt (phaseFamily A P τ) x t) =
      pair G (trajectoryAt (phaseFamily A' P τ) x' t) := by
  refine readings_agree_on_walk
    (phaseFamily_sparse (sparse_of_movesOnLoaded hA₀ hL hA) P τ)
    (phaseFamily_sparse (sparse_of_movesOnLoaded hA₀' hL hA') P τ)
    (fun k y z hw => ?_) hx hx' hxx hG t
  by_cases hyz : y = z ∧ y ∈ L
  · obtain ⟨rfl, hy⟩ := hyz
    exact hres _ y hy hw
  · simp only [phaseFamily]
    rw [hA' _ y z hyz, hA _ y z hyz]
    exact hstatic y z hw

/-! ## 5. The resonator's motion release -/

omit [Field K] [∀ b, AddCommGroup (M b)] [∀ b, Module K (M b)] in
/-- [proved-derived; formal-checked] **A released resonator's ring is off every walk**: at the
continuing diamond a ring the rule releases is not both reached and observing. -/
theorem released_resonator_off_walk {S R : Set B} {b : B}
    (hb : ¬ InDiamond adj S R (2 * Fintype.card B) b b) :
    ¬ (b ∈ reachAll adj S ∧ ObservesAll adj R b) := fun h =>
  hb ((resonator_continuing_iff S R b).mpr h)

omit [Fintype B] in
theorem resonator_motion_release_agrees_of {S R : Set B} {x x' : (b : B) → M b}
    (hx : SupportedIn x (reachAll adj S)) (hx' : SupportedIn x' (reachAll adj S))
    (hmoves : ∀ b, x' b ≠ x b → ¬ (b ∈ reachAll adj S ∧ ObservesAll adj R b)) :
    ∀ b, ObservesAll adj R b → x' b = x b :=
  CarriedMotion.motion_release_agrees hx hx' fun b hr ho => by
    by_contra hne
    exact hmoves b hne ⟨hr, ho⟩

/-- [proved-derived; formal-checked] **The resonator's motion release agrees on every observing
block** (`ReceptionCarry::released`): a release that changes only the blocks of rings whose
resonator the continuing rule releases (their state, phase and momentum zeroed), from and to
changes on the reached blocks, agrees with the carried change on every block that observes a
receiver. -/
theorem resonator_motion_release_agrees {S R : Set B} {x x' : (b : B) → M b}
    (hx : SupportedIn x (reachAll adj S)) (hx' : SupportedIn x' (reachAll adj S))
    (hmoves : ∀ b, x' b ≠ x b → ¬ InDiamond adj S R (2 * Fintype.card B) b b) :
    ∀ b, ObservesAll adj R b → x' b = x b :=
  resonator_motion_release_agrees_of hx hx' fun b hne => released_resonator_off_walk (hmoves b hne)

/-- [proved-derived; formal-checked] **Releasing a resonator's material and motion together is
indistinguishable** for the tick-indexed word: the released constitution (resonators kept only
where the continuing rule keeps them) run from the motion-released change gives every admitted
reading at every epoch the value the kept constitution gives from the carried change, at any pump
phase. -/
theorem resonator_release_indistinguishable {A A' : ℕ → BlockOp K M} {A₀ : BlockOp K M}
    {L : Set B} (hA₀ : Sparse adj A₀) (hL : ∀ b ∈ L, adj b b) (hA : MovesOnLoaded A A₀ L)
    (hA' : MovesOnLoaded A' A₀ L) {S R : Set B}
    (hres : ∀ j b, b ∈ L → InDiamond adj S R (2 * Fintype.card B) b b → A j b b = A' j b b)
    (P τ : ℕ) {x x' : (b : B) → M b} (hx : SupportedIn x (reachAll adj S))
    (hx' : SupportedIn x' (reachAll adj S))
    (hmoves : ∀ b, x' b ≠ x b → ¬ InDiamond adj S R (2 * Fintype.card B) b b)
    {G : (b : B) → Module.Dual K (M b)} (hG : SupportedIn G R) (t : ℕ) :
    pair G (trajectoryAt (phaseFamily A P τ) x t) =
      pair G (trajectoryAt (phaseFamily A' P τ) x' t) :=
  resonator_release_on_walk hA₀ hA₀ hL hA hA' (fun _ _ _ => rfl)
    (fun j b hb hw => hres j b hb ((resonator_continuing_iff S R b).mpr hw)) P τ hx hx'
    (fun b hb => (resonator_motion_release_agrees hx hx' hmoves b hb).symm) hG t

end Family

/-! ## 6. The loaded edge on a ring block -/

section Edge

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {X : Type*} [AddCommGroup X] [Module ℝ X]

/-- [definition] **The loaded ring's element edge `g → g`** on the block `X × (E × E)`: the unloaded
edge is `rest + store ∘ elem`; loaded, the element's output `e = elem x` drives the resonator,
whose returned wave `s′` is stored and whose state moves. -/
def loadedEdge (rest : X →ₗ[ℝ] X) (elem : X →ₗ[ℝ] E) (store : E →ₗ[ℝ] X)
    (C K Minv : E →L[ℝ] E) (Y h : ℝ) : X × (E × E) →ₗ[ℝ] X × (E × E) :=
  (rest ∘ₗ LinearMap.fst ℝ X (E × E) +
      store ∘ₗ (LinearMap.snd ℝ (E × E) E ∘ₗ ((stepMap C K Minv Y h : (E × E) × E →ₗ[ℝ] _) ∘ₗ
        (LinearMap.snd ℝ X (E × E)).prod (elem ∘ₗ LinearMap.fst ℝ X (E × E))))).prod
    (LinearMap.fst ℝ (E × E) E ∘ₗ ((stepMap C K Minv Y h : (E × E) × E →ₗ[ℝ] _) ∘ₗ
      (LinearMap.snd ℝ X (E × E)).prod (elem ∘ₗ LinearMap.fst ℝ X (E × E))))

theorem loadedEdge_apply (rest : X →ₗ[ℝ] X) (elem : X →ₗ[ℝ] E) (store : E →ₗ[ℝ] X)
    (C K Minv : E →L[ℝ] E) (Y h : ℝ) (x : X) (p : E × E) :
    loadedEdge rest elem store C K Minv Y h (x, p) =
      (rest x + store (stepMap C K Minv Y h (p, elem x)).2,
        (stepMap C K Minv Y h (p, elem x)).1) :=
  rfl

/-- [proved-derived; formal-checked] **The loaded edge's resonator closes its balance** with the
element's output as drive: the resonator part of the edge's image is `resonator_tick_balance` at
`e = elem x`. -/
theorem loadedEdge_balance (rest : X →ₗ[ℝ] X) (elem : X →ₗ[ℝ] E) (store : E →ₗ[ℝ] X)
    (C D K K' Minv : E →L[ℝ] E) (hC : ∀ x y, inner ℝ (C x) y = inner ℝ x (C y))
    (hK' : ∀ x y, inner ℝ (K' x) y = inner ℝ x (K' y)) {Y h : ℝ} (hY : Y ≠ 0)
    (hM : ∀ v, ringOperator C D K' Y h (Minv v) = v) (x : X) (p : E × E) :
    contactEnergy C K' (loadedEdge rest elem store C K' Minv Y h (x, p)).2.1
        (loadedEdge rest elem store C K' Minv Y h (x, p)).2.2 - contactEnergy C K p.1 p.2 =
      (1 / 2 : ℝ) * inner ℝ p.1 ((K' - K) p.1) +
        h * Y / 4 * (‖elem x‖ ^ 2 - ‖(stepMap C K' Minv Y h (p, elem x)).2‖ ^ 2) -
        h * inner ℝ (Minv (ringRight C K' h p.1 p.2 (elem x)))
          (D (Minv (ringRight C K' h p.1 p.2 (elem x)))) := by
  rw [loadedEdge_apply]
  exact resonator_tick_balance C D K K' Minv hC hK' hY hM p (elem x)

end Edge

end Holonics.HNN.LoadedRing
