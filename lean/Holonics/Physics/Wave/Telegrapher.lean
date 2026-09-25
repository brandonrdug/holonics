import Mathlib

/-!
# The telegrapher's constitution on a chain of LC cells: a causal cone that loss never widens

[definition] Rebuild step 6, K3 (#74), battle test 2, second half, and the light-is-change record
§1 and §8.1 (local propagation). The field law `εμ ∂²u + σμ ∂u = ∇²u` is carried by a chain of
**LC cells**. Node `i` stores charge on a capacitance `C i` (`ε Δx`) with a leakage conductance
`G i` (`σ Δx`); junction `e` joins nodes `e` and `e + 1` through an inductance `L e` (`μ Δx`).
The **clock** is a tick `h`, staggered: node voltages `V` live at whole ticks, junction currents
`I` at half ticks. One tick (`step`) is

```text
L e (I⁺ e − I e)   = −h (V (e+1) − V e)                                  flow inertia
C i (V⁺ i − V i)   = h (I⁺ (i−1) − I⁺ i + s·[i = 0]) − h G i (V⁺ i + V i)/2   storage, loss, source
```

(`step_is_the_telegrapher`). The leakage is read at the midpoint of the tick, so the node's own
factor is the Cayley map of its decay, `a = (2C − hG)/(2C + hG)` (`loss`), and the update is
explicit: no global solve, one junction and one node at a time. Eliminating `I` gives
`LC ∂²V + LG ∂V = ∂²_x V`, the telegrapher equation, in the continuum limit (not formalized here).
The **supplied operator** is the incidence of the chain; its general finite form, with the energy
balance and the Courant bound, is in `Physics/Wave/Energy`.

[proved-derived; formal-checked] What is proved, exactly over `ℚ`.

1. **Locality.** A state supported in `[lo, hi]` is supported in `[lo − 1, hi + 1]` one tick
   later (`step_supported`); after `n` ticks, in `[lo − n, hi + n]` (`run_cone`). The step is
   linear (`step_sub`, `run_sub`), so **a change moves at most one cell per tick**: two states that
   differ inside `[lo, hi]` differ only inside `[lo − n, hi + n]` after `n` ticks, under any
   source schedule (`change_moves_one_cell_per_tick`). None of these theorems has a hypothesis on
   the material: the lattice cone is one cell per tick for every `C`, `L` and `G`.
2. **The cone is attained.** The front advances exactly one cell per tick: the value at the new
   edge is `gain · coupling` times the value at the old edge (`step_front_right`,
   `step_front_left`), and for positive `C`, `L`, `h` and `G ≥ 0` that factor is never zero
   (`frontFactor_ne_zero`). A unit impulse on a uniform chain reads `(gain · coupling)ⁿ` at
   `±n` after `n` ticks and nothing beyond (`impulse_cone`).
3. **Loss damps but never speeds a signal.** The front factor with leakage is the lossless one
   times the damping ratio `2C/(2C + hG)` (`frontFactor_eq_damping_mul_lossless`), which lies in
   `(0, 1]` and is `1` exactly without leakage (`damping_pos`, `damping_le_one`,
   `damping_eq_one_iff`); a negative leakage amplifies instead (`negative_leakage_amplifies`). So after `n` ticks the impulse front is `(2C/(2C+hG))ⁿ` times the
   lossless front, on the same cone (`impulse_front_damped`). The node's own factor is the Cayley
   image of its decay: `−1 < a ≤ 1`, `a = 1` exactly without leakage (`loss_gt_neg_one`,
   `loss_le_one`, `loss_eq_one_iff`).

The continuum statement that the characteristic cone of `εμ∂² + σμ∂ − ∇²` has speed
`(εμ)^(−½)` for every `σ ≥ 0` is `proved-standard` (its principal symbol `εμτ² − |ξ|²` has no
`σ`; atlas `em.telegrapher-constitution`). The Courant (CFL) condition `h² < LC` is a
stability statement: under it the staggered energy is a norm
(`Physics/Wave/Energy.chain_energy_definite`; in general `energy_lower_bound`, `energy_definite`).
It is not a proof that the physical cone lies inside the lattice cone; that reading of
`h² < LC` as `Δx/√(LC)` against one cell per tick is an interpretation. No `axiom`, no `sorry`.
-/

namespace Holonics.Physics.Wave.Telegrapher

/-! ## 1. The chain, its constitution and its clock -/

/-- [definition] **The constitution of an LC chain**: node capacitance `C` and leakage `G`,
junction inductance `L` (junction `e` joins nodes `e` and `e + 1`). -/
structure Material where
  C : ℤ → ℚ
  G : ℤ → ℚ
  L : ℤ → ℚ

/-- [definition] **A state** at a whole tick: node voltages `V` and the junction currents `I` of
the previous half tick. -/
@[ext] structure State where
  V : ℤ → ℚ
  I : ℤ → ℚ

instance : Zero State := ⟨⟨0, 0⟩⟩
instance : Sub State := ⟨fun x y => ⟨x.V - y.V, x.I - y.I⟩⟩

@[simp] theorem zero_V : (0 : State).V = 0 := rfl
@[simp] theorem zero_I : (0 : State).I = 0 := rfl
@[simp] theorem sub_V (x y : State) : (x - y).V = x.V - y.V := rfl
@[simp] theorem sub_I (x y : State) : (x - y).I = x.I - y.I := rfl

/-- [definition] The node's own factor over one tick: the Cayley map of its decay. -/
def loss (m : Material) (h : ℚ) (i : ℤ) : ℚ := (2 * m.C i - h * m.G i) / (2 * m.C i + h * m.G i)

/-- [definition] The node's response to the net inflow over one tick. -/
def gain (m : Material) (h : ℚ) (i : ℤ) : ℚ := 2 * h / (2 * m.C i + h * m.G i)

/-- [definition] The junction's response to the voltage drop over one tick. -/
def coupling (m : Material) (h : ℚ) (e : ℤ) : ℚ := h / m.L e

/-- [definition] A source current entering node `0`. -/
def inject (s : ℚ) (i : ℤ) : ℚ := if i = 0 then s else 0

/-- [definition] The junction currents after one half tick. -/
def currentStep (m : Material) (h : ℚ) (x : State) (e : ℤ) : ℚ :=
  x.I e - coupling m h e * (x.V (e + 1) - x.V e)

/-- [definition] **One tick of the chain** under source `s`. -/
def step (m : Material) (h s : ℚ) (x : State) : State where
  I := currentStep m h x
  V := fun i => loss m h i * x.V i +
    gain m h i * (currentStep m h x (i - 1) - currentStep m h x i + inject s i)

/-- [definition] **Propagation** under a source schedule: `n` ticks from `x`. -/
def run (m : Material) (h : ℚ) (src : ℕ → ℚ) (x : State) : ℕ → State
  | 0 => x
  | n + 1 => step m h (src n) (run m h src x n)

@[simp] theorem run_zero (m : Material) (h : ℚ) (src : ℕ → ℚ) (x : State) :
    run m h src x 0 = x := rfl

@[simp] theorem run_succ (m : Material) (h : ℚ) (src : ℕ → ℚ) (x : State) (n : ℕ) :
    run m h src x (n + 1) = step m h (src n) (run m h src x n) := rfl

/-- [proved-derived; formal-checked] **The step is the discretized telegrapher law**: flow inertia
on each junction, storage with midpoint leakage and the source on each node. -/
theorem step_is_the_telegrapher (m : Material) (h s : ℚ) (x : State) (i e : ℤ)
    (hden : 2 * m.C i + h * m.G i ≠ 0) (hL : m.L e ≠ 0) :
    m.C i * ((step m h s x).V i - x.V i) =
        h * ((step m h s x).I (i - 1) - (step m h s x).I i + inject s i) -
          h * m.G i * ((step m h s x).V i + x.V i) / 2 ∧
      m.L e * ((step m h s x).I e - x.I e) = -h * (x.V (e + 1) - x.V e) := by
  constructor
  · have hden' : m.C i * 2 + h * m.G i ≠ 0 := by rwa [mul_comm]
    have key : (2 * m.C i + h * m.G i) * (step m h s x).V i =
        (2 * m.C i - h * m.G i) * x.V i + 2 * h *
          ((step m h s x).I (i - 1) - (step m h s x).I i + inject s i) := by
      simp only [step, loss, gain]
      field_simp
    linear_combination (1 / 2 : ℚ) * key
  · simp only [step, currentStep, coupling]
    field_simp
    ring

/-! ## 2. Linearity: the change is itself a motion of the chain -/

theorem inject_sub (s s' : ℚ) (i : ℤ) : inject s i - inject s' i = inject (s - s') i := by
  unfold inject; split_ifs <;> ring

/-- [proved-derived; formal-checked] The step is linear in the state and the source. -/
theorem step_sub (m : Material) (h s s' : ℚ) (x y : State) :
    step m h s x - step m h s' y = step m h (s - s') (x - y) := by
  ext i
  · simp only [sub_V, Pi.sub_apply, step, currentStep, sub_I, ← inject_sub]
    ring
  · simp only [sub_I, Pi.sub_apply, step, currentStep, sub_V]
    ring

/-- [proved-derived; formal-checked] Propagation is linear: the difference of two runs is the run
of the difference under the difference of the sources. -/
theorem run_sub (m : Material) (h : ℚ) (src src' : ℕ → ℚ) (x y : State) (n : ℕ) :
    run m h src x n - run m h src' y n = run m h (src - src') (x - y) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [run_succ, run_succ, run_succ, step_sub, ih]; rfl

/-! ## 3. The causal cone -/

/-- [definition] **Supported in `[lo, hi]`**: every node outside the interval reads zero, and
every junction not joining two nodes of the interval carries no current. -/
def Supported (lo hi : ℤ) (x : State) : Prop :=
  (∀ i, (i < lo ∨ hi < i) → x.V i = 0) ∧ (∀ e, (e < lo ∨ hi ≤ e) → x.I e = 0)

theorem currentStep_supported {m : Material} {h : ℚ} {lo hi : ℤ} {x : State}
    (hx : Supported lo hi x) (e : ℤ) (he : e < lo - 1 ∨ hi + 1 ≤ e) :
    currentStep m h x e = 0 := by
  unfold currentStep
  rcases he with he | he
  · rw [hx.2 e (Or.inl (by omega)), hx.1 (e + 1) (Or.inl (by omega)), hx.1 e (Or.inl (by omega))]
    ring
  · rw [hx.2 e (Or.inr (by omega)), hx.1 (e + 1) (Or.inr (by omega)), hx.1 e (Or.inr (by omega))]
    ring

/-- [proved-derived; formal-checked] **One cell per tick.** A state supported in `[lo, hi]` is
supported in `[lo − 1, hi + 1]` after one tick, when the source node lies in the widened interval
or the source is silent. No hypothesis on the material. -/
theorem step_supported {m : Material} {h s : ℚ} {lo hi : ℤ} {x : State}
    (hx : Supported lo hi x) (hs : s = 0 ∨ (lo ≤ 1 ∧ -1 ≤ hi)) :
    Supported (lo - 1) (hi + 1) (step m h s x) := by
  refine ⟨fun i hi' => ?_, fun e he => currentStep_supported hx e he⟩
  have hinj : inject s i = 0 := by
    unfold inject
    split_ifs with h0
    · rcases hs with hs | hs
      · exact hs
      · omega
    · rfl
  simp only [step]
  rcases hi' with hi' | hi'
  · rw [hx.1 i (Or.inl (by omega)), currentStep_supported hx (i - 1) (Or.inl (by omega)),
      currentStep_supported hx i (Or.inl (by omega)), hinj]
    ring
  · rw [hx.1 i (Or.inr (by omega)), currentStep_supported hx (i - 1) (Or.inr (by omega)),
      currentStep_supported hx i (Or.inr (by omega)), hinj]
    ring

/-- The silent source schedule. -/
def silent : ℕ → ℚ := fun _ => 0

/-- [proved-derived; formal-checked] **The causal cone**: without a source, a state supported in
`[lo, hi]` is supported in `[lo − n, hi + n]` after `n` ticks. -/
theorem run_cone (m : Material) (h : ℚ) {lo hi : ℤ} {x : State} (hx : Supported lo hi x) (n : ℕ) :
    Supported (lo - n) (hi + n) (run m h silent x n) := by
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    rw [run_succ, show lo - ((n + 1 : ℕ) : ℤ) = lo - n - 1 by push_cast; ring,
      show hi + ((n + 1 : ℕ) : ℤ) = hi + n + 1 by push_cast; ring]
    exact step_supported ih (Or.inl rfl)

/-- [proved-derived; formal-checked] **A change moves at most one cell per tick.** Two states
that differ only inside `[lo, hi]` differ only inside `[lo − n, hi + n]` after `n` ticks under the
same source schedule, whatever the material. -/
theorem change_moves_one_cell_per_tick (m : Material) (h : ℚ) (src : ℕ → ℚ) {lo hi : ℤ}
    {x y : State} (hxy : Supported lo hi (x - y)) (n : ℕ) :
    Supported (lo - n) (hi + n) (run m h src x n - run m h src y n) := by
  rw [run_sub]
  have hsrc : src - src = silent := by funext k; simp [silent]
  rw [hsrc]
  exact run_cone m h hxy n

/-! ## 4. The front: the cone is attained, and loss only damps it -/

/-- [definition] The factor by which the front advances one cell. -/
def frontFactor (m : Material) (h : ℚ) (i e : ℤ) : ℚ := gain m h i * coupling m h e

/-- [proved-derived; formal-checked] **The right front advances one cell**: at the new edge the
state reads `gain · coupling` times the old edge. -/
theorem step_front_right {m : Material} {h s : ℚ} {lo hi : ℤ} {x : State}
    (hx : Supported lo hi x) (hhi : 0 ≤ hi) :
    (step m h s x).V (hi + 1) = frontFactor m h (hi + 1) hi * x.V hi := by
  have h1 : currentStep m h x (hi + 1) = 0 := currentStep_supported hx _ (Or.inr le_rfl)
  have h0 : currentStep m h x hi = coupling m h hi * x.V hi := by
    unfold currentStep
    rw [hx.2 hi (Or.inr le_rfl), hx.1 (hi + 1) (Or.inr (by omega))]
    ring
  have hinj : inject s (hi + 1) = 0 := by unfold inject; rw [if_neg (by omega)]
  simp only [step, frontFactor]
  rw [hx.1 (hi + 1) (Or.inr (by omega)), show hi + 1 - 1 = hi by ring, h0, h1, hinj]
  ring

/-- [proved-derived; formal-checked] **The left front advances one cell.** -/
theorem step_front_left {m : Material} {h s : ℚ} {lo hi : ℤ} {x : State}
    (hx : Supported lo hi x) (hlo : lo ≤ 0) :
    (step m h s x).V (lo - 1) = frontFactor m h (lo - 1) (lo - 1) * x.V lo := by
  have h2 : currentStep m h x (lo - 1 - 1) = 0 := currentStep_supported hx _ (Or.inl (by omega))
  have h1 : currentStep m h x (lo - 1) = -(coupling m h (lo - 1) * x.V lo) := by
    unfold currentStep
    rw [hx.2 (lo - 1) (Or.inl (by omega)), hx.1 (lo - 1) (Or.inl (by omega)),
      show lo - 1 + 1 = lo by ring]
    ring
  have hinj : inject s (lo - 1) = 0 := by unfold inject; rw [if_neg (by omega)]
  simp only [step, frontFactor]
  rw [hx.1 (lo - 1) (Or.inl (by omega)), h2, h1, hinj]
  ring

/-- [definition] **A uniform chain.** -/
def Material.uniform (C G L : ℚ) : Material := ⟨fun _ => C, fun _ => G, fun _ => L⟩

/-- [definition] **The unit impulse** at node `0`, with no current. -/
def impulse : State := ⟨fun i => if i = 0 then 1 else 0, 0⟩

theorem impulse_supported : Supported 0 0 impulse := by
  refine ⟨fun i hi => ?_, fun e _ => rfl⟩
  simp only [impulse]
  rw [if_neg (by omega)]

/-- [definition] The damping ratio of the front per tick, `2C/(2C + hG)`. -/
def damping (C G h : ℚ) : ℚ := 2 * C / (2 * C + h * G)

/-- [proved-derived; formal-checked] **Loss only damps the front**: the front factor with leakage
is the lossless front factor times the damping ratio. -/
theorem frontFactor_eq_damping_mul_lossless (C G L h : ℚ) (hC : 0 < C) (hh : 0 ≤ h)
    (hG : 0 ≤ G) (i e : ℤ) :
    frontFactor (Material.uniform C G L) h i e =
      damping C G h * frontFactor (Material.uniform C 0 L) h i e := by
  have hden : 2 * C + h * G ≠ 0 := by positivity
  simp only [frontFactor, gain, coupling, damping, Material.uniform]
  field_simp
  ring

theorem damping_pos {C G h : ℚ} (hC : 0 < C) (hh : 0 ≤ h) (hG : 0 ≤ G) : 0 < damping C G h := by
  unfold damping; positivity

theorem damping_le_one {C G h : ℚ} (hC : 0 < C) (hh : 0 ≤ h) (hG : 0 ≤ G) :
    damping C G h ≤ 1 := by
  unfold damping
  rw [div_le_one (by positivity)]
  nlinarith [mul_nonneg hh hG]

/-- [proved-derived; formal-checked] The damping ratio is one exactly without leakage. -/
theorem damping_eq_one_iff {C G h : ℚ} (hC : 0 < C) (hh : 0 < h) (hG : 0 ≤ G) :
    damping C G h = 1 ↔ G = 0 := by
  unfold damping
  rw [div_eq_one_iff_eq (by positivity)]
  constructor
  · intro heq
    have : h * G = 0 := by linarith
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 hh.ne'
    · exact h0
  · rintro rfl; ring

/-- [counterexample; formal-checked] **`G ≥ 0` is load-bearing for the damping**: a negative
leakage (an active medium) amplifies the front, `2C/(2C + hG) = 2` at `C = h = 1`, `G = −1`, on
the same cone. -/
theorem negative_leakage_amplifies : damping 1 (-1) 1 = 2 ∧ 1 < damping 1 (-1) 1 := by
  unfold damping; norm_num

/-- [proved-derived; formal-checked] **The front never stops** on a positive chain: the front
factor is nonzero for every leakage `G ≥ 0`. -/
theorem frontFactor_ne_zero {C G L h : ℚ} (hC : 0 < C) (hL : 0 < L) (hh : 0 < h) (hG : 0 ≤ G)
    (i e : ℤ) : frontFactor (Material.uniform C G L) h i e ≠ 0 := by
  simp only [frontFactor, gain, coupling, Material.uniform]
  have : 0 < 2 * C + h * G := by positivity
  positivity

/-- [proved-derived; formal-checked] **The impulse fills exactly its cone.** On a uniform chain,
`n` ticks after a unit impulse the state is supported in `[−n, n]` and reads
`(gain · coupling)ⁿ` at both edges. -/
theorem impulse_cone (C G L h : ℚ) (n : ℕ) :
    Supported (-n) n (run (Material.uniform C G L) h silent impulse n) ∧
      (run (Material.uniform C G L) h silent impulse n).V n =
        frontFactor (Material.uniform C G L) h 0 0 ^ n ∧
      (run (Material.uniform C G L) h silent impulse n).V (-n) =
        frontFactor (Material.uniform C G L) h 0 0 ^ n := by
  have hff : ∀ i e i' e', frontFactor (Material.uniform C G L) h i e =
      frontFactor (Material.uniform C G L) h i' e' := by
    intro i e i' e'; rfl
  induction n with
  | zero =>
    refine ⟨by simpa using impulse_supported, ?_, ?_⟩ <;> simp [impulse]
  | succ n ih =>
    obtain ⟨hs, hr, hl⟩ := ih
    have hcone := run_cone (Material.uniform C G L) h impulse_supported (n + 1)
    refine ⟨by simpa using hcone, ?_, ?_⟩
    · rw [run_succ]
      have := step_front_right (m := Material.uniform C G L) (h := h) (s := silent n) hs
        (by positivity)
      push_cast
      rw [this, hr, hff _ _ 0 0, pow_succ]
      ring
    · rw [run_succ]
      have := step_front_left (m := Material.uniform C G L) (h := h) (s := silent n) hs
        (by simp)
      push_cast
      rw [show -((n : ℤ) + 1) = -(n : ℤ) - 1 by ring, this, hl, hff _ _ 0 0, pow_succ]
      ring

/-- [proved-derived; formal-checked] **Loss damps but never speeds a signal.** For every leakage
`G ≥ 0` the impulse occupies the same cone `[−n, n]`, its front is nonzero, and it is the lossless
front times `(2C/(2C + hG))ⁿ`. -/
theorem impulse_front_damped {C G L h : ℚ} (hC : 0 < C) (hL : 0 < L) (hh : 0 < h) (hG : 0 ≤ G)
    (n : ℕ) :
    Supported (-n) n (run (Material.uniform C G L) h silent impulse n) ∧
      (run (Material.uniform C G L) h silent impulse n).V n ≠ 0 ∧
      (run (Material.uniform C G L) h silent impulse n).V n =
        damping C G h ^ n * (run (Material.uniform C 0 L) h silent impulse n).V n := by
  obtain ⟨hs, hr, -⟩ := impulse_cone C G L h n
  obtain ⟨-, hr0, -⟩ := impulse_cone C 0 L h n
  refine ⟨hs, ?_, ?_⟩
  · rw [hr]; exact pow_ne_zero _ (frontFactor_ne_zero hC hL hh hG 0 0)
  · rw [hr, hr0, frontFactor_eq_damping_mul_lossless C G L h hC hh.le hG, mul_pow]

/-! ## 5. The node's own factor is a Cayley map -/

theorem loss_le_one {C G h : ℚ} (hC : 0 < C) (hh : 0 ≤ h) (hG : 0 ≤ G) (i : ℤ) :
    loss (Material.uniform C G 1) h i ≤ 1 := by
  simp only [loss, Material.uniform]
  rw [div_le_one (by positivity)]
  nlinarith [mul_nonneg hh hG]

theorem loss_gt_neg_one {C G h : ℚ} (hC : 0 < C) (hh : 0 ≤ h) (hG : 0 ≤ G) (i : ℤ) :
    -1 < loss (Material.uniform C G 1) h i := by
  simp only [loss, Material.uniform]
  rw [lt_div_iff₀ (by positivity)]
  nlinarith

/-- [proved-derived; formal-checked] The node keeps its charge over a tick exactly without
leakage. -/
theorem loss_eq_one_iff {C G h : ℚ} (hC : 0 < C) (hh : 0 < h) (hG : 0 ≤ G) (i : ℤ) :
    loss (Material.uniform C G 1) h i = 1 ↔ G = 0 := by
  simp only [loss, Material.uniform]
  rw [div_eq_one_iff_eq (by positivity)]
  constructor
  · intro heq
    have : h * G = 0 := by linarith
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 hh.ne'
    · exact h0
  · rintro rfl; ring

section Audit

#print axioms step_is_the_telegrapher
#print axioms change_moves_one_cell_per_tick
#print axioms impulse_cone
#print axioms impulse_front_damped
#print axioms loss_eq_one_iff

end Audit

end Holonics.Physics.Wave.Telegrapher
