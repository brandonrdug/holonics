import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic

/-!
# A place hearing its own release in step: two-cycles, and the flip of a multiplier under `−1`

The ring record of November 13 (`research/records/2026-11-13_THE_FIELD_RINGS_UNDER_ITS_OWN_RELEASE_…`, §2 and §5; atlas
`tower.field-echo`, `motion.relaxed-step-three-kinds`) read the field's release run off when every open place heard the
others' releases at once: a place flipped each pass. #410 owes the statement that a symmetric map iterated in step settles only
at fixed points or two-cycles, and that a place whose release returns to it with a multiplier under `−1` flips each pass. This
file proves both, the first in the sign chart (the half-turn sheets of the parametron's Ising lock), the second on the
linearized return.

[proved-standard; formal-checked] What is proved.

1. **The pair energy falls in step** (`energy_identity`, `energy_drop_nonneg`, `energy_drop_pos`): for a symmetric integer
   coupling `W` and the synchronous step `s ↦ sign(W s)`, the energy of two successive states,
   `E(s, t) = −⟨t, W s⟩`, satisfies `E(s, t) = E(t, F t) + Σ_i (F(t)_i − s_i)(W t)_i` with `t = F s`; every term of the
   sum is nonnegative, and where no place's field is zero a term is positive exactly where `F(t)_i ≠ s_i`.
2. **Every orbit ends on a fixed point or a two-cycle** (`eventually_period_two`): with no place's field zero on a sign
   state, the orbit of any sign state satisfies `s_(k+2) = s_k` from some step on. This is the theorem of Goles and Olivos
   (1980) for synchronous symmetric threshold networks: a synchronous symmetric map has no longer cycle, and the two-cycle is
   the only motion it keeps.
3. **A multiplier under `−1` flips each pass and grows** (`flip_each_pass`): on the linearized return `x_k = μ^k x_0` with
   `μ < −1` and `x_0 ≠ 0`, successive passes have opposite signs and growing size, so a place hearing its own release at that
   gain flips each pass until its saturation holds it, on the two-cycle of statement 2.

Limits: statement 2 is in the sign chart with integer couplings and assumes no place's field is zero on any sign state (a
tie rule would give the energy's fall without its strictness); the field's release is a softmax over classes, not a sign, and
its two-cycle is read on the line, not derived here. The parametron's period doubling in this chart (a pumped constitution's
monodromy crossing `−1`) stays owed. The Rust release is not tied to these statements.

The computational object is the helical pair interaction: the coupling `W` is the pair contacts' symmetric exchange, a place's
field the contacts' sum at it, and the two-cycle the half-turn sheet flipping each pass. Of the winding guide's six general
objects this touches the pair (the symmetric exchange) and the tube (the passes as a clocked span); the helix, faces and
placement, cell holonomy and tower thread stay attached.

Consumers: the atlas rows `tower.field-echo` and `motion.relaxed-step-three-kinds`; #410's box for the synchronous two-cycle.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.HNN.SynchronousTwoCycle

open Matrix

variable {n : ℕ}

/-! ## 1. The sign chart and the pair energy -/

/-- [definition] A sign state: every place on one of its two half-turn sheets. -/
def IsSign (s : Fin n → ℤ) : Prop := ∀ i, s i = 1 ∨ s i = -1

/-- [definition] **The synchronous step**: every place takes the sign of the field its contacts give it, all at once. -/
def step (W : Matrix (Fin n) (Fin n) ℤ) (s : Fin n → ℤ) : Fin n → ℤ :=
  fun i => if 0 < (W *ᵥ s) i then 1 else -1

/-- [proved-standard; formal-checked] The step lands on a sign state. -/
theorem step_isSign (W : Matrix (Fin n) (Fin n) ℤ) (s : Fin n → ℤ) : IsSign (step W s) := fun i => by
  unfold step
  split_ifs <;> simp

/-- [definition] **The pair energy** of two successive states, `E(s, t) = −⟨t, W s⟩`. -/
def energy (W : Matrix (Fin n) (Fin n) ℤ) (s t : Fin n → ℤ) : ℤ := -(t ⬝ᵥ (W *ᵥ s))

/-- [proved-standard; formal-checked] For a symmetric coupling the pair energy is symmetric in its two states. -/
theorem energy_symm (W : Matrix (Fin n) (Fin n) ℤ) (hW : Wᵀ = W) (s t : Fin n → ℤ) :
    energy W s t = -(s ⬝ᵥ (W *ᵥ t)) := by
  unfold energy
  congr 1
  rw [dotProduct_mulVec, ← mulVec_transpose, hW, dotProduct_comm]

/-- [proved-standard; formal-checked] **The energy identity**: `E(s, t) = E(t, u) + Σ_i (u_i − s_i)(W t)_i`. -/
theorem energy_identity (W : Matrix (Fin n) (Fin n) ℤ) (hW : Wᵀ = W) (s t u : Fin n → ℤ) :
    energy W s t = energy W t u + ∑ i, (u i - s i) * (W *ᵥ t) i := by
  rw [energy_symm W hW s t, energy]
  simp only [dotProduct, sub_mul, Finset.sum_sub_distrib]
  ring

/-- [proved-standard; formal-checked] Every term of the energy's fall is nonnegative when `u` is the step from `t` and `s`
is a sign state. -/
theorem energy_drop_nonneg (W : Matrix (Fin n) (Fin n) ℤ) (s t : Fin n → ℤ) (hs : IsSign s) (i : Fin n) :
    0 ≤ (step W t i - s i) * (W *ᵥ t) i := by
  unfold step
  rcases hs i with h | h <;> rw [h] <;> split_ifs with hp
  · simp
  · nlinarith
  · nlinarith
  · simp

/-- [proved-standard; formal-checked] Where a place's field is not zero and the step changes the place from `s`, its term of
the fall is positive. -/
theorem energy_drop_pos (W : Matrix (Fin n) (Fin n) ℤ) (s t : Fin n → ℤ) (hs : IsSign s) (i : Fin n)
    (hz : (W *ᵥ t) i ≠ 0) (hne : step W t i ≠ s i) :
    0 < (step W t i - s i) * (W *ᵥ t) i := by
  unfold step at hne ⊢
  rcases hs i with h | h <;> rw [h] at hne ⊢ <;> split_ifs at hne ⊢ with hp
  · exact absurd rfl hne
  · have : (W *ᵥ t) i < 0 := lt_of_le_of_ne (not_lt.mp hp) hz
    nlinarith
  · nlinarith
  · exact absurd rfl hne

/-! ## 2. Every orbit ends on a fixed point or a two-cycle -/

/-- [proved-standard; formal-checked] An antitone sequence of naturals is eventually constant. -/
theorem antitone_nat_stabilizes : ∀ (v : ℕ) (f : ℕ → ℕ), Antitone f → f 0 ≤ v → ∃ K, ∀ k, K ≤ k → f k = f K
  | 0, f, hf, h0 => ⟨0, fun k _ => by have := hf (Nat.zero_le k); omega⟩
  | v + 1, f, hf, h0 => by
    by_cases hc : ∀ k, f k = f 0
    · exact ⟨0, fun k _ => hc k⟩
    · push Not at hc
      obtain ⟨k, hk⟩ := hc
      have hlt : f k < f 0 := lt_of_le_of_ne (hf (Nat.zero_le k)) hk
      obtain ⟨K, hK⟩ := antitone_nat_stabilizes v (fun j => f (k + j))
        (fun a b hab => hf (by omega)) (by simp only [Nat.add_zero]; omega)
      refine ⟨k + K, fun m hm => ?_⟩
      have h := hK (m - k) (by omega)
      rwa [show k + (m - k) = m by omega] at h

/-- [proved-standard; formal-checked] The sign states are finitely many. -/
theorem isSign_finite : {s : Fin n → ℤ | IsSign s}.Finite := by
  have h : (Set.pi Set.univ (fun _ : Fin n => ({1, -1} : Set ℤ))).Finite :=
    Set.Finite.pi (fun _ => Set.toFinite _)
  refine h.subset ?_
  intro s hs i _
  rcases hs i with h | h <;> simp [h]

/-- [proved-standard; formal-checked] **Every orbit of the synchronous symmetric step ends on a fixed point or a
two-cycle** (Goles and Olivos): with no place's field zero on a sign state, `s_(k+2) = s_k` from some step on. -/
theorem eventually_period_two (W : Matrix (Fin n) (Fin n) ℤ) (hW : Wᵀ = W)
    (hties : ∀ s, IsSign s → ∀ i, (W *ᵥ s) i ≠ 0) (s₀ : Fin n → ℤ) (hs₀ : IsSign s₀) :
    ∃ K, ∀ k, K ≤ k → (step W)^[k + 2] s₀ = (step W)^[k] s₀ := by
  set s : ℕ → Fin n → ℤ := fun k => (step W)^[k] s₀ with hsdef
  have hsign : ∀ k, IsSign (s k) := by
    intro k
    cases k with
    | zero => simpa [hsdef] using hs₀
    | succ k =>
      simp only [hsdef, Function.iterate_succ_apply']
      exact step_isSign W _
  have hsucc : ∀ k, s (k + 1) = step W (s k) := fun k => by
    simp only [hsdef, Function.iterate_succ_apply']
  set e : ℕ → ℤ := fun k => energy W (s k) (s (k + 1)) with hedef
  -- the fall from `e k` to `e (k + 1)`
  have hfall : ∀ k, e k = e (k + 1) + ∑ i, (s (k + 2) i - s k i) * (W *ᵥ s (k + 1)) i := by
    intro k
    simp only [hedef]
    exact energy_identity W hW (s k) (s (k + 1)) (s (k + 2))
  have hterm : ∀ k i, 0 ≤ (s (k + 2) i - s k i) * (W *ᵥ s (k + 1)) i := by
    intro k i
    rw [hsucc (k + 1)]
    exact energy_drop_nonneg W (s k) (s (k + 1)) (hsign k) i
  have hanti : ∀ k, e (k + 1) ≤ e k := by
    intro k
    have := hfall k
    have : 0 ≤ ∑ i, (s (k + 2) i - s k i) * (W *ᵥ s (k + 1)) i := Finset.sum_nonneg (fun i _ => hterm k i)
    linarith
  -- the energies lie in a finite set, so they are bounded below
  obtain ⟨m, hm⟩ : BddBelow ((fun p : (Fin n → ℤ) × (Fin n → ℤ) => energy W p.1 p.2) ''
      ({s : Fin n → ℤ | IsSign s} ×ˢ {s : Fin n → ℤ | IsSign s})) :=
    ((isSign_finite.prod isSign_finite).image _).bddBelow
  have hlow : ∀ k, m ≤ e k := fun k => hm ⟨(s k, s (k + 1)), ⟨hsign k, hsign (k + 1)⟩, rfl⟩
  set f : ℕ → ℕ := fun k => (e k - m).toNat with hfdef
  have hfanti : Antitone f := by
    refine antitone_nat_of_succ_le (fun k => ?_)
    simp only [hfdef]
    have := hanti k
    omega
  obtain ⟨K, hK⟩ := antitone_nat_stabilizes (f 0) f hfanti le_rfl
  refine ⟨K, fun k hk => ?_⟩
  have hk1 : f (k + 1) = f k := by rw [hK (k + 1) (by omega), hK k hk]
  have heq : e (k + 1) = e k := by
    simp only [hfdef] at hk1
    have := hlow k
    have := hlow (k + 1)
    omega
  have hzero : ∑ i, (s (k + 2) i - s k i) * (W *ᵥ s (k + 1)) i = 0 := by
    have := hfall k
    linarith
  have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hterm k i)).mp hzero
  show s (k + 2) = s k
  funext i
  by_contra hne
  have hpos : 0 < (s (k + 2) i - s k i) * (W *ᵥ s (k + 1)) i := by
    rw [hsucc (k + 1)] at hne ⊢
    exact energy_drop_pos W (s k) (s (k + 1)) (hsign k) i (hties _ (hsign (k + 1)) i) hne
  have := hall i (Finset.mem_univ i)
  linarith

/-! ## 3. A multiplier under `−1` flips each pass -/

/-- [proved-standard; formal-checked] **A place whose release returns to it with a multiplier `μ < −1` flips each pass and
grows**: on `x_k = μ^k x_0` with `x_0 ≠ 0`, successive passes have opposite signs and `|x_k| < |x_(k+1)|`. -/
theorem flip_each_pass (μ x : ℝ) (hμ : μ < -1) (hx : x ≠ 0) (k : ℕ) :
    μ ^ (k + 1) * x * (μ ^ k * x) < 0 ∧ |μ ^ k * x| < |μ ^ (k + 1) * x| := by
  have hμ0 : μ ≠ 0 := by linarith
  have hy : μ ^ k * x ≠ 0 := mul_ne_zero (pow_ne_zero k hμ0) hx
  have hsq : 0 < (μ ^ k * x) ^ 2 := by positivity
  have hrw : μ ^ (k + 1) * x = μ * (μ ^ k * x) := by ring
  constructor
  · rw [hrw]
    nlinarith
  · rw [hrw, abs_mul μ (μ ^ k * x)]
    have habs : 1 < |μ| := by
      rw [abs_of_neg (by linarith)]
      linarith
    have hpos : 0 < |μ ^ k * x| := abs_pos.mpr hy
    nlinarith

end Holonics.HNN.SynchronousTwoCycle
