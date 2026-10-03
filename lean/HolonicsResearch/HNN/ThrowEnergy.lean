import HolonicsResearch.HNN.MoveDirection

/-!
# HNN.ThrowEnergy: the throw's per-move energy law and the floor along a nonconvex line

[definition] The throw (#240,
`research/records/2026-10-02_THE_THROW_CARRIES_ITS_MOMENTUM_THROUGH_THE_DEPOSITS_ACCRETED_MASS_AND_A_HALVING_HALVES_IT.md`
at [`4743e836`](https://github.com/brandonrdug/holonics/tree/4743e836), §2, §5 and §7) and the deposit
record's §6 items 4 and 5 (#62). The constitution's map moves with the source Gram `H` for its mass.
A deposit accretes `F` (`H′ = H + F`) and holds the carried momentum `P`; the coast is `c = X P`
through the deposit's chart `X = H′⁻¹`; the impulse is the descent covector `G` with unit step
`D = X G` and step `η`; a trial adopted at the halving `τ` moves by `v = τ(ηD + c)`, and the carried
velocity is that move on the lattice, `d′ = v + r`. The next deposit accretes `F′` and its chart
`X′ = (H′ + F′)⁻¹` reads the next coast `c′ = X′ P′` of the next momentum `P′ = H′ d′`.

[proved-derived; formal-checked] What is proved.

1. **The kinetic reading after the move** (`throw_kinetic_after`):
   `½⟨v, H′ v⟩ = τ² (½⟨P, c⟩ + η⟨G, c⟩ + ½η²⟨G, D⟩)`, since `H′ v = τ(ηG + P)`: the momentum after
   the impulse is `P + ηG`, halved with the move.
2. **The per-move energy law** (`throw_energy_law`): with `L_held` read at the carried state and
   its second-order remainder `R = L(x + d′) − L(x) + ⟨G, d′⟩` along the move, exactly
   ```text
   ½⟨P′, c′⟩ + L(x + d′) = ½⟨P, c⟩ + L(x)
       − (1 − τ²)·½⟨P, c⟩                        (the halving drops momentum)
       − loss′                                   (the next deposit's sticking loss)
       − τ(1 − τη)⟨G, c⟩                         (the coast's power)
       − τη(1 − τη/2)⟨G, D⟩                      (the impulse's descent)
       + ρ + R
   ```
   with `loss′ = ½⟨c′, F′ c′⟩ + ½⟨d′ − c′, H′(d′ − c′)⟩` (`MoveDirection.held_momentum_loss`) and the
   lattice's rounding `ρ = τ⟨r, ηG + P⟩ + ½⟨r, H′ r⟩ − ⟨G, r⟩`, zero at `r = 0`.
3. **When the energy falls** (`throw_energy_falls`, `throw_dissipation_nonneg`). The energy
   `½⟨P, c⟩ + L_held` does not rise across the move exactly when `R + ρ` is within the four
   dissipations. For `H′ ⪰ 0`, `F′ ⪰ 0`, `0 ≤ τ ≤ 1` and `0 ≤ τη ≤ 1`, the halving, the sticking loss
   and the impulse's term are each nonnegative (`½⟨P, c⟩ = ½⟨c, H′c⟩`, `⟨G, D⟩ = ⟨D, H′D⟩`), and the
   coast's term is nonnegative exactly when the coast falls at first order, `⟨G, c⟩ ≥ 0`. Where the
   coast climbs (`⟨G, c⟩ < 0`) it injects `τ(1 − τη)|⟨G, c⟩|` unless `τη = 1`, which is #240's apex
   release read as energy. The law is stated at the exact chart `H′X = 1`; the chart's certified
   residual `δ` enters as a further term this file does not state.
4. **The floor along a nonconvex line** (§7, `line_slope_le`, `nonconvex_line_falls_to`,
   `nonconvex_line_le_quadratic`, `nonconvex_stop_value`, `nonconvex_apex_rises`). Along
   `f(τ) = L(E + τw)` with slope `s = f′(0)` and only an upper curvature bound `f″ ≤ κ⁺` on
   `[0, T]` (either sign), `f′(t) ≤ s + κ⁺t`; the line falls on `[τ₁, τ₂] ⊆ [0, T]` wherever
   `s ≤ 0` and `s + κ⁺τ₂ ≤ 0`; it lies below the quadratic `f(0) + sτ + κ⁺τ²/2`; and the derived stop
   `τ* = −s/κ⁺` (`κ⁺ > 0`, `τ* ≤ T`) lowers it by at least `s²/(2κ⁺)`. With a lower bound
   `f″ ≥ κ⁻`, nothing on `[0, τ]` is lower while `s + κ⁻τ/2 ≥ 0`, which at an apex (`s ≥ 0`)
   holds near the start: at a nonconvex apex
   the reach with nothing lower ahead is `−2s/κ⁻` when `κ⁻ < 0`, and the whole line when `κ⁻ ≥ 0`
   (`MoveDirection.coast_apex_no_floor_ahead`'s convex case). The quadratic lemmas of
   `MoveDirection` §9 are the case `f″ ≡ κ`.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.HNN.ThrowEnergy

open Matrix
open Holonics.HNN.MoveDirection (held_momentum_loss)

/-! ## 1. The throw's per-move energy law -/

section Energy

variable {n : Type*} [Fintype n]

/-- The chart returns its argument through the mass: `H′ (X y) = y` when `H′ X = 1`. -/
theorem mass_chart [DecidableEq n] {M X : Matrix n n ℝ} (hX : M * X = 1)
    (y : n → ℝ) : M *ᵥ (X *ᵥ y) = y := by
  rw [mulVec_mulVec, hX, one_mulVec]

/-- A symmetric matrix pairs symmetrically. -/
theorem dot_mulVec_symm {X : Matrix n n ℝ} (hX : Xᵀ = X) (a b : n → ℝ) :
    (X *ᵥ a) ⬝ᵥ b = (X *ᵥ b) ⬝ᵥ a := by
  rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, hX]

/-- [proved-derived; formal-checked] **The kinetic reading after the move.** With the exact chart
`H′ X = 1`, `X` symmetric, the coast `c = X P`, the unit step `D = X G` and the trial
`v = τ(ηD + c)`: `⟨v, H′ v⟩ = τ²(⟨P, c⟩ + 2η⟨G, c⟩ + η²⟨G, D⟩)`. -/
theorem throw_kinetic_after [DecidableEq n] {M X : Matrix n n ℝ} (hX : M * X = 1)
    (hXs : Xᵀ = X) (P G : n → ℝ) (η τ : ℝ) :
    (τ • (η • (X *ᵥ G) + X *ᵥ P)) ⬝ᵥ (M *ᵥ (τ • (η • (X *ᵥ G) + X *ᵥ P))) =
      τ ^ 2 * (P ⬝ᵥ (X *ᵥ P) + 2 * η * (G ⬝ᵥ (X *ᵥ P)) + η ^ 2 * (G ⬝ᵥ (X *ᵥ G))) := by
  have hv : M *ᵥ (τ • (η • (X *ᵥ G) + X *ᵥ P)) = τ • (η • G + P) := by
    rw [mulVec_smul, mulVec_add, mulVec_smul, mass_chart hX, mass_chart hX]
  have hs : (X *ᵥ G) ⬝ᵥ P = G ⬝ᵥ (X *ᵥ P) := by
    rw [dot_mulVec_symm hXs, dotProduct_comm]
  rw [hv]
  simp only [smul_dotProduct, dotProduct_smul, add_dotProduct, dotProduct_add, smul_eq_mul, hs]
  rw [dotProduct_comm (X *ᵥ P) G, dotProduct_comm (X *ᵥ G) G, dotProduct_comm (X *ᵥ P) P]
  ring

/-- [proved-derived; formal-checked] **The throw's per-move energy law.** With the deposit's mass
`H′` (symmetric) and exact chart `H′ X = 1` (`X` symmetric), the coast `c = X P`, the unit step
`D = X G`, the carried velocity `d′ = τ(ηD + c) + r`, the next momentum `P′ = H′ d′` and the next
coast `c′ = X′ P′` through `(H′ + F′) X′ = 1`, for any comparison `L`:
`½⟨P′, c′⟩ + L(x + d′) = ½⟨P, c⟩ + L(x) − (1 − τ²)·½⟨P, c⟩ − loss′ − τ(1 − τη)⟨G, c⟩
 − τη(1 − τη/2)⟨G, D⟩ + ρ + R`, each term as in the module header. -/
theorem throw_energy_law [DecidableEq n] {M F' X X' : Matrix n n ℝ} (hM : Mᵀ = M)
    (hX : M * X = 1) (hXs : Xᵀ = X) (hX' : (M + F') * X' = 1)
    (P G r x : n → ℝ) (η τ : ℝ) (L : (n → ℝ) → ℝ) :
    let c := X *ᵥ P
    let D := X *ᵥ G
    let d' := τ • (η • D + c) + r
    let c' := X' *ᵥ (M *ᵥ d')
    (1 / 2) * ((M *ᵥ d') ⬝ᵥ c') + L (x + d') =
      (1 / 2) * (P ⬝ᵥ c) + L x
        - (1 - τ ^ 2) * ((1 / 2) * (P ⬝ᵥ c))
        - ((1 / 2) * (c' ⬝ᵥ (F' *ᵥ c')) + (1 / 2) * ((d' - c') ⬝ᵥ (M *ᵥ (d' - c'))))
        - τ * (1 - τ * η) * (G ⬝ᵥ c)
        - τ * η * (1 - τ * η / 2) * (G ⬝ᵥ D)
        + (τ * (r ⬝ᵥ (η • G + P)) + (1 / 2) * (r ⬝ᵥ (M *ᵥ r)) - G ⬝ᵥ r)
        + (L (x + d') - L x + G ⬝ᵥ d') := by
  intro c D d' c'
  set v := τ • (η • D + c) with hvdef
  have k2 := throw_kinetic_after hX hXs P G η τ
  have hMv : M *ᵥ v = τ • (η • G + P) := by
    rw [hvdef, mulVec_smul, mulVec_add, mulVec_smul, mass_chart hX, mass_chart hX]
  have k3 : r ⬝ᵥ (M *ᵥ v) = τ * (r ⬝ᵥ (η • G + P)) := by
    rw [hMv, dotProduct_smul, smul_eq_mul]
  have hsymM : v ⬝ᵥ (M *ᵥ r) = r ⬝ᵥ (M *ᵥ v) := by
    rw [dotProduct_comm, ← dot_mulVec_symm hM, dotProduct_comm]
  have k1 : d' ⬝ᵥ (M *ᵥ d') = v ⬝ᵥ (M *ᵥ v) + 2 * (r ⬝ᵥ (M *ᵥ v)) + r ⬝ᵥ (M *ᵥ r) := by
    change (v + r) ⬝ᵥ (M *ᵥ (v + r)) = _
    rw [mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add, hsymM]
    ring
  have hheld : M *ᵥ d' = (M + F') *ᵥ c' := (mass_chart hX' _).symm
  have k4 := held_momentum_loss M F' hM d' c' hheld
  have k5 : (M *ᵥ d') ⬝ᵥ c' = c' ⬝ᵥ ((M + F') *ᵥ c') := by rw [hheld, dotProduct_comm]
  have k6 : G ⬝ᵥ d' = τ * η * (G ⬝ᵥ D) + τ * (G ⬝ᵥ c) + G ⬝ᵥ r := by
    change G ⬝ᵥ (τ • (η • D + c) + r) = _
    simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]
    ring
  rw [k5]
  change (1 / 2) * (c' ⬝ᵥ ((M + F') *ᵥ c')) + L (x + d') = _
  have k2' : v ⬝ᵥ (M *ᵥ v) =
      τ ^ 2 * (P ⬝ᵥ c + 2 * η * (G ⬝ᵥ c) + η ^ 2 * (G ⬝ᵥ D)) := k2
  linear_combination (1 / 2) * k1 - (1 / 2) * k4 + (1 / 2) * k2' + k3 - k6

/-- [proved-derived; formal-checked] **The energy falls exactly when the remainder is within the
dissipation**: in the law's terms, `½⟨P′, c′⟩ + L(x + d′) ≤ ½⟨P, c⟩ + L(x)` iff
`ρ + R ≤ (1 − τ²)·½⟨P, c⟩ + loss′ + τ(1 − τη)⟨G, c⟩ + τη(1 − τη/2)⟨G, D⟩`. -/
theorem throw_energy_falls {E₀ E₁ halving loss coast impulse ρ R : ℝ}
    (hlaw : E₁ = E₀ - halving - loss - coast - impulse + ρ + R) :
    E₁ ≤ E₀ ↔ ρ + R ≤ halving + loss + coast + impulse := by
  constructor <;> intro h <;> linarith

/-- [proved-derived; formal-checked] **The dissipations' signs.** For `H′ ⪰ 0` (as a form), the
exact chart `H′ X = 1`, `F′ ⪰ 0`, `0 ≤ τ ≤ 1` and `0 ≤ τη ≤ 1`: the halving's
`(1 − τ²)·½⟨P, c⟩`, the sticking loss and the impulse's `τη(1 − τη/2)⟨G, D⟩` are nonnegative, and
the coast's `τ(1 − τη)⟨G, c⟩` is nonnegative wherever the coast falls at first order, `⟨G, c⟩ ≥ 0`. -/
theorem throw_dissipation_nonneg [DecidableEq n] {M F' X : Matrix n n ℝ}
    (hpsd : ∀ y : n → ℝ, 0 ≤ y ⬝ᵥ (M *ᵥ y)) (hF' : ∀ y : n → ℝ, 0 ≤ y ⬝ᵥ (F' *ᵥ y))
    (hX : M * X = 1) (P G a b : n → ℝ) {η τ : ℝ}
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (hτη0 : 0 ≤ τ * η) (hτη1 : τ * η ≤ 1) :
    0 ≤ (1 - τ ^ 2) * ((1 / 2) * (P ⬝ᵥ (X *ᵥ P))) ∧
      0 ≤ (1 / 2) * (a ⬝ᵥ (F' *ᵥ a)) + (1 / 2) * (b ⬝ᵥ (M *ᵥ b)) ∧
      0 ≤ τ * η * (1 - τ * η / 2) * (G ⬝ᵥ (X *ᵥ G)) ∧
      (0 ≤ G ⬝ᵥ (X *ᵥ P) → 0 ≤ τ * (1 - τ * η) * (G ⬝ᵥ (X *ᵥ P))) := by
  have hread : ∀ y, y ⬝ᵥ (X *ᵥ y) = (X *ᵥ y) ⬝ᵥ (M *ᵥ (X *ᵥ y)) := fun y => by
    rw [mass_chart hX, dotProduct_comm]
  have hP := hread P
  have hG := hread G
  have h1 : 0 ≤ P ⬝ᵥ (X *ᵥ P) := hP ▸ hpsd _
  have h2 : 0 ≤ G ⬝ᵥ (X *ᵥ G) := hG ▸ hpsd _
  refine ⟨?_, ?_, ?_, ?_⟩
  · have : 0 ≤ 1 - τ ^ 2 := by nlinarith
    positivity
  · have := hF' a
    have := hpsd b
    linarith
  · have : 0 ≤ 1 - τ * η / 2 := by linarith
    have := mul_nonneg (mul_nonneg hτη0 this) h2
    linarith [this]
  · intro hc
    have : 0 ≤ 1 - τ * η := by linarith
    positivity

end Energy

/-! ## 2. The floor along a nonconvex line -/

section Floor

/-- A function whose derivative is nonpositive on `[a, b]` is antitone there. -/
theorem antitoneOn_Icc_of_hasDerivAt {g g' : ℝ → ℝ} {a b : ℝ}
    (hg : ∀ t, HasDerivAt g (g' t) t) (hle : ∀ t ∈ Set.Icc a b, g' t ≤ 0) :
    AntitoneOn g (Set.Icc a b) :=
  antitoneOn_of_deriv_nonpos (convex_Icc a b)
    (fun t _ => (hg t).continuousAt.continuousWithinAt)
    (fun t _ => (hg t).differentiableAt.differentiableWithinAt)
    (fun t ht => by rw [(hg t).deriv]; exact hle t (interior_subset ht))

variable {f f' f'' : ℝ → ℝ}

/-- [proved-derived; formal-checked] **An upper curvature bound bounds the slope**: if
`f″ ≤ κ` on `[0, T]` then `f′(t) ≤ f′(0) + κt` there, for either sign of `κ`. -/
theorem line_slope_le (hf' : ∀ t, HasDerivAt f' (f'' t) t) {κ T : ℝ}
    (hκ : ∀ t ∈ Set.Icc 0 T, f'' t ≤ κ) : ∀ t ∈ Set.Icc 0 T, f' t ≤ f' 0 + κ * t := by
  have hg : ∀ t, HasDerivAt (fun t => f' t - κ * t) (f'' t - κ) t := fun t =>
    ((hf' t).fun_sub ((hasDerivAt_id' t).const_mul κ)).congr_deriv (by ring)
  have ha := antitoneOn_Icc_of_hasDerivAt hg (fun t ht => by linarith [hκ t ht])
  intro t ht
  have := ha (Set.left_mem_Icc.mpr (le_trans ht.1 ht.2)) ht ht.1
  dsimp only at this
  linarith

/-- [proved-derived; formal-checked] **A nonconvex line falls up to where its slope bound turns**:
with `f″ ≤ κ⁺` on `[0, T]` (either sign), `s = f′(0) ≤ 0` and `s + κ⁺τ₂ ≤ 0`, the line falls on
`[τ₁, τ₂]` for `0 ≤ τ₁ ≤ τ₂ ≤ T`. The stop `min(T, −s⁺/κ⁺)` of `MoveDirection.line_falls_to` holds
without the quadratic profile. -/
theorem nonconvex_line_falls_to (hf : ∀ t, HasDerivAt f (f' t) t)
    (hf' : ∀ t, HasDerivAt f' (f'' t) t) {κ T τ₁ τ₂ : ℝ}
    (hκ : ∀ t ∈ Set.Icc 0 T, f'' t ≤ κ) (h₁ : 0 ≤ τ₁) (h₁₂ : τ₁ ≤ τ₂) (h₂ : τ₂ ≤ T)
    (hs : f' 0 ≤ 0) (hturn : f' 0 + κ * τ₂ ≤ 0) : f τ₂ ≤ f τ₁ := by
  have hslope := line_slope_le hf' hκ
  have hneg : ∀ t ∈ Set.Icc 0 τ₂, f' t ≤ 0 := fun t ht => by
    have := hslope t ⟨ht.1, le_trans ht.2 h₂⟩
    rcases le_total 0 κ with hκ0 | hκ0
    · nlinarith [mul_le_mul_of_nonneg_left ht.2 hκ0]
    · nlinarith [mul_nonpos_of_nonpos_of_nonneg hκ0 ht.1]
  exact antitoneOn_Icc_of_hasDerivAt hf hneg ⟨h₁, h₁₂⟩ ⟨le_trans h₁ h₁₂, le_rfl⟩ h₁₂

/-- [proved-derived; formal-checked] **A nonconvex line lies below its upper quadratic**: with
`f″ ≤ κ⁺` on `[0, T]`, `f(τ) ≤ f(0) + sτ + κ⁺τ²/2` for `τ ∈ [0, T]`, `s = f′(0)`. -/
theorem nonconvex_line_le_quadratic (hf : ∀ t, HasDerivAt f (f' t) t)
    (hf' : ∀ t, HasDerivAt f' (f'' t) t) {κ T : ℝ} (hκ : ∀ t ∈ Set.Icc 0 T, f'' t ≤ κ)
    {τ : ℝ} (hτ : τ ∈ Set.Icc 0 T) : f τ ≤ f 0 + f' 0 * τ + κ * τ ^ 2 / 2 := by
  have hslope := line_slope_le hf' hκ
  have hg : ∀ t, HasDerivAt (fun t => f t - (f' 0 * t + κ * t ^ 2 / 2)) (f' t - (f' 0 + κ * t)) t :=
    fun t => by
      have h2 : HasDerivAt (fun t : ℝ => f' 0 * t + κ * t ^ 2 / 2) (f' 0 + κ * t) t := by
        exact (((hasDerivAt_id' t).const_mul (f' 0)).fun_add
          (((hasDerivAt_pow 2 t).const_mul κ).div_const 2)).congr_deriv (by push_cast; ring)
      exact (hf t).sub h2
  have ha := antitoneOn_Icc_of_hasDerivAt hg (fun t ht => by linarith [hslope t ht])
  have := ha (Set.left_mem_Icc.mpr (le_trans hτ.1 hτ.2)) hτ hτ.1
  dsimp only at this
  linarith

/-- [proved-derived; formal-checked] **The derived stop lowers a nonconvex line**: with
`f″ ≤ κ⁺`, `κ⁺ > 0`, on `[0, T]` and the stop `τ* = −s/κ⁺ ∈ [0, T]`,
`f(τ*) ≤ f(0) − s²/(2κ⁺)`. -/
theorem nonconvex_stop_value (hf : ∀ t, HasDerivAt f (f' t) t)
    (hf' : ∀ t, HasDerivAt f' (f'' t) t) {κ T : ℝ} (hκ : ∀ t ∈ Set.Icc 0 T, f'' t ≤ κ)
    (hκ0 : 0 < κ) (hs : f' 0 ≤ 0) (hT : -f' 0 / κ ≤ T) :
    f (-f' 0 / κ) ≤ f 0 - f' 0 ^ 2 / (2 * κ) := by
  have hτ : -f' 0 / κ ∈ Set.Icc 0 T := ⟨div_nonneg (by linarith) hκ0.le, hT⟩
  have h := nonconvex_line_le_quadratic hf hf' hκ hτ
  have e : f' 0 * (-f' 0 / κ) + κ * (-f' 0 / κ) ^ 2 / 2 = -(f' 0 ^ 2 / (2 * κ)) := by
    field_simp
    ring
  linarith

/-- [proved-derived; formal-checked] **At a nonconvex apex nothing is lower within the reach of the
lower curvature bound**: with `f″ ≥ κ⁻` on `[0, T]` and `s = f′(0)` (at an apex `s ≥ 0`), every
`τ ∈ [0, T]` with
`s + κ⁻τ/2 ≥ 0` has `f(0) ≤ f(τ)`. For `κ⁻ ≥ 0` that is the whole line (the convex case); for
`κ⁻ < 0` it is `τ ≤ −2s/κ⁻`. -/
theorem nonconvex_apex_rises (hf : ∀ t, HasDerivAt f (f' t) t)
    (hf' : ∀ t, HasDerivAt f' (f'' t) t) {κ T : ℝ} (hκ : ∀ t ∈ Set.Icc 0 T, κ ≤ f'' t)
    {τ : ℝ} (hτ : τ ∈ Set.Icc 0 T) (hreach : 0 ≤ f' 0 + κ * τ / 2) :
    f 0 ≤ f τ := by
  have hneg : ∀ t, HasDerivAt (fun t => -f t) (-f' t) t := fun t => (hf t).neg
  have hneg' : ∀ t, HasDerivAt (fun t => -f' t) (-f'' t) t := fun t => (hf' t).neg
  have h := nonconvex_line_le_quadratic (f := fun t => -f t) (f' := fun t => -f' t)
    (f'' := fun t => -f'' t) hneg hneg' (κ := -κ) (fun t ht => by linarith [hκ t ht]) hτ
  nlinarith [mul_nonneg hτ.1 hreach]

end Floor

section Audit

#print axioms throw_kinetic_after
#print axioms throw_energy_law
#print axioms throw_energy_falls
#print axioms throw_dissipation_nonneg
#print axioms line_slope_le
#print axioms nonconvex_line_falls_to
#print axioms nonconvex_line_le_quadratic
#print axioms nonconvex_stop_value
#print axioms nonconvex_apex_rises

end Audit

end Holonics.HNN.ThrowEnergy
