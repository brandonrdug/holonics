import Holonics.HNN.LatticeWord

/-!
# HNN.StorageResolution: a storage deposit reaches the next contact passage only through the rate's jump

[proved-derived; formal-checked] Astra's joint continuation (`hnn::reference::continuation`) deposits
on a contact's storage factor and opens the next contact passage from the same representatives as
the word it replaces. On the declared word lattice the next representative stays equal while the
material changed. This module states why, and the condition under which it must part.

```text
transit       m ζ = b ,  m′ = m + (G/h)ΔC ,  m′ ζ′ = b + 2ΔC w
response      m′(ζ′ − ζ) = ΔC (w − w⁺) ,   w⁺ = (G/h)ζ − w                 (exact)
telescoping   Σ_(t<N) (w_t − w⁺_t) = (w_0 − w_N) + (ρ_0 − ρ_N) + (G/h)(r_0 − r_N)
two words     equal representatives ⇒ r′_N − r_N = Σ_(t<N) (y′_t − y_t)
floor         m′ = c + S , S ⪰ 0 , m′V = ΔC J ⇒ c²|V|² ≤ |ΔC J|²
held          C′w′ = Cw ⇒ m′ζ′ = b ,  m′(ζ′ − ζ) = −ΔC (w + w⁺) ;  k Σ_(t<N) ζ_t = Δu + Δσ + kΔr
```

1. **The response** (`storage_transit_response`). At one representative `(u, w, α)` the transit's
   right side `h(α_g − α_h) + 2Cw − hKu` moves by `2ΔC w` and its operator
   `m = 1 + (G/2h)(2C + hD + ½h²K)` by `(G/h)ΔC`. So `m′(ζ′ − ζ) = 2ΔC(w − ω) = ΔC(w − w⁺)`, with
   `ω = (G/2h)ζ` and `w⁺ = 2ω − w` the predecessor's next rate before its split. A storage change is
   felt only through the change of rate across the tick: at a rate that does not move, the stored
   term `2Cw` and the operator's `(G/h)ΔC ζ` cancel exactly.
2. **The rate jumps telescope** (`rate_jumps_telescope`). The rate is split with its remainder `ρ`
   from `(G/h)ζ̂ − w`, and the solve `ζ̂` with its remainder `r` from `ζ`; summed over `N` ticks the
   jumps leave `(w_0 − w_N) + (ρ_0 − ρ_N) + (G/h)(r_0 − r_N)`, whatever `N`.
3. **Two words at one representative** (`feedback_remainder_difference`,
   `representatives_part_of_accumulated_unit`). Two error-feedback streams opened at one remainder
   whose carried values agree through `N` ticks differ in their remainders by exactly the
   accumulated image difference. Since both remainders lie in the half-open cell, an accumulated
   difference of one unit forces a carried value apart before tick `N`; below one unit it is held in
   the remainder, and a value parts only where a point crosses a cell boundary.
4. **The floor** (`le_of_margin_add_psd`, `storage_floor`). The contact operator is `1 + S` with
   `S = (G/2h)(2C + hD + ½h²K) ⪰ 0`; written `c·1 + S′` with `c` its least eigenvalue (`c ≥ 1`),
   `m′V = ΔC J` gives `c²|V|² ≤ |ΔC J|²`. With `V` the accumulated exact response and `J` the
   telescoped jumps, a deposit with `|ΔC J| < c·u` never forces the next passage's representative
   apart at any tick.
5. **At held momentum** (`held_storage_transit_response`, `midpoint_sum_is_travel`,
   `feedback_remainder_difference_of_openings`). When the continuation holds the momentum,
   `C′w′ = Cw`, the right side does not move, so `m′(ζ′ − ζ) = −ΔC(cζ) = −ΔC(w + w⁺)`: the deposit
   is felt through the motion, not the rate's jump. Summed over the ticks, `k = G/2` times the
   midpoints is the travel plus the displacement and solve remainders' changes. The rate's jump
   opens in the rate remainder, so two streams start from different openings and differ by that
   opening difference plus the accumulated image difference. The floor (item 4) applies unchanged.

The executed solve is a certified chart, not `m′⁻¹`; its residual adds a per-tick difference that
does not telescope (`LatticeWord.inverse_chart_deviation` bounds it). The record
`research/records/2026-10-02_A_STORAGE_DEPOSIT_IS_FELT_ONLY_THROUGH_THE_RATE_S_JUMP_AND_THE_WORD_HOLDS_IT_BELOW_ONE_UNIT.md`
reads both parts on Astra's control.
-/

namespace Holonics.HNN.StorageResolution

open Matrix Holonics.HNN.LatticeDeposit Holonics.HNN.LatticeWord

/-! ## 1. The transit's response to a storage deposit -/

section Response

variable {n : Type*} [Fintype n]

/-- [proved-derived; formal-checked] **The storage response.** If `m ζ = b` and the deposited
operator `m + cΔC` solves the right side moved by `2ΔC w`, then
`(m + cΔC)(ζ′ − ζ) = ΔC(w − (cζ − w))`: with `c = G/h`, the material change acts on the rate's jump
`w − w⁺`, `w⁺ = cζ − w`, and on nothing else. -/
theorem storage_transit_response (m ΔC : Matrix n n ℚ) (c : ℚ) (b w ζ ζ' : n → ℚ)
    (hζ : m *ᵥ ζ = b) (hζ' : (m + c • ΔC) *ᵥ ζ' = b + (2 : ℚ) • (ΔC *ᵥ w)) :
    (m + c • ΔC) *ᵥ (ζ' - ζ) = ΔC *ᵥ (w - (c • ζ - w)) := by
  rw [mulVec_sub, hζ', add_mulVec, hζ, smul_mulVec, mulVec_sub, mulVec_sub, mulVec_smul]
  ext i
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- [proved-derived; formal-checked] **A rate that does not move leaves the deposit unfelt**: at
`w⁺ = w` the response is zero, so `ζ′ = ζ` whenever the deposited operator is injective. -/
theorem storage_response_of_still_rate (m ΔC : Matrix n n ℚ) (c : ℚ) (b w ζ ζ' : n → ℚ)
    (hζ : m *ᵥ ζ = b) (hζ' : (m + c • ΔC) *ᵥ ζ' = b + (2 : ℚ) • (ΔC *ᵥ w))
    (hstill : c • ζ - w = w) : (m + c • ΔC) *ᵥ (ζ' - ζ) = 0 := by
  rw [storage_transit_response m ΔC c b w ζ ζ' hζ hζ', hstill, sub_self, mulVec_zero]

end Response

/-! ## 2. The rate jumps telescope -/

section Telescope

variable {E : Type*}

/-- [proved-derived; formal-checked] **The rate jumps telescope.** The rate is carried by error
feedback from its pre-split image `cζ̂_t − w_t` (`w_(t+1) + ρ_(t+1) = cζ̂_t − w_t + ρ_t`) and the solve
from its image (`ζ̂_t + r_(t+1) = ζ_t + r_t`). Then the jumps against the exact next rate
`w⁺_t = cζ_t − w_t` sum to `(w_0 − w_N) + (ρ_0 − ρ_N) + c(r_0 − r_N)`, however many ticks. -/
theorem rate_jumps_telescope (c : ℚ) (w ρ ζ ζhat r : ℕ → E → ℚ)
    (hw : ∀ t i, w (t + 1) i + ρ (t + 1) i = c * ζhat t i - w t i + ρ t i)
    (hζ : ∀ t i, ζhat t i + r (t + 1) i = ζ t i + r t i) (N : ℕ) (i : E) :
    ∑ t ∈ Finset.range N, (w t i - (c * ζ t i - w t i)) =
      (w 0 i - w N i) + (ρ 0 i - ρ N i) + c * (r 0 i - r N i) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    linear_combination hw N i + c * hζ N i

end Telescope

/-! ## 3. Two words at one representative -/

section TwoWords

variable {E : Type*}

/-- [proved-derived; formal-checked] **Equal representatives carry the image difference in the
remainder.** Two error-feedback streams from one starting remainder whose carried values agree at
coordinate `i` for every tick before `N` differ there by `r′_N − r_N = Σ_(t<N) (y′_t − y_t)`. -/
theorem feedback_remainder_difference (L : ℕ) (y y' : ℕ → E → ℚ) (r₀ : E → ℚ) (N : ℕ) (i : E)
    (hagree : ∀ t < N, fbOut L y' r₀ t i = fbOut L y r₀ t i) :
    fbRem L y' r₀ N i - fbRem L y r₀ N i = ∑ t ∈ Finset.range N, (y' t i - y t i) := by
  have h' := feedback_accounting L y' r₀ N i
  have h := feedback_accounting L y r₀ N i
  have hsum : ∑ t ∈ Finset.range N, fbOut L y' r₀ t i = ∑ t ∈ Finset.range N, fbOut L y r₀ t i :=
    Finset.sum_congr rfl fun t ht => hagree t (Finset.mem_range.mp ht)
  rw [Finset.sum_sub_distrib]
  linarith

/-- [proved-derived; formal-checked] **One accumulated unit forces the representatives apart.** If
the two streams' accumulated image difference at `i` reaches one lattice unit, their carried values
differ at some tick before `N`. Below one unit no parting is forced: the difference can sit in the
remainder. -/
theorem representatives_part_of_accumulated_unit (L : ℕ) (y y' : ℕ → E → ℚ) {r₀ : E → ℚ}
    (h₀ : ∀ i, -(unit L / 2) ≤ r₀ i ∧ r₀ i < unit L / 2) (N : ℕ) (i : E)
    (hreach : unit L ≤ |∑ t ∈ Finset.range N, (y' t i - y t i)|) :
    ∃ t < N, fbOut L y' r₀ t i ≠ fbOut L y r₀ t i := by
  by_contra hno
  push Not at hno
  have hd := feedback_remainder_difference L y y' r₀ N i hno
  have h1 := feedback_rem_bounds L y' h₀ N i
  have h2 := feedback_rem_bounds L y h₀ N i
  rw [← hd] at hreach
  have : |fbRem L y' r₀ N i - fbRem L y r₀ N i| < unit L := by
    rw [abs_lt]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  linarith

end TwoWords

/-! ## 4. The floor -/

section Floor

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- [proved-derived; formal-checked] **An operator `c + S` with `S ⪰ 0` shrinks an inverse image by
`c`**: `(c·1 + S)v = b` gives `c²|v|² ≤ |b|²`. From `⟨v, b⟩ = c|v|² + ⟨v, Sv⟩ ≥ c|v|²` and
`0 ≤ |b − cv|² = |b|² − 2c⟨v, b⟩ + c²|v|²`. The contact operator `m = 1 + (G/2h)(2C + hD + ½h²K)`
has `c = 1` at least; its least eigenvalue is the sharper `c`. -/
theorem le_of_margin_add_psd (S : Matrix n n ℚ) (hS : ∀ x, 0 ≤ x ⬝ᵥ (S *ᵥ x)) {c : ℚ}
    (hc : 0 ≤ c) (v b : n → ℚ) (h : (c • (1 : Matrix n n ℚ) + S) *ᵥ v = b) :
    c ^ 2 * (v ⬝ᵥ v) ≤ b ⬝ᵥ b := by
  have hvb : v ⬝ᵥ b = c * (v ⬝ᵥ v) + v ⬝ᵥ (S *ᵥ v) := by
    rw [← h, add_mulVec, smul_mulVec, one_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul]
  have hsq : 0 ≤ (b - c • v) ⬝ᵥ (b - c • v) :=
    Finset.sum_nonneg fun j _ => mul_self_nonneg _
  have hexp : (b - c • v) ⬝ᵥ (b - c • v) = b ⬝ᵥ b - 2 * c * (v ⬝ᵥ b) + c ^ 2 * (v ⬝ᵥ v) := by
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      dotProduct_comm b v]
    ring
  have hSv := hS v
  have hcv : 0 ≤ c * (v ⬝ᵥ (S *ᵥ v)) := mul_nonneg hc hSv
  nlinarith

/-- [proved-derived; formal-checked] **The storage floor.** With the deposited contact operator
`c·1 + S`, `S ⪰ 0`, `0 < c`, and the accumulated exact response `V` solving `(c·1 + S)V = ΔC J`
(`J` the telescoped rate jumps), `|ΔC J|² < c²u²` gives `|V_i| < u` at every coordinate: the
material response alone never forces the next passage's representative apart. -/
theorem storage_floor (S ΔC : Matrix n n ℚ) (hS : ∀ x, 0 ≤ x ⬝ᵥ (S *ᵥ x)) {c : ℚ} (hc : 0 < c)
    (V J : n → ℚ) (u : ℚ) (hu : 0 ≤ u) (h : (c • (1 : Matrix n n ℚ) + S) *ᵥ V = ΔC *ᵥ J)
    (hbelow : (ΔC *ᵥ J) ⬝ᵥ (ΔC *ᵥ J) < c ^ 2 * u ^ 2) (i : n) : |V i| < u := by
  have hle := le_of_margin_add_psd S hS hc.le V _ h
  have hi : V i * V i ≤ V ⬝ᵥ V :=
    Finset.single_le_sum (f := fun j => V j * V j) (fun j _ => mul_self_nonneg _)
      (Finset.mem_univ i)
  have hc2 : 0 < c ^ 2 := by positivity
  have hsq : V i ^ 2 < u ^ 2 := by
    have : c ^ 2 * V i ^ 2 < c ^ 2 * u ^ 2 := by nlinarith
    exact lt_of_mul_lt_mul_left this hc2.le
  exact abs_lt_of_sq_lt_sq hsq hu

end Floor

/-! ## 5. At held momentum

The within-refinement continuation holds the contact's momentum across its deposit, `C′w′ = Cw`
(the deposit record's law; `HolonicsResearch/HNN/MoveDirection.held_momentum_loss` reads its work).
The transit's right side then does not move, the deposit is felt through the motion `2ω = w + w⁺`,
the midpoints sum to the travel, and the rate's jump opens in the rate remainder. -/

section Held

variable {n : Type*} [Fintype n]

/-- [proved-derived; formal-checked] **The storage response at held momentum.** If `m ζ = b` and the
deposited operator `m + cΔC` solves the same right side (`2C′w′ = 2Cw`), then
`(m + cΔC)(ζ′ − ζ) = −ΔC(cζ)`: with `c = G/h`, `cζ = w + w⁺`, so the deposit acts on the motion
`2ω`, not on the rate's jump. -/
theorem held_storage_transit_response (m ΔC : Matrix n n ℚ) (c : ℚ) (b ζ ζ' : n → ℚ)
    (hζ : m *ᵥ ζ = b) (hζ' : (m + c • ΔC) *ᵥ ζ' = b) :
    (m + c • ΔC) *ᵥ (ζ' - ζ) = -(ΔC *ᵥ (c • ζ)) := by
  rw [mulVec_sub, hζ', add_mulVec, hζ, smul_mulVec, mulVec_smul]
  ext i
  simp only [Pi.sub_apply, Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
  ring

end Held

section Travel

variable {E : Type*}

/-- [proved-derived; formal-checked] **The midpoints sum to the travel.** The displacement is
carried by error feedback from `u_t + kζ̂_t` (`k = G/2`, so `kζ̂ = hω̂`) and the solve from its
image. Then `k Σ_(t<N) ζ_t = (u_N − u_0) + (σ_N − σ_0) + k(r_N − r_0)`. -/
theorem midpoint_sum_is_travel (k : ℚ) (u σ ζ ζhat r : ℕ → E → ℚ)
    (hu : ∀ t i, u (t + 1) i + σ (t + 1) i = u t i + k * ζhat t i + σ t i)
    (hζ : ∀ t i, ζhat t i + r (t + 1) i = ζ t i + r t i) (N : ℕ) (i : E) :
    k * ∑ t ∈ Finset.range N, ζ t i =
      (u N i - u 0 i) + (σ N i - σ 0 i) + k * (r N i - r 0 i) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    linear_combination -(hu N i) - k * hζ N i

end Travel

section Openings

variable {E : Type*}

/-- [proved-derived; formal-checked] **Two streams from different openings.** Two error-feedback
streams whose carried values agree at `i` before `N` differ there by their openings' difference plus
the accumulated image difference: `r′_N − r_N = (r′_0 − r_0) + Σ_(t<N)(y′_t − y_t)`. -/
theorem feedback_remainder_difference_of_openings (L : ℕ) (y y' : ℕ → E → ℚ) (r₀ r₀' : E → ℚ)
    (N : ℕ) (i : E) (hagree : ∀ t < N, fbOut L y' r₀' t i = fbOut L y r₀ t i) :
    fbRem L y' r₀' N i - fbRem L y r₀ N i =
      (r₀' i - r₀ i) + ∑ t ∈ Finset.range N, (y' t i - y t i) := by
  have h' := feedback_accounting L y' r₀' N i
  have h := feedback_accounting L y r₀ N i
  have hsum : ∑ t ∈ Finset.range N, fbOut L y' r₀' t i =
      ∑ t ∈ Finset.range N, fbOut L y r₀ t i :=
    Finset.sum_congr rfl fun t ht => hagree t (Finset.mem_range.mp ht)
  rw [Finset.sum_sub_distrib]
  linarith

end Openings

#print axioms held_storage_transit_response
#print axioms midpoint_sum_is_travel
#print axioms feedback_remainder_difference_of_openings

end Holonics.HNN.StorageResolution
