import Holonics.HNN.Retention
import Mathlib.Algebra.Order.Round
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Lemmas
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Order.Interval.Finset.SuccPred

/-!
# HNN.LatticeDeposit: the carrier lattice, with a release budgeted since the locus's founding

[definition; agent-inferred] Item 4 of the step 4 design (`docs/plans/THE_REBUILD.md`, "The laws
stated in Lean first"), amended twice. Exact rational deposition compounds: the maps that form
each other's covectors (`E`, `R`, `W_c` through the word's inverses) feed their own denominators
back into the next deposit. CLAUDE.md's exact-representation law says what to do: "When a value
outgrows its carrier, it is rebased, factored or re-represented with its decoder and residual."
With the Ratio's division with remainder (`div_rem`, `docs/ELEMENTARY_OBJECTS.md`) and the carry
cocycle (`Geometry/PhaseCarry.carry_cocycle`: helix = circle + carry, the lattice coordinate the
winding and the remainder its phase), every entry of a locus `ℓ` lives on its declared lattice
`2^(−L_ℓ)ℤ` with a carried remainder. The first amendment carried the exact remainder and
released it at the aeon collapse. That fails twice: the remainder's magnitude is bounded but its
denominator accumulates every update's, and an aeon (a first-passage time of the joint clock's
carry chain) has no upper bound, so no bit bound can be keyed to it; and the releases add across
aeons without bound, so the word drifts from the exact accumulation of what reached the locus.

The retention law applied to the whole admitted future fixes both: the total released since a
locus's founding stays below the one-unit deviation the lattice rule certifies
(`remainder_below_grain`).
With the locus's deposit clock `m` (the count of epochs at the locus's section: the deposits that
reached it with a nonzero update, from the locus's founding, the field's mount or a later founding;
not reset at an aeon boundary, and ending when the collapse releases the locus whole) and the
Elias-gamma length of `m` (the field's own natural code) as the precision:

```text
u = 2^(−L) ,  k_m = 2⌊log₂ m⌋ + 1
y   = Δ + r_prev                                   exact
y   = y_f + e ,   y_f ∈ 2^(−L−k_m)ℤ nearest, ties upward ,   e ∈ [−½·2^(−L−k_m), ½·2^(−L−k_m))
y_f = q u + r ,   q nearest, ties upward ,   r ∈ [−u/2, u/2) ∩ 2^(−L−k_m)ℤ
value += q u ;  carry r ;  release e (reported exactly in the deposit's reading)
```

The nested lattices `2^(−L−k_m)ℤ` are a tower whose thread refines with the clock; the remainder is
the error feedback, and only its Kraft tail is released. Since `Σ_m 2^(−k_m) < 1`, the releases
since the locus's founding sum to less than `u/2`, and the word always reads within one unit of
the exact accumulation. `Δ` is the exact update of the locus's law (`HNN/Normal`) computed at the
lattice-valued operands; no float enters. Brandon may override this choice.

[open] The pre-rebuild precedent, `Objects/CommitRebase.commit_chain_residual`, is the
counterfactual bound: how far the carried trajectory is from the one whose updates are computed at
the exact (never rounded) operands, `Σ_(i<n) K^(n−1−i) r_i` for a Lipschitz bound `K` of the deposit
map. No such `K` is stated for the HNN's deposit, so that bound remains owed. What is proved here is
the accounting against the updates that actually reached the locus; the pre-reset rebase dropped a
radius at every commit with no carry, and its "sum of dropped radii" was no trajectory bound
(history's `IncidentRebaseResidual`). Here the remainder is carried and the released radii sum
below `u/2` since the locus's founding.

[proved-derived; formal-checked] What is proved.

1. **Division with remainder at the nearest point** (`div_rem_spec`, `rem_bounds`): `x = q u + r`
   with `−u/2 ≤ r < u/2`, and a remainder alone divides to zero (`quot_eq_zero_of_bounds`).
2. **Budgeted accounting** (`carry_accounting`, `run_accounting`, `lattice_deposit_accounting`):
   for any sequence of updates, the applied lattice steps plus the carried remainder plus the
   released residuals equal the exact sum of the updates, entry by entry. Lattice values stay on
   the lattice (`run_onLattice`).
3. **The remainder** is bounded (`carried_remainder_bounded`, `|r| ≤ 2^(−L−1)`) and lies on the
   fine lattice of its clock (`Carried.rem_fine`), so `r·2^(L+k_m)` is an integer of magnitude at
   most `2^(k_m−1)` (`remainder_numerator_bounded`) and the reduced remainder takes at most
   `L + 2k_m + 1` bits (`remainder_rat_bits_bounded`): `O(L + log m)`.
4. **The release** at one deposit is at most `½·2^(−L−k_m)` (`release_bounded`); the Elias-gamma
   lengths satisfy Kraft, `Σ_(m=1..M) 2^(−(2⌊log₂ m⌋+1)) < 1` (`gamma_kraft_lt_one`: blocks of
   `2^j` terms of `2^(−(2j+1))` sum to `2^(−(j+1))`), so the releases of any run sum to less than
   `u/2` (`release_bounded_since_founding`) and every value stays within one unit of the exact
   accumulation since the locus's founding (`within_one_unit_since_founding`). By
   `remainder_below_grain` one unit per entry moves a read by at most `2^(−L)` times the
   operand's ℓ1 norm, so under the lattice rule `2 L_R X ≤ 2^L` by at most `1/(2 L_R)`, below the
   receiver's grain.
5. **The carried Gram stays positive definite** (`carried_gram_posDef`,
   `carried_gram_posDef_rule`): every entry of a carried Gram is within one unit of the exact
   Gram `H_exact ⪰ I`, so `|vᵀ(H − H_exact)v| ≤ u(Σ|v_i|)² ≤ n·u·|v|²`, and under the lattice rule
   with the Gram width `n ≤ X_ℓ`, `H ⪰ (1 − 1/(2L_R)) I` since the locus's founding, with no clamp.
6. **A zero update moves nothing** (`carry_zero`: the whole locus, clock included;
   `carry_entry_zero`: an entry whose update is zero inside a nonzero deposit keeps its value and
   remainder and releases nothing, because its remainder already lies on the coarser fine lattice
   of an earlier clock).
7. **Bits** (`lattice_entry_bits`, `lattice_bits_bounded`, `lattice_rat_bits_bounded`): a lattice
   entry of magnitude at most `M` has an integer coordinate of at most `⌈log₂(⌊M·2^L⌋ + 1)⌉` bits,
   and so at most `⌈log₂(⌊M·2^L⌋ + 1)⌉ + 1` with its sign; as a reduced rational (the Rust count,
   numerator and denominator), at most `⌈log₂(⌊M·2^L⌋ + 1)⌉ + L + 1` bits.
8. **Descent** (`lattice_deposit_descends`): the carried locus reads only its lattice value and an
   empty window's update is zero, so by `carry_zero` `HNN/Retention.deposit_descends` applies
   verbatim: the budgeted deposit agrees with or without the collapse. The aeon collapse releases
   only exact complements, and a carried remainder is not one (releasing it could move a later
   lattice value by a unit, and so a later admitted reading), so it releases no remainder of a
   retained locus and resets no clock; a locus it releases leaves whole.

[established-bounded; measured] The measured bits per deposit (entries, remainders, solved charts
and released residuals) are in `research/notebook/hnn_design/README.md` (`hnn_lattice_growth`).

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.HNN.LatticeDeposit

/-! ## 1. Division with remainder at the nearest lattice point -/

/-- [definition] The unit `2^(−L)` of the lattice `2^(−L)ℤ`. -/
def unit (L : ℕ) : ℚ := ((2 : ℚ) ^ L)⁻¹

theorem unit_pos (L : ℕ) : 0 < unit L := by
  unfold unit
  positivity

/-- A coarse unit is `2^k` fine units: `2^(−L) = 2^k·2^(−L−k)`. -/
theorem unit_eq_pow_mul (L k : ℕ) : unit L = 2 ^ k * unit (L + k) := by
  unfold unit
  rw [pow_add]
  field_simp

/-- [definition] `x` lies on the lattice `2^(−L)ℤ`. -/
def OnLattice (L : ℕ) (x : ℚ) : Prop := ∃ q : ℤ, x = q * unit L

/-- The lattices are nested: `2^(−a)ℤ ⊆ 2^(−b)ℤ` for `a ≤ b`. -/
theorem OnLattice.mono {a b : ℕ} {x : ℚ} (h : OnLattice a x) (hab : a ≤ b) : OnLattice b x := by
  obtain ⟨q, hq⟩ := h
  refine ⟨q * 2 ^ (b - a), ?_⟩
  rw [hq, unit_eq_pow_mul a (b - a), Nat.add_sub_cancel' hab]
  push_cast
  ring

/-- [definition] **The quotient**: the nearest lattice point's coordinate, ties upward. -/
def quot (L : ℕ) (x : ℚ) : ℤ := round (x / unit L)

/-- [definition] **The remainder** of the nearest-point division. -/
def rem (L : ℕ) (x : ℚ) : ℚ := x - quot L x * unit L

/-- [proved-derived; formal-checked] `x = q·2^(−L) + r`. -/
theorem div_rem_spec (L : ℕ) (x : ℚ) : x = quot L x * unit L + rem L x := by
  unfold rem
  ring

/-- [proved-derived; formal-checked] **The remainder lies in the half-open cell**
`−2^(−L−1) ≤ r < 2^(−L−1)`. -/
theorem rem_bounds (L : ℕ) (x : ℚ) : -(unit L / 2) ≤ rem L x ∧ rem L x < unit L / 2 := by
  have hu := unit_pos L
  have h1 := Int.floor_le (x / unit L + 1 / 2)
  have h2 := Int.lt_floor_add_one (x / unit L + 1 / 2)
  have key : rem L x = (x / unit L - (⌊x / unit L + 1 / 2⌋ : ℚ)) * unit L := by
    unfold rem quot
    rw [round_eq]
    field_simp
  rw [key]
  constructor
  · have ht : -(1 / 2 : ℚ) ≤ x / unit L - ⌊x / unit L + 1 / 2⌋ := by linarith
    nlinarith
  · have ht : x / unit L - ⌊x / unit L + 1 / 2⌋ < 1 / 2 := by linarith
    nlinarith

/-- [proved-derived; formal-checked] **A remainder alone divides to zero**: the upward tie rule
keeps `−u/2` in its own cell. -/
theorem quot_eq_zero_of_bounds {L : ℕ} {r : ℚ} (h : -(unit L / 2) ≤ r ∧ r < unit L / 2) :
    quot L r = 0 := by
  have hu := unit_pos L
  unfold quot
  rw [round_eq, Int.floor_eq_iff]
  have hlo : -(1 / 2 : ℚ) ≤ r / unit L := by
    rw [le_div_iff₀ hu]
    linarith [h.1]
  have hhi : r / unit L < 1 / 2 := by
    rw [div_lt_iff₀ hu]
    linarith [h.2]
  push_cast
  constructor <;> linarith

/-- A lattice point divides exactly: its remainder is zero. -/
theorem rem_of_onLattice {L : ℕ} {x : ℚ} (h : OnLattice L x) : rem L x = 0 := by
  obtain ⟨q, rfl⟩ := h
  have hu := (unit_pos L).ne'
  unfold rem quot
  rw [mul_div_cancel_right₀ _ hu, round_intCast]
  ring

/-! ## 2. The Elias-gamma precision and its Kraft sum -/

/-- [definition] **The precision at clock `m`**: the Elias-gamma length `k_m = 2⌊log₂ m⌋ + 1`. -/
def gammaLength (m : ℕ) : ℕ := 2 * Nat.log 2 m + 1

theorem one_le_gammaLength (m : ℕ) : 1 ≤ gammaLength m := by
  unfold gammaLength
  omega

theorem gammaLength_mono {a b : ℕ} (h : a ≤ b) : gammaLength a ≤ gammaLength b := by
  unfold gammaLength
  have := Nat.log_mono_right (b := 2) h
  omega

/-- [definition] Its weight `2^(−k_m)`. -/
def gammaWeight (m : ℕ) : ℚ := ((2 : ℚ) ^ gammaLength m)⁻¹

theorem gammaWeight_nonneg (m : ℕ) : 0 ≤ gammaWeight m := by
  unfold gammaWeight
  positivity

/-- The fine lattice's half-unit is the coarse half-unit times the weight. -/
theorem half_fine_unit (L m : ℕ) : unit (L + gammaLength m) / 2 = unit L / 2 * gammaWeight m := by
  unfold unit gammaWeight
  rw [pow_add]
  field_simp

/-- One block: the `2^j` clocks of `[2^j, 2^(j+1))` share `k = 2j + 1`, and weigh `2^(−(j+1))`. -/
theorem gamma_block (j : ℕ) :
    ∑ m ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)), gammaWeight m = ((2 : ℚ) ^ (j + 1))⁻¹ := by
  have hconst : ∀ m ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)),
      gammaWeight m = ((2 : ℚ) ^ (2 * j + 1))⁻¹ := by
    intro m hm
    rw [Finset.mem_Ico] at hm
    unfold gammaWeight gammaLength
    rw [Nat.log_eq_of_pow_le_of_lt_pow hm.1 hm.2]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
  have hcard : 2 ^ (j + 1) - 2 ^ j = 2 ^ j := by
    rw [pow_succ]
    omega
  rw [hcard]
  push_cast
  have hsplit : (2 : ℚ) ^ (2 * j + 1) = 2 ^ j * 2 ^ (j + 1) := by
    rw [← pow_add]
    ring_nf
  rw [hsplit]
  field_simp

/-- The clocks below `2^J` weigh `1 − 2^(−J)`. -/
theorem gamma_prefix (J : ℕ) :
    ∑ m ∈ Finset.Ico 1 (2 ^ J), gammaWeight m = 1 - ((2 : ℚ) ^ J)⁻¹ := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [← Finset.sum_Ico_consecutive _ (Nat.one_le_two_pow)
      (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ J)), ih, gamma_block]
    rw [pow_succ]
    field_simp
    ring

/-- [proved-derived; formal-checked] **`gamma_kraft_lt_one`.** The Elias-gamma lengths satisfy
Kraft strictly: `Σ_(m=1..M) 2^(−(2⌊log₂ m⌋+1)) < 1` for every `M`. -/
theorem gamma_kraft_lt_one (M : ℕ) : ∑ m ∈ Finset.Icc 1 M, gammaWeight m < 1 := by
  have hM : M < 2 ^ (Nat.log 2 M + 1) := Nat.lt_pow_succ_log_self (by norm_num) M
  have hpos : (0 : ℚ) < ((2 : ℚ) ^ (Nat.log 2 M + 1))⁻¹ := by positivity
  calc ∑ m ∈ Finset.Icc 1 M, gammaWeight m
      ≤ ∑ m ∈ Finset.Ico 1 (2 ^ (Nat.log 2 M + 1)), gammaWeight m :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Ico_right hM)
          (fun m _ _ => gammaWeight_nonneg m)
    _ = 1 - ((2 : ℚ) ^ (Nat.log 2 M + 1))⁻¹ := gamma_prefix _
    _ < 1 := by linarith

/-- Any window of clocks weighs less than one. -/
theorem gamma_window_lt_one (a b : ℕ) : ∑ m ∈ Finset.Ioc a b, gammaWeight m < 1 := by
  calc ∑ m ∈ Finset.Ioc a b, gammaWeight m ≤ ∑ m ∈ Finset.Ioc 0 b, gammaWeight m :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ioc_subset_Ioc_left (Nat.zero_le a))
          (fun m _ _ => gammaWeight_nonneg m)
    _ = ∑ m ∈ Finset.Icc 1 b, gammaWeight m := by
        rw [← Finset.Icc_succ_left_eq_Ioc]
        rfl
    _ < 1 := gamma_kraft_lt_one b

/-! ## 3. The budgeted carry and its accounting -/

/-- [definition] **A lattice-carried locus**: its entries (indexed by `E`), their carried
remainders, each in its half-open cell and on the fine lattice of the locus's deposit clock, and
the clock (the count of epochs at the locus's section: the deposits that reached it with a nonzero
update since its founding, not reset at an aeon boundary). -/
@[ext]
structure Carried (L : ℕ) (E : Type*) where
  value : E → ℚ
  rem : E → ℚ
  clock : ℕ
  rem_bounded : ∀ i, -(unit L / 2) ≤ rem i ∧ rem i < unit L / 2
  rem_fine : ∀ i, OnLattice (L + gammaLength clock) (rem i)

variable {L : ℕ} {E : Type*}

/-- [definition] A founding carrier: the given entries, no remainder, clock zero. -/
def Carried.fresh (value : E → ℚ) : Carried L E where
  value := value
  rem := 0
  clock := 0
  rem_bounded _ := by
    have hu := unit_pos L
    simp only [Pi.zero_apply]
    constructor <;> linarith
  rem_fine _ := ⟨0, by simp⟩

/-- [definition] The fine point: `y` at the nearest point of `2^(−L−k)ℤ`, ties upward. -/
def fine (L k : ℕ) (y : ℚ) : ℚ := quot (L + k) y * unit (L + k)

/-- [definition] **The budgeted step** of a nonzero update: the clock advances to `m`; `Δ + r_prev`
is split at the fine lattice `2^(−L−k_m)ℤ` (the release), and its fine point at the coarse lattice
(the applied step and the carried remainder). -/
def step (s : Carried L E) (Δ : E → ℚ) : Carried L E where
  value i := s.value i + quot L (fine L (gammaLength (s.clock + 1)) (Δ i + s.rem i)) * unit L
  rem i := rem L (fine L (gammaLength (s.clock + 1)) (Δ i + s.rem i))
  clock := s.clock + 1
  rem_bounded _ := rem_bounds L _
  rem_fine i := by
    set k := gammaLength (s.clock + 1)
    refine ⟨quot (L + k) (Δ i + s.rem i) - quot L (fine L k (Δ i + s.rem i)) * 2 ^ k, ?_⟩
    unfold rem fine
    rw [unit_eq_pow_mul L k]
    push_cast
    ring

open Classical in
/-- [definition] **One budgeted deposit** of the exact update `Δ`: the step when `Δ ≠ 0`, nothing
(the clock included) when `Δ = 0`. -/
noncomputable def carry (s : Carried L E) (Δ : E → ℚ) : Carried L E :=
  if Δ = 0 then s else step s Δ

open Classical in
/-- [definition] **The released residual** `e` of one deposit at an entry, reported exactly. -/
noncomputable def release (s : Carried L E) (Δ : E → ℚ) (i : E) : ℚ :=
  if Δ = 0 then 0 else rem (L + gammaLength (s.clock + 1)) (Δ i + s.rem i)

/-- [definition] A run of budgeted deposits over a sequence of exact updates. -/
noncomputable def run (s : Carried L E) (Δs : List (E → ℚ)) : Carried L E := Δs.foldl carry s

/-- [definition] The residuals a run releases at an entry, summed. -/
noncomputable def released : Carried L E → List (E → ℚ) → E → ℚ
  | _, [], _ => 0
  | s, Δ :: Δs, i => release s Δ i + released (carry s Δ) Δs i

/-- [proved-derived; formal-checked] **`carry_zero`.** A zero update leaves the locus: value,
remainder and clock. -/
theorem carry_zero (s : Carried L E) : carry s 0 = s := by
  simp [carry]

theorem release_zero (s : Carried L E) (i : E) : release s 0 i = 0 := by
  simp [release]

theorem carry_clock (s : Carried L E) (Δ : E → ℚ) :
    s.clock ≤ (carry s Δ).clock ∧ (carry s Δ).clock ≤ s.clock + 1 := by
  by_cases hΔ : Δ = 0
  · simp [carry, hΔ]
  · simp only [carry, if_neg hΔ, step]
    omega

theorem carry_clock_of_ne {s : Carried L E} {Δ : E → ℚ} (hΔ : Δ ≠ 0) :
    (carry s Δ).clock = s.clock + 1 := by
  simp [carry, hΔ, step]

theorem run_clock_ge (s : Carried L E) (Δs : List (E → ℚ)) : s.clock ≤ (run s Δs).clock := by
  induction Δs generalizing s with
  | nil => simp [run]
  | cons Δ Δs ih =>
    simp only [run, List.foldl_cons] at ih ⊢
    exact (carry_clock s Δ).1.trans (ih (carry s Δ))

/-- [proved-derived; formal-checked] **One deposit's accounting**: the applied step, the carried
remainder and the released residual together move `value + rem` by exactly `Δ`. -/
theorem carry_accounting (s : Carried L E) (Δ : E → ℚ) (i : E) :
    (carry s Δ).value i + (carry s Δ).rem i + release s Δ i = s.value i + s.rem i + Δ i := by
  by_cases hΔ : Δ = 0
  · subst hΔ
    simp [carry, release]
  · simp only [carry, release, if_neg hΔ, step]
    have h1 := div_rem_spec (L + gammaLength (s.clock + 1)) (Δ i + s.rem i)
    have h2 := div_rem_spec L (fine L (gammaLength (s.clock + 1)) (Δ i + s.rem i))
    unfold fine at h2 ⊢
    linarith

/-- [proved-derived; formal-checked] **Accounting from any carrier**: after any sequence, the
applied steps plus the carried remainder plus the released residuals equal the exact sum of the
updates plus the starting remainder. -/
theorem run_accounting (s : Carried L E) (Δs : List (E → ℚ)) (i : E) :
    ((run s Δs).value i - s.value i) + (run s Δs).rem i + released s Δs i =
      (Δs.map (· i)).sum + s.rem i := by
  induction Δs generalizing s with
  | nil => simp [run, released]
  | cons Δ Δs ih =>
    have hstep := carry_accounting s Δ i
    have hrest := ih (carry s Δ)
    simp only [run, List.foldl_cons] at hrest ⊢
    simp only [released, List.map_cons, List.sum_cons]
    linarith

/-- [proved-derived; formal-checked] **`lattice_deposit_accounting`.** From a founding carrier, for
any sequence of exact updates, the applied lattice steps plus the carried remainder plus the
released residuals equal the exact sum of the updates: nothing is rounded away unreported. -/
theorem lattice_deposit_accounting (value : E → ℚ) (Δs : List (E → ℚ)) (i : E) :
    ((run (Carried.fresh (L := L) value) Δs).value i - value i) +
        (run (Carried.fresh (L := L) value) Δs).rem i +
        released (Carried.fresh (L := L) value) Δs i = (Δs.map (· i)).sum := by
  have := run_accounting (Carried.fresh (L := L) value) Δs i
  simpa [Carried.fresh] using this

/-- [proved-derived; formal-checked] A lattice entry stays on the lattice under a deposit. -/
theorem carry_onLattice (s : Carried L E) (Δ : E → ℚ) {i : E} (h : OnLattice L (s.value i)) :
    OnLattice L ((carry s Δ).value i) := by
  by_cases hΔ : Δ = 0
  · simpa [carry, hΔ] using h
  · obtain ⟨q, hq⟩ := h
    refine ⟨q + quot L (fine L (gammaLength (s.clock + 1)) (Δ i + s.rem i)), ?_⟩
    simp only [carry, if_neg hΔ, step, hq]
    push_cast
    ring

/-- [proved-derived; formal-checked] Lattice entries stay on the lattice over any run. -/
theorem run_onLattice (s : Carried L E) (Δs : List (E → ℚ)) {i : E}
    (h : OnLattice L (s.value i)) : OnLattice L ((run s Δs).value i) := by
  induction Δs generalizing s with
  | nil => simpa [run] using h
  | cons Δ Δs ih =>
    simp only [run, List.foldl_cons]
    exact ih (carry s Δ) (carry_onLattice s Δ h)

/-- [proved-derived; formal-checked] **`carry_entry_zero`.** An entry whose update is zero keeps
its value and remainder and releases nothing, even when the deposit moves other entries: its
remainder lies on the fine lattice of an earlier clock, which the refined lattice contains. -/
theorem carry_entry_zero (s : Carried L E) (Δ : E → ℚ) {i : E} (h : Δ i = 0) :
    (carry s Δ).value i = s.value i ∧ (carry s Δ).rem i = s.rem i ∧ release s Δ i = 0 := by
  by_cases hΔ : Δ = 0
  · simp [carry, release, hΔ]
  · set k := gammaLength (s.clock + 1)
    have hfine : OnLattice (L + k) (s.rem i) :=
      (s.rem_fine i).mono (Nat.add_le_add_left (gammaLength_mono (Nat.le_succ _)) L)
    have hzero : rem (L + k) (s.rem i) = 0 := rem_of_onLattice hfine
    have hpoint : fine L k (s.rem i) = s.rem i := by
      have := div_rem_spec (L + k) (s.rem i)
      unfold fine
      linarith
    have hq : quot L (s.rem i) = 0 := quot_eq_zero_of_bounds (s.rem_bounded i)
    simp only [carry, release, if_neg hΔ, step, h, zero_add]
    refine ⟨?_, ?_, hzero⟩
    · rw [hpoint, hq]
      simp
    · rw [hpoint]
      unfold rem
      rw [hq]
      simp

/-! ## 4. The remainder's bound and bits -/

/-- [proved-derived; formal-checked] **`carried_remainder_bounded`**: after any sequence of
deposits the carried remainder satisfies `|r| ≤ 2^(−L−1)`. -/
theorem carried_remainder_bounded (s : Carried L E) (Δs : List (E → ℚ)) (i : E) :
    |(run s Δs).rem i| ≤ ((2 : ℚ) ^ (L + 1))⁻¹ := by
  have h := (run s Δs).rem_bounded i
  have hhalf : unit L / 2 = ((2 : ℚ) ^ (L + 1))⁻¹ := by
    unfold unit
    rw [pow_succ]
    field_simp
  rw [abs_le]
  constructor <;> linarith [h.1, h.2]

/-- [proved-derived; formal-checked] **`remainder_numerator_bounded`.** A carried remainder at
clock `m` is `z·2^(−L−k_m)` with `|z| ≤ 2^(k_m−1)`, so `z` takes at most `k_m` bits. -/
theorem remainder_numerator_bounded (s : Carried L E) (i : E) :
    ∃ z : ℤ, s.rem i = z * unit (L + gammaLength s.clock) ∧
      |z| ≤ 2 ^ (gammaLength s.clock - 1) ∧ Nat.size z.natAbs ≤ gammaLength s.clock := by
  obtain ⟨z, hz⟩ := s.rem_fine i
  set k := gammaLength s.clock
  have hk : 1 ≤ k := one_le_gammaLength _
  have hb := s.rem_bounded i
  have hu := unit_pos (L + k)
  have hhalf : unit L / 2 = 2 ^ (k - 1) * unit (L + k) := by
    have h2 : (2 : ℚ) ^ k = 2 * 2 ^ (k - 1) := by
      rw [← pow_succ']
      congr 1
    rw [unit_eq_pow_mul L k, h2]
    ring
  rw [hhalf, hz] at hb
  have hlo : -(2 ^ (k - 1) : ℚ) ≤ z := by
    have := hb.1
    nlinarith
  have hhi : (z : ℚ) < 2 ^ (k - 1) := by
    have := hb.2
    nlinarith
  have habs : |z| ≤ 2 ^ (k - 1) := by
    rw [abs_le]
    constructor
    · exact_mod_cast hlo
    · exact_mod_cast hhi.le
  refine ⟨z, hz, habs, ?_⟩
  rw [Nat.size_le]
  have h1 : z.natAbs ≤ 2 ^ (k - 1) := by
    have : ((z.natAbs : ℕ) : ℤ) ≤ ((2 ^ (k - 1) : ℕ) : ℤ) := by
      rw [Int.natCast_natAbs]
      push_cast
      exact habs
    exact_mod_cast this
  calc z.natAbs ≤ 2 ^ (k - 1) := h1
    _ < 2 ^ k := Nat.pow_lt_pow_right (by norm_num) (by omega)

/-- [proved-derived; formal-checked] **`remainder_rat_bits_bounded`.** As a reduced rational
(numerator and denominator, the Rust count), a carried remainder at clock `m` takes at most
`L + 2k_m + 1` bits: `O(L + log m)`. -/
theorem remainder_rat_bits_bounded (s : Carried L E) (i : E) :
    Nat.size (s.rem i).num.natAbs + Nat.size (s.rem i).den ≤
      L + 2 * gammaLength s.clock + 1 := by
  obtain ⟨z, hz, -, hsize⟩ := remainder_numerator_bounded s i
  set k := gammaLength s.clock
  have hx : s.rem i = Rat.divInt z (2 ^ (L + k)) := by
    rw [hz, Rat.divInt_eq_div]
    unfold unit
    push_cast
    ring
  have hden : Nat.size (s.rem i).den ≤ L + k + 1 := by
    rw [Nat.size_le]
    have hd := Rat.den_dvd z (2 ^ (L + k))
    rw [← hx] at hd
    have hle : ((s.rem i).den : ℤ) ≤ 2 ^ (L + k) := Int.le_of_dvd (by positivity) hd
    have : (s.rem i).den ≤ 2 ^ (L + k) := by exact_mod_cast hle
    calc (s.rem i).den ≤ 2 ^ (L + k) := this
      _ < 2 ^ (L + k + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hnum : Nat.size (s.rem i).num.natAbs ≤ k := by
    by_cases hzero : z = 0
    · have : s.rem i = 0 := by rw [hz, hzero]; simp
      rw [this]
      simp
    · refine le_trans (Nat.size_le_size ?_) hsize
      have hd := Rat.num_dvd z (by positivity : (2 : ℤ) ^ (L + k) ≠ 0)
      rw [← hx] at hd
      exact Nat.le_of_dvd (Int.natAbs_pos.mpr hzero) (Int.natAbs_dvd_natAbs.mpr hd)
  omega

/-! ## 5. The release: per deposit and since the locus's founding -/

/-- [proved-derived; formal-checked] **`release_bounded`.** One deposit releases at most
`½·2^(−L−k_m)` at an entry, `m` the clock it advances to. -/
theorem release_bounded (s : Carried L E) (Δ : E → ℚ) (i : E) :
    |release s Δ i| ≤ unit (L + gammaLength (s.clock + 1)) / 2 := by
  have hu := unit_pos (L + gammaLength (s.clock + 1))
  by_cases hΔ : Δ = 0
  · simp only [release, if_pos hΔ, abs_zero]
    positivity
  · simp only [release, if_neg hΔ]
    have hb := rem_bounds (L + gammaLength (s.clock + 1)) (Δ i + s.rem i)
    rw [abs_le]
    constructor <;> linarith [hb.1, hb.2]

/-- The releases of a run are bounded by the weights of the clocks it advanced through. -/
theorem released_le (s : Carried L E) (Δs : List (E → ℚ)) (i : E) :
    |released s Δs i| ≤ unit L / 2 * ∑ m ∈ Finset.Ioc s.clock (run s Δs).clock, gammaWeight m := by
  induction Δs generalizing s with
  | nil => simp [released, run]
  | cons Δ Δs ih =>
    have hrest := ih (carry s Δ)
    have hrun : run s (Δ :: Δs) = run (carry s Δ) Δs := rfl
    simp only [released, hrun]
    by_cases hΔ : Δ = 0
    · subst hΔ
      rw [release_zero, zero_add, carry_zero] at *
      exact hrest
    · have hclock := carry_clock_of_ne (s := s) hΔ
      have hge := run_clock_ge (carry s Δ) Δs
      rw [hclock] at hrest hge
      have hone := release_bounded s Δ i
      rw [half_fine_unit] at hone
      have hsplit : ∑ m ∈ Finset.Ioc s.clock (run (carry s Δ) Δs).clock, gammaWeight m =
          gammaWeight (s.clock + 1) +
            ∑ m ∈ Finset.Ioc (s.clock + 1) (run (carry s Δ) Δs).clock, gammaWeight m := by
        rw [← Finset.sum_Ioc_consecutive _ (Nat.le_succ s.clock) hge, Nat.Ioc_succ_singleton,
          Finset.sum_singleton]
      rw [hsplit, mul_add]
      calc |release s Δ i + released (carry s Δ) Δs i|
          ≤ |release s Δ i| + |released (carry s Δ) Δs i| := abs_add_le _ _
        _ ≤ _ := add_le_add hone hrest

/-- [proved-derived; formal-checked] **`release_bounded_since_founding`.** Over any run, from any
carrier (from the locus's founding in particular), the residuals released at an entry sum to less
than half a unit: the Kraft tail. -/
theorem release_bounded_since_founding (s : Carried L E) (Δs : List (E → ℚ)) (i : E) :
    |released s Δs i| < unit L / 2 := by
  have hu : 0 < unit L / 2 := by have := unit_pos L; positivity
  calc |released s Δs i| ≤ unit L / 2 * ∑ m ∈ Finset.Ioc s.clock (run s Δs).clock, gammaWeight m :=
        released_le s Δs i
    _ < unit L / 2 * 1 := mul_lt_mul_of_pos_left (gamma_window_lt_one _ _) hu
    _ = unit L / 2 := mul_one _

/-- [proved-derived; formal-checked] **`within_one_unit_since_founding`.** After any run from the
locus's founding, every value is within one lattice unit of the exact accumulation of what reached
the entry (its starting value and remainder plus the exact updates): the carried remainder is at
most half a unit, and the releases since the founding less than half. -/
theorem within_one_unit_since_founding (s : Carried L E) (Δs : List (E → ℚ)) (i : E) :
    |(run s Δs).value i - (s.value i + s.rem i + (Δs.map (· i)).sum)| < unit L := by
  have hacc := run_accounting s Δs i
  have hrel := release_bounded_since_founding s Δs i
  have hb := (run s Δs).rem_bounded i
  have heq : (run s Δs).value i - (s.value i + s.rem i + (Δs.map (· i)).sum) =
      -((run s Δs).rem i + released s Δs i) := by linarith
  rw [heq, abs_neg]
  rw [abs_lt] at hrel ⊢
  constructor <;> linarith [hb.1, hb.2, hrel.1, hrel.2]

/-- [proved-derived; formal-checked] **`remainder_below_grain`.** A displacement of at most one
lattice unit per entry (the deviation since the founding, `within_one_unit_since_founding`)
moves a read of its locus by at most `2^(−L)` times the operand's ℓ1 norm; under the lattice rule `2 L_R X ≤ 2^L` (the
operand's ℓ1 norm at most `X`) that is at most `1/(2 L_R)`, below the receiver's grain `1/L_R`. -/
theorem remainder_below_grain {ι : Type*} (s : Finset ι) (r x : ι → ℚ) {LR : ℕ} {X : ℚ}
    (hLR : 0 < LR) (hr : ∀ i ∈ s, |r i| ≤ unit L)
    (hx : ∑ i ∈ s, |x i| ≤ X) (hL : 2 * LR * X ≤ 2 ^ L) :
    |∑ i ∈ s, r i * x i| ≤ 1 / (2 * LR) ∧ |∑ i ∈ s, r i * x i| < 1 / LR := by
  have hpow : (0 : ℚ) < 2 ^ L := by positivity
  have hLRq : (0 : ℚ) < LR := by exact_mod_cast hLR
  have hsum : |∑ i ∈ s, r i * x i| ≤ unit L * X := by
    calc |∑ i ∈ s, r i * x i| ≤ ∑ i ∈ s, |r i * x i| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i ∈ s, |r i| * |x i| := by simp only [abs_mul]
      _ ≤ ∑ i ∈ s, unit L * |x i| :=
          Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right (hr i hi) (abs_nonneg _)
      _ = unit L * ∑ i ∈ s, |x i| := by rw [Finset.mul_sum]
      _ ≤ unit L * X := mul_le_mul_of_nonneg_left hx (unit_pos L).le
  have hX : X ≤ 2 ^ L / (2 * LR) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hbound : unit L * X ≤ 1 / (2 * LR) := by
    calc unit L * X ≤ unit L * (2 ^ L / (2 * LR)) :=
          mul_le_mul_of_nonneg_left hX (unit_pos L).le
      _ = 1 / (2 * LR) := by
          unfold unit
          field_simp
  refine ⟨hsum.trans hbound, ?_⟩
  calc |∑ i ∈ s, r i * x i| ≤ 1 / (2 * LR) := hsum.trans hbound
    _ < 1 / LR := by
      rw [div_lt_div_iff₀ (by positivity) hLRq]
      linarith

/-! ## 6. The carried Gram stays positive definite -/

/-- [proved-derived; formal-checked] **`carried_gram_posDef`.** A carried Gram `H` whose every
entry is within one unit of an exact Gram `H_exact ⪰ I` (the exact accumulation of the unit prior
and the rank-one statistics that reached it, `within_one_unit_since_founding`) satisfies
`vᵀHv ≥ (1 − n·u)|v|²`, `n` its width: `|vᵀ(H − H_exact)v| ≤ u(Σ|v_i|)² ≤ n·u·|v|²` by
Cauchy–Schwarz. -/
theorem carried_gram_posDef {σ : Type*} [Fintype σ] (H Hx : σ → σ → ℚ)
    (hclose : ∀ i j, |H i j - Hx i j| ≤ unit L)
    (hexact : ∀ v : σ → ℚ, ∑ i, v i ^ 2 ≤ ∑ i, ∑ j, v i * Hx i j * v j) (v : σ → ℚ) :
    (1 - Fintype.card σ * unit L) * ∑ i, v i ^ 2 ≤ ∑ i, ∑ j, v i * H i j * v j := by
  have hu := unit_pos L
  set dev := ∑ i, ∑ j, v i * (H i j - Hx i j) * v j
  have hdev : |dev| ≤ unit L * (∑ i, |v i|) ^ 2 := by
    calc |dev| ≤ ∑ i, |∑ j, v i * (H i j - Hx i j) * v j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, |v i * (H i j - Hx i j) * v j| :=
          Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, unit L * (|v i| * |v j|) := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          rw [abs_mul, abs_mul]
          have h1 := hclose i j
          have h2 := mul_nonneg (abs_nonneg (v i)) (abs_nonneg (v j))
          nlinarith [abs_nonneg (H i j - Hx i j)]
      _ = unit L * (∑ i, |v i|) ^ 2 := by
          rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
  have hcs : (∑ i, |v i|) ^ 2 ≤ Fintype.card σ * ∑ i, v i ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => |v i|) (fun _ => (1 : ℚ))
    simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, sq_abs] at h
    linarith
  have hsplit : ∑ i, ∑ j, v i * H i j * v j = ∑ i, ∑ j, v i * Hx i j * v j + dev := by
    simp only [dev]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hx := hexact v
  have hlow := neg_abs_le dev
  have hscaled := mul_le_mul_of_nonneg_left hcs hu.le
  rw [hsplit]
  nlinarith

/-- [proved-derived; formal-checked] **`carried_gram_posDef_rule`.** Under the lattice rule
`2 L_R X ≤ 2^L` with the Gram width `n ≤ X`, the carried Gram satisfies
`vᵀHv ≥ (1 − 1/(2L_R))|v|²` since the locus's founding: positive definite, with no clamp. -/
theorem carried_gram_posDef_rule {σ : Type*} [Fintype σ] (H Hx : σ → σ → ℚ)
    (hclose : ∀ i j, |H i j - Hx i j| ≤ unit L)
    (hexact : ∀ v : σ → ℚ, ∑ i, v i ^ 2 ≤ ∑ i, ∑ j, v i * Hx i j * v j) {LR : ℕ}
    (hLR : 0 < LR) (hL : 2 * LR * Fintype.card σ ≤ 2 ^ L) (v : σ → ℚ) :
    (1 - 1 / (2 * LR)) * ∑ i, v i ^ 2 ≤ ∑ i, ∑ j, v i * H i j * v j := by
  have hLRq : (0 : ℚ) < LR := by exact_mod_cast hLR
  have hn : (Fintype.card σ : ℚ) * unit L ≤ 1 / (2 * LR) := by
    have hLq : (2 * LR * Fintype.card σ : ℚ) ≤ 2 ^ L := by exact_mod_cast hL
    unfold unit
    rw [le_div_iff₀ (by positivity)]
    calc (Fintype.card σ : ℚ) * ((2 : ℚ) ^ L)⁻¹ * (2 * LR)
        = (2 * LR * Fintype.card σ) * ((2 : ℚ) ^ L)⁻¹ := by ring
      _ ≤ 2 ^ L * ((2 : ℚ) ^ L)⁻¹ := mul_le_mul_of_nonneg_right hLq (by positivity)
      _ = 1 := by field_simp
  have hsq : 0 ≤ ∑ i, v i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg (v i)
  calc (1 - 1 / (2 * LR)) * ∑ i, v i ^ 2 ≤ (1 - Fintype.card σ * unit L) * ∑ i, v i ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith) hsq
    _ ≤ _ := carried_gram_posDef H Hx hclose hexact v

/-! ## 7. Bits of a lattice entry -/

/-- [definition] The bits of a lattice coordinate: its magnitude's binary length and a sign. -/
def coordinateBits (q : ℤ) : ℕ := Nat.size q.natAbs + 1

/-- [proved-derived; formal-checked] A coordinate of magnitude at most `N` takes at most
`⌈log₂(N + 1)⌉ + 1` bits. -/
theorem coordinateBits_le {q : ℤ} {N : ℕ} (h : q.natAbs ≤ N) :
    coordinateBits q ≤ Nat.clog 2 (N + 1) + 1 := by
  unfold coordinateBits
  have : Nat.size q.natAbs ≤ Nat.clog 2 (N + 1) := by
    rw [Nat.size_le]
    calc q.natAbs < N + 1 := Nat.lt_succ_of_le h
      _ ≤ 2 ^ Nat.clog 2 (N + 1) := Nat.le_pow_clog (by norm_num) _
  omega

/-- A lattice entry of magnitude at most `M` has a coordinate of magnitude at most `⌊M·2^L⌋`. -/
theorem natAbs_le_floor {q : ℤ} {M : ℚ} (h : |(q : ℚ) * unit L| ≤ M) :
    q.natAbs ≤ ⌊M * 2 ^ L⌋₊ := by
  have hpow : (0 : ℚ) < 2 ^ L := by positivity
  have habs : |(q : ℚ)| ≤ M * 2 ^ L := by
    have hu : |(q : ℚ) * unit L| = |(q : ℚ)| * ((2 : ℚ) ^ L)⁻¹ := by
      unfold unit
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℚ) < ((2 : ℚ) ^ L)⁻¹)]
    rw [hu] at h
    have := mul_le_mul_of_nonneg_right h hpow.le
    rwa [mul_assoc, inv_mul_cancel₀ hpow.ne', mul_one] at this
  have hM : 0 ≤ M * 2 ^ L := le_trans (abs_nonneg _) habs
  rw [Nat.le_floor_iff hM]
  have : ((q.natAbs : ℕ) : ℚ) = |(q : ℚ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [this]
  exact habs

/-- [proved-derived; formal-checked] **A lattice entry's bits.** An entry `q·2^(−L)` of magnitude
at most `M` takes at most `⌈log₂(⌊M·2^L⌋ + 1)⌉ + 1` bits, sign included. -/
theorem lattice_entry_bits {q : ℤ} {M : ℚ} (h : |(q : ℚ) * unit L| ≤ M) :
    coordinateBits q ≤ Nat.clog 2 (⌊M * 2 ^ L⌋₊ + 1) + 1 :=
  coordinateBits_le (natAbs_le_floor h)

/-- [proved-derived; formal-checked] **`lattice_bits_bounded`.** A family of lattice entries, each
of magnitude at most `M`, with remainders of `b i` bits, carries at most
`entries × (⌈log₂(⌊M·2^L⌋ + 1)⌉ + 1)` bits plus the remainders' bits. -/
theorem lattice_bits_bounded {ι : Type*} (s : Finset ι) (q : ι → ℤ) (b : ι → ℕ) {M : ℚ}
    (h : ∀ i ∈ s, |(q i : ℚ) * unit L| ≤ M) :
    ∑ i ∈ s, (coordinateBits (q i) + b i) ≤
      s.card * (Nat.clog 2 (⌊M * 2 ^ L⌋₊ + 1) + 1) + ∑ i ∈ s, b i := by
  rw [Finset.sum_add_distrib]
  gcongr
  calc ∑ i ∈ s, coordinateBits (q i) ≤ ∑ _i ∈ s, (Nat.clog 2 (⌊M * 2 ^ L⌋₊ + 1) + 1) :=
        Finset.sum_le_sum fun i hi => lattice_entry_bits (h i hi)
    _ = s.card * (Nat.clog 2 (⌊M * 2 ^ L⌋₊ + 1) + 1) := by
        rw [Finset.sum_const, smul_eq_mul]

/-- [proved-derived; formal-checked] **As a reduced rational** (numerator and denominator, the
Rust count), a lattice entry of magnitude at most `M` takes at most
`⌈log₂(⌊M·2^L⌋ + 1)⌉ + L + 1` bits: its numerator divides the coordinate and its denominator
divides `2^L`. -/
theorem lattice_rat_bits_bounded {q : ℤ} {M : ℚ} (h : |(q : ℚ) * unit L| ≤ M) :
    Nat.size ((q : ℚ) * unit L).num.natAbs + Nat.size ((q : ℚ) * unit L).den ≤
      Nat.clog 2 (⌊M * 2 ^ L⌋₊ + 1) + L + 1 := by
  have hx : (q : ℚ) * unit L = Rat.divInt q (2 ^ L) := by
    rw [Rat.divInt_eq_div]
    unfold unit
    push_cast
    ring
  have hden : Nat.size ((q : ℚ) * unit L).den ≤ L + 1 := by
    rw [Nat.size_le]
    have hd := Rat.den_dvd q (2 ^ L)
    rw [← hx] at hd
    have hle : (((q : ℚ) * unit L).den : ℤ) ≤ 2 ^ L :=
      Int.le_of_dvd (by positivity) hd
    have : ((q : ℚ) * unit L).den ≤ 2 ^ L := by exact_mod_cast hle
    calc ((q : ℚ) * unit L).den ≤ 2 ^ L := this
      _ < 2 ^ (L + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hnum : Nat.size ((q : ℚ) * unit L).num.natAbs ≤ Nat.clog 2 (⌊M * 2 ^ L⌋₊ + 1) := by
    have hcoord := coordinateBits_le (natAbs_le_floor h)
    unfold coordinateBits at hcoord
    have hsize : Nat.size ((q : ℚ) * unit L).num.natAbs ≤ Nat.size q.natAbs := by
      by_cases hq : q = 0
      · simp [hq]
      · apply Nat.size_le_size
        have hd := Rat.num_dvd q (by positivity : (2 : ℤ) ^ L ≠ 0)
        rw [← hx] at hd
        exact Nat.le_of_dvd (Int.natAbs_pos.mpr hq) (Int.natAbs_dvd_natAbs.mpr hd)
    omega
  omega

/-! ## 8. The budgeted deposit descends through the collapse -/

section Descends

open Holonics.HNN.Propagation Holonics.HNN.Retention

variable {B : Type*} [Fintype B] {adj : B → B → Prop}
variable {K : Type*} [Field K] {M : B → Type*} [∀ b, AddCommGroup (M b)] [∀ b, Module K (M b)]
variable {Cls : Type*} {Ent : B → B → Type*}

/-- [definition] **The carried locus's operator**: it reads only the lattice value. -/
def carriedOp (op : Cls → (y z : B) → (Ent y z → ℚ) → (M z →ₗ[K] M y)) :
    Cls → (y z : B) → Carried L (Ent y z) → (M z →ₗ[K] M y) :=
  fun c y z s => op c y z s.value

/-- [definition] **The carried release**: a released locus leaves whole, its value, remainder and
clock replaced by the declared release value, no remainder and clock zero. -/
def carriedRel (rel : (y z : B) → Ent y z → ℚ) : (y z : B) → Carried L (Ent y z) :=
  fun y z => Carried.fresh (rel y z)

/-- [definition] **The lattice deposit law** of a locus law `upd` (its exact update from its own
lattice value and its window's data, `HNN/Normal`): the exact update, carried with its budgeted
release. -/
noncomputable def latticeLaw
    (upd : (y z : B) → (Ent y z → ℚ) → List (M z × Module.Dual K (M y)) → (Ent y z → ℚ)) :
    (y z : B) → Carried L (Ent y z) → List (M z × Module.Dual K (M y)) → Carried L (Ent y z) :=
  fun y z s data => carry s (upd y z s.value data)

/-- [proved-derived; formal-checked] **`lattice_deposit_descends`.** If a locus law's update from
an empty window is zero, the budgeted deposit gives the same carried constitution (values,
remainders and clocks) with or without the collapse: `HNN/Retention.deposit_descends` at the
carried law, whose empty-window identity is `carry_zero`. -/
theorem lattice_deposit_descends [DecidableEq B]
    {op : Cls → (y z : B) → (Ent y z → ℚ) → (M z →ₗ[K] M y)} {rel : (y z : B) → Ent y z → ℚ}
    (hrel : ∀ c y z, op c y z (rel y z) = 0)
    (upd : (y z : B) → (Ent y z → ℚ) → List (M z × Module.Dual K (M y)) → (Ent y z → ℚ))
    (hupd : ∀ y z θ, upd y z θ [] = 0) {θ : (y z : B) → Carried L (Ent y z)}
    (hθ : LociSparse adj (carriedOp op) θ) {S R : Set B} {eLast : ℕ} (c : Cls)
    {x₀ : (b : B) → M b} (hx : SupportedIn x₀ S)
    {rd : List (ℕ × ((b : B) → Module.Dual K (M b)))} (hrd : Admitted R eLast rd) :
    collapse adj (carriedRel rel) S R eLast
        (deposit adj (carriedOp op) (latticeLaw upd) S R c x₀ rd θ) =
      deposit adj (carriedOp op) (latticeLaw upd) S R c x₀ rd
        (collapse adj (carriedRel rel) S R eLast θ) :=
  deposit_descends (op := carriedOp op) (rel := carriedRel rel) (fun c y z => hrel c y z)
    (latticeLaw upd) (fun y z s => by simp only [latticeLaw, hupd, carry_zero]) hθ c hx hrd

end Descends

section Audit

#print axioms div_rem_spec
#print axioms rem_bounds
#print axioms quot_eq_zero_of_bounds
#print axioms gamma_kraft_lt_one
#print axioms carry_zero
#print axioms carry_accounting
#print axioms run_accounting
#print axioms lattice_deposit_accounting
#print axioms run_onLattice
#print axioms carry_entry_zero
#print axioms carried_remainder_bounded
#print axioms remainder_numerator_bounded
#print axioms remainder_rat_bits_bounded
#print axioms release_bounded
#print axioms release_bounded_since_founding
#print axioms within_one_unit_since_founding
#print axioms remainder_below_grain
#print axioms carried_gram_posDef
#print axioms carried_gram_posDef_rule
#print axioms lattice_entry_bits
#print axioms lattice_bits_bounded
#print axioms lattice_rat_bits_bounded
#print axioms lattice_deposit_descends

end Audit

end Holonics.HNN.LatticeDeposit
