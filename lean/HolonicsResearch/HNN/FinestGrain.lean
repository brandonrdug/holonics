import Mathlib
import Holonics.HNN.LatticeDeposit

/-!
# Every receiver of a declared field has a grain, so the finest grain is read without refusal

Source: comment c6249536068 of #62, box "Every receiver of a declared field has a grain, so the
finest grain `max_R L_R` is read without refusal" of #410, on `hnn::field::{receiver_grain,
finest_grain, lattice_exponent}` and `Field::declare` at `d5ed4adc1` (atlas
`hnn.receiving-precision-at-grain`, whose assumption column states the refusal). A receiver
declares a tolerance `ε`; its grain is the denominator `L_R = ⌈1/ε⌉`, refused, typed, where `ε` is
not positive or `L_R` has no `u64` representation. The finest grain is `max_R L_R` over the declared
receivers, `1` where none is declared, a fold that refuses at the first receiver without a grain.
`Field::declare` reads it first and returns its refusal, so a declared field's finest grain is
read by every later consumer (the lattice rule, the word's lattice, the initial constitution, the
population chart) with no refusal to handle and no coarser grain substituted.

## What is proved

* **The grain** (`receiverGrain`, `receiverGrain_isSome_iff`, `receiverGrain_spec`): it exists
  exactly when `0 < ε` and `⌈1/ε⌉ ≤ 2^64 − 1`; then `L_R ≥ 1`, `1/ε ≤ L_R < 1/ε + 1`, its unit
  resolves the tolerance (`one_div_grain_le`: `1/L_R ≤ ε`), and it is the least denominator that
  does (`grain_le_of_resolves`: `1/M ≤ ε` with `M > 0` gives `L_R ≤ M`).
* **The finest grain is the fold of `try_fold`** (`finestGrain`, `finestGrain_eq_foldlM`: the
  recursive reading equals `List.foldlM` of `max` from `1` in the refusal monad). It is read without
  refusal exactly when every receiver has a grain (`finestGrain_isSome_iff`), and then it is
  `max(1, max_R L_R)`: at least one and every receiver's grain, and either one or some receiver's
  grain (`finestGrain_spec`). Where none is declared it is one (`finestGrain_nil`).
* **The box.** `declare` models `Field::declare`'s first refusal, and it refuses exactly where the
  finest grain does (`declare_isSome_iff`). A declared set of receivers (`Declared`) carries the
  proof that every receiver has a grain, so its finest grain is a total read (`Declared.finest`,
  `Declared.finestGrain_eq`) that bounds every receiver's grain (`Declared.grain_le_finest`) and
  whose unit resolves every receiver's tolerance (`Declared.finest_resolves`: `1/max_R L_R ≤ ε_R`).
* **The lattice rule's exponent** (`latticeExponent`): `L = size(2·L_R·max(X, 1) − 1)`, the Rust's
  `128 − leading_zeros(reach − 1)` with its branch `reach ≤ 1 ↦ 0` included, is the least `L` with
  `2·L_R·max(X, 1) ≤ 2^L` (`reach_le_two_pow`, `latticeExponent_le_of_reach_le`), `⌈log₂(2 L_R X)⌉`.
* **The consumer** (`remainder_below_every_tolerance`): on a declared field's lattice by rule, a
  remainder of at most one lattice unit per entry moves a read through an operand of ℓ1 norm at most
  the fan-in by at most `ε_R / 2` for every declared receiver `R`, by
  `LatticeDeposit.remainder_below_grain` at the finest grain.

## Limits

* The `u128` saturation of `lattice_exponent`'s reach is not modelled: the exponent is the exact
  one, which the Rust's equals while `2·L_R·max(X, 1)` fits `u128` (it does for `L_R < 2^64` and
  `X < 2^63`).
* The operand's ℓ1 bound by the fan-in is the consumer's hypothesis, as in `LatticeDeposit` ("the
  unit scale of the waves is an assumption the notebook measures at each boundary").
* The rest of `Field::declare` (the rings, contacts, complex and capacity it checks after the
  grain) is not modelled; only its first refusal is, which is the one the box reads.
* Tolerances are rationals (`Rat` in the Rust); the typed error is `none`.

The computational object is the helical pair interaction's receiving face, read at a receiver's
grain. Of the winding guide's six objects this touches faces and placement (the receiver's grain,
the lattice a deposit lands on and the read through an operand); the helix, the pair, cell
holonomy, the tube and the tower thread stay attached through `LatticeDeposit` and the field's
declaration.

Consumers: `Holonics/HNN/LatticeDeposit` (`remainder_below_grain`, whose hypothesis
`2 L_R X ≤ 2^L` this module discharges from the declaration), the Rust owners
`hnn::field::{receiver_grain, finest_grain, lattice_exponent, Field::declare,
FieldDeclaration::lattice_by_rule}` at `d5ed4adc1`, and the atlas rows
`hnn.receiving-precision-at-grain` and `hnn.release-since-founding`.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.HNN.FinestGrain

/-! ## 1. A receiver's grain -/

/-- [definition] **The `u64` carrier's largest value**, `2^64 − 1`. -/
def carrierMax : ℕ := 2 ^ 64 - 1

/-- [definition] **The receiver's grain denominator** `L_R = ⌈1/ε⌉` (`receiver_grain`): `none`, the
typed refusal, where the tolerance is not positive or the grain exceeds the `u64` carrier. -/
def receiverGrain (ε : ℚ) : Option ℕ :=
  if 0 < ε ∧ ⌈ε⁻¹⌉ ≤ (carrierMax : ℤ) then some ⌈ε⁻¹⌉.toNat else none

/-- [proved-derived; formal-checked] A tolerance has a grain exactly when it is positive and its
grain fits the carrier. -/
theorem receiverGrain_isSome_iff (ε : ℚ) :
    (receiverGrain ε).isSome ↔ 0 < ε ∧ ⌈ε⁻¹⌉ ≤ (carrierMax : ℤ) := by
  unfold receiverGrain
  split_ifs with h <;> simp [h]

/-- [proved-derived; formal-checked] **The grain's reading**: a grain `L` of `ε` is positive, fits
the carrier, and is the ceiling of `1/ε`: `1/ε ≤ L < 1/ε + 1`. -/
theorem receiverGrain_spec {ε : ℚ} {L : ℕ} (h : receiverGrain ε = some L) :
    0 < ε ∧ 1 ≤ L ∧ L ≤ carrierMax ∧ ε⁻¹ ≤ L ∧ (L : ℚ) < ε⁻¹ + 1 := by
  unfold receiverGrain at h
  split_ifs at h with hε
  obtain ⟨hpos, hfit⟩ := hε
  simp only [Option.some.injEq] at h
  have hc1 : (1 : ℤ) ≤ ⌈ε⁻¹⌉ := Int.one_le_ceil_iff.mpr (inv_pos.mpr hpos)
  have hL : (L : ℤ) = ⌈ε⁻¹⌉ := by rw [← h]; exact Int.toNat_of_nonneg (by omega)
  have hLq : (L : ℚ) = (⌈ε⁻¹⌉ : ℚ) := by exact_mod_cast hL
  refine ⟨hpos, by omega, by omega, ?_, ?_⟩
  · rw [hLq]; exact Int.le_ceil _
  · rw [hLq]; exact Int.ceil_lt_add_one _

/-- [proved-derived; formal-checked] **The grain's unit resolves the tolerance**: `1/L_R ≤ ε`. -/
theorem one_div_grain_le {ε : ℚ} {L : ℕ} (h : receiverGrain ε = some L) : 1 / (L : ℚ) ≤ ε := by
  obtain ⟨hpos, hL1, -, hle, -⟩ := receiverGrain_spec h
  have hLpos : (0 : ℚ) < L := by exact_mod_cast hL1
  rw [div_le_iff₀ hLpos]
  have := mul_le_mul_of_nonneg_left hle hpos.le
  rwa [mul_inv_cancel₀ hpos.ne'] at this

/-- [proved-derived; formal-checked] **The grain is the least resolving denominator**: any `M > 0`
whose unit `1/M` resolves `ε` is at least `L_R`. -/
theorem grain_le_of_resolves {ε : ℚ} {L M : ℕ} (h : receiverGrain ε = some L) (hM : 0 < M)
    (hres : 1 / (M : ℚ) ≤ ε) : L ≤ M := by
  unfold receiverGrain at h
  split_ifs at h with hε
  obtain ⟨hpos, -⟩ := hε
  simp only [Option.some.injEq] at h
  have hMq : (0 : ℚ) < M := by exact_mod_cast hM
  have hinv : ε⁻¹ ≤ M := by
    rw [one_div] at hres
    exact (inv_le_comm₀ hMq hpos).mp hres
  have hc : ⌈ε⁻¹⌉ ≤ (M : ℤ) := Int.ceil_le.mpr (by exact_mod_cast hinv)
  rw [← h]
  omega

/-! ## 2. The finest grain -/

/-- [definition] **The fold from a grain read so far** (`try_fold` of `max`): refuses at the first
receiver without a grain. -/
def finestFrom (F : ℕ) : List ℚ → Option ℕ
  | [] => some F
  | ε :: εs =>
    match receiverGrain ε with
    | none => none
    | some L => finestFrom (max F L) εs

/-- [definition] **The finest receiver grain** `max_R L_R` (`finest_grain`), one where none is
declared. -/
def finestGrain (εs : List ℚ) : Option ℕ := finestFrom 1 εs

/-- [proved-derived; formal-checked] The recursive fold is `List.foldlM` of `max` in the refusal
monad, the Rust's `try_fold(1, |finest, R| Ok(finest.max(receiver_grain(R)?)))`. -/
theorem finestFrom_eq_foldlM (F : ℕ) (εs : List ℚ) :
    finestFrom F εs = εs.foldlM (fun G ε => (receiverGrain ε).map (max G)) F := by
  induction εs generalizing F with
  | nil => rfl
  | cons ε εs ih =>
    simp only [finestFrom, List.foldlM_cons]
    cases receiverGrain ε with
    | none => rfl
    | some L => simpa using ih (max F L)

/-- [proved-derived; formal-checked] `finestGrain` is the Rust's fold. -/
theorem finestGrain_eq_foldlM (εs : List ℚ) :
    finestGrain εs = εs.foldlM (fun G ε => (receiverGrain ε).map (max G)) 1 :=
  finestFrom_eq_foldlM 1 εs

/-- [proved-derived; formal-checked] Where no receiver is declared the finest grain is one. -/
theorem finestGrain_nil : finestGrain [] = some 1 := rfl

/-- [proved-derived; formal-checked] **The fold refuses exactly where a receiver has no grain.** -/
theorem finestFrom_isSome_iff (F : ℕ) (εs : List ℚ) :
    (finestFrom F εs).isSome ↔ ∀ ε ∈ εs, (receiverGrain ε).isSome := by
  induction εs generalizing F with
  | nil => simp [finestFrom]
  | cons ε εs ih =>
    simp only [finestFrom, List.mem_cons, forall_eq_or_imp]
    cases hε : receiverGrain ε with
    | none => simp
    | some L => simpa using ih (max F L)

/-- [proved-derived; formal-checked] **The finest grain is read without refusal exactly when every
receiver has a grain.** -/
theorem finestGrain_isSome_iff (εs : List ℚ) :
    (finestGrain εs).isSome ↔ ∀ ε ∈ εs, (receiverGrain ε).isSome :=
  finestFrom_isSome_iff 1 εs

/-- [proved-derived; formal-checked] **The fold's value** is the maximum of its start and every
receiver's grain: at least each, and equal to one of them. -/
theorem finestFrom_spec {F G : ℕ} {εs : List ℚ} (h : finestFrom F εs = some G) :
    F ≤ G ∧ (∀ ε ∈ εs, ∀ L, receiverGrain ε = some L → L ≤ G) ∧
      (G = F ∨ ∃ ε ∈ εs, receiverGrain ε = some G) := by
  induction εs generalizing F with
  | nil =>
    simp only [finestFrom, Option.some.injEq] at h
    subst h
    simp
  | cons ε εs ih =>
    simp only [finestFrom] at h
    cases hε : receiverGrain ε with
    | none => rw [hε] at h; exact absurd h (by simp)
    | some L =>
      rw [hε] at h
      obtain ⟨h1, h2, h3⟩ := ih h
      refine ⟨le_trans (le_max_left _ _) h1, ?_, ?_⟩
      · intro ε' hε' L' hL'
        rcases List.mem_cons.mp hε' with rfl | hmem
        · rw [hε] at hL'
          cases hL'
          exact le_trans (le_max_right _ _) h1
        · exact h2 ε' hmem L' hL'
      · rcases h3 with h3 | ⟨ε', hε', hG⟩
        · rcases le_total F L with hFL | hLF
          · right
            refine ⟨ε, List.mem_cons_self, ?_⟩
            rw [hε, h3, max_eq_right hFL]
          · left
            rw [h3, max_eq_left hLF]
        · exact Or.inr ⟨ε', List.mem_cons_of_mem _ hε', hG⟩

/-- [proved-derived; formal-checked] **The finest grain is `max(1, max_R L_R)`.** -/
theorem finestGrain_spec {G : ℕ} {εs : List ℚ} (h : finestGrain εs = some G) :
    1 ≤ G ∧ (∀ ε ∈ εs, ∀ L, receiverGrain ε = some L → L ≤ G) ∧
      (G = 1 ∨ ∃ ε ∈ εs, receiverGrain ε = some G) :=
  finestFrom_spec h

/-! ## 3. A declared field's receivers -/

/-- [definition] **A declared field's receivers**: their tolerances, each with a grain, which
`Field::declare` certifies before any lattice reads it. -/
structure Declared where
  tolerances : List ℚ
  grained : ∀ ε ∈ tolerances, (receiverGrain ε).isSome

/-- [definition] **The declaration's first refusal** (`Field::declare`'s
`finest_grain(&declared.receivers)?`). -/
def declare (εs : List ℚ) : Option Declared :=
  if h : ∀ ε ∈ εs, (receiverGrain ε).isSome then some ⟨εs, h⟩ else none

/-- [proved-derived; formal-checked] **The declaration refuses exactly where the finest grain
does.** -/
theorem declare_isSome_iff (εs : List ℚ) : (declare εs).isSome ↔ (finestGrain εs).isSome := by
  rw [finestGrain_isSome_iff]
  unfold declare
  split_ifs with h
  · simpa using h
  · simpa using h

/-- [definition] **The finest grain of a declared field**, a total read. -/
def Declared.finest (D : Declared) : ℕ :=
  (finestGrain D.tolerances).get ((finestGrain_isSome_iff _).mpr D.grained)

/-- [proved-derived; formal-checked] **The box: a declared field's finest grain is read without
refusal**, and it is `Declared.finest`. -/
theorem Declared.finestGrain_eq (D : Declared) : finestGrain D.tolerances = some D.finest := by
  simp [Declared.finest]

/-- [proved-derived; formal-checked] The finest grain is at least one. -/
theorem Declared.one_le_finest (D : Declared) : 1 ≤ D.finest :=
  (finestGrain_spec D.finestGrain_eq).1

/-- [proved-derived; formal-checked] **The finest grain bounds every receiver's grain.** -/
theorem Declared.grain_le_finest (D : Declared) {ε : ℚ} (hε : ε ∈ D.tolerances) {L : ℕ}
    (hL : receiverGrain ε = some L) : L ≤ D.finest :=
  (finestGrain_spec D.finestGrain_eq).2.1 ε hε L hL

/-- [proved-derived; formal-checked] **The finest grain's unit resolves every receiver's
tolerance**: `1/max_R L_R ≤ ε_R`. -/
theorem Declared.finest_resolves (D : Declared) {ε : ℚ} (hε : ε ∈ D.tolerances) :
    1 / (D.finest : ℚ) ≤ ε := by
  obtain ⟨L, hL⟩ := Option.isSome_iff_exists.mp (D.grained ε hε)
  have hle := D.grain_le_finest hε hL
  have hL1 := (receiverGrain_spec hL).2.1
  have hLq : (0 : ℚ) < L := by exact_mod_cast hL1
  calc 1 / (D.finest : ℚ) ≤ 1 / (L : ℚ) :=
        one_div_le_one_div_of_le hLq (by exact_mod_cast hle)
    _ ≤ ε := one_div_grain_le hL

/-! ## 4. The lattice rule and its consumer -/

/-- [definition] **The lattice rule's exponent** (`lattice_exponent`):
`size(2·L_R·max(X, 1) − 1)`, the bit length `128 − leading_zeros(reach − 1)`, zero where
`reach ≤ 1`. -/
def latticeExponent (grain fanIn : ℕ) : ℕ := Nat.size (2 * grain * max fanIn 1 - 1)

/-- [proved-derived; formal-checked] **The rule holds**: `2·L_R·max(X, 1) ≤ 2^L`. -/
theorem reach_le_two_pow (grain fanIn : ℕ) :
    2 * grain * max fanIn 1 ≤ 2 ^ latticeExponent grain fanIn := by
  have := Nat.lt_size_self (2 * grain * max fanIn 1 - 1)
  unfold latticeExponent
  omega

/-- [proved-derived; formal-checked] **The rule's exponent is the least**: `⌈log₂(2 L_R X)⌉`. -/
theorem latticeExponent_le_of_reach_le {grain fanIn k : ℕ}
    (h : 2 * grain * max fanIn 1 ≤ 2 ^ k) : latticeExponent grain fanIn ≤ k := by
  unfold latticeExponent
  rw [Nat.size_le]
  have := Nat.one_le_two_pow (n := k)
  omega

/-- [proved-derived; formal-checked] **A remainder on the declared field's lattice is below every
receiver's tolerance.** On the lattice by rule at the finest grain, a remainder of at most one
lattice unit per entry moves a read through an operand of ℓ1 norm at most the fan-in by at most
`ε_R / 2` for every declared receiver (`LatticeDeposit.remainder_below_grain`). -/
theorem remainder_below_every_tolerance (D : Declared) {ι : Type*} (s : Finset ι) (r x : ι → ℚ)
    (fanIn : ℕ)
    (hr : ∀ i ∈ s, |r i| ≤ LatticeDeposit.unit (latticeExponent D.finest fanIn))
    (hx : ∑ i ∈ s, |x i| ≤ fanIn) {ε : ℚ} (hε : ε ∈ D.tolerances) :
    |∑ i ∈ s, r i * x i| ≤ ε / 2 := by
  have hLR : 0 < D.finest := D.one_le_finest
  have hX : ∑ i ∈ s, |x i| ≤ ((max fanIn 1 : ℕ) : ℚ) :=
    le_trans hx (by exact_mod_cast le_max_left fanIn 1)
  have hL : 2 * (D.finest : ℚ) * ((max fanIn 1 : ℕ) : ℚ) ≤ 2 ^ latticeExponent D.finest fanIn := by
    exact_mod_cast reach_le_two_pow D.finest fanIn
  have hrem := (LatticeDeposit.remainder_below_grain s r x hLR hr hX hL).1
  have hres := D.finest_resolves hε
  calc |∑ i ∈ s, r i * x i| ≤ 1 / (2 * (D.finest : ℚ)) := hrem
    _ = (1 / (D.finest : ℚ)) / 2 := by ring
    _ ≤ ε / 2 := by linarith

/-! ## 5. Fixtures -/

/-- [proved-derived; formal-checked] A tolerance of zero has no grain, and refuses the
declaration. -/
theorem zero_refused : receiverGrain 0 = none ∧ declare [1, 0] = none := by
  refine ⟨by simp [receiverGrain], ?_⟩
  unfold declare
  rw [dif_neg]
  intro h
  have := h 0 (by simp)
  simp [receiverGrain] at this

end Holonics.HNN.FinestGrain
