import Holonics.HNN.LatticeDeposit
import Holonics.HNN.Ratio

/-!
# HNN.FiniteDecrease: the finite-decrease landing's first reach, witness and admission

[definition; agent-inferred, October 9] The medium-of-joints record §7 and #73. The certified
contact step `η = 2^-33` (C) and `2^-31` (K, D) puts its largest proposed entry 22, 20 and 20 binary
orders below the material lattice's half-unit, so the applied factor change is zero and the move
stays in the carried remainder (`LatticeDeposit.carry_accounting`). The landing replaces the a
priori curvature certificate, for ONE declared candidate per deposit, by an a posteriori admission:

* **The declared step** (`hnn::constitution::{first_reach_scan, Constitution::first_reach,
  Constitution::deposited_with_contact_spans_at}`). Each reached contact family `f` with unit step
  `d_f` steps at its first reach
  `k_f = min { k ≥ k_cert(f) : some entry has q_i(k) ≠ 0 }`, with `q_i(k)` the owner's own split
  (`LatticeDeposit.quot`: nearest, ties upward) of `2^k d_{f,i} + r_i`, `r_i` the part the native
  pass carries there. The scan is finite: at the least `k_max` with `2^k_max max_i |d_i| > u`, the
  widest entry's split is nonzero (`first_reach_endpoint`).
* **The re-read** (`hnn::word::continuation::Word::compare_contacts_landing`): a transient Word of
  the same declared passage (source, Rest opening, junction steps, receiver, targets, mask) reads the
  candidate's comparison.
* **The admission** (`hnn::word::continuation::{decide, reading_identity, FiniteDecrease}`): with
  `L`, `L′` the producing and candidate code enclosures and `X`, `X′` their exact phase excesses,
  admit iff `upper(L′) < lower(L)` and `X′ ≤ X`, or the reading-identity witness holds and
  `X′ < X`.

[proved-derived] What is written here, as stated and not yet kernel-checked: the proofs are owed
to the queue's library build (`bash tools/lean_check.sh`), and no grade above `proved-derived` is
claimed until it accepts them.

1. **The split** (`split_spec`, `split_bounds`, consuming `LatticeDeposit.{div_rem_spec,
   rem_bounds}`): `q·u + r = x` with `−u/2 ≤ r < u/2`.
2. **The first-reach bound** (`quot_ne_zero_of_half_lt`): `|x| > u/2 ⇒ q ≠ 0`; **the scan's
   endpoint** (`first_reach_endpoint`): a remainder in its cell and `|y| > u` give `q(y + r) ≠ 0`;
   and a zero direction never reaches (`zero_direction_stays`, consuming
   `LatticeDeposit.quot_eq_zero_of_bounds`).
3. **The witness implies equal code expressions.** The code length a face reads from its cells at
   grain `L` is `HNN/Ratio.codeLength` at the exponents `n_c + k_c/L` (the fibre is never read,
   `HNN/Ratio.face_constant_on_fibre`); it is unchanged by a common carry shift (`codeLength_shift`),
   so normalizing by the largest carry VALUE is a gauge (`cellCode_gauge`, `Station.code_eq_cells`).
   Equal grain, target and gauge-normalized cells give equal code expressions, station by station
   and summed (`witness_code_eq`, `witness_total_eq`).
4. **The admission is sound** (`admission_sound`): over exact enclosures holding the true code
   lengths, either case gives "no worse in both parts and strictly better in one":
   `(ℓ′ ≤ ℓ ∧ X′ ≤ X) ∧ (ℓ′ < ℓ ∨ X′ < X)`. **Equal endpoints without the witness admit nothing**
   (`equal_endpoints_need_the_witness`).

[agent-inferred] **What it does not claim.** The admission certifies only the declared re-read
comparison on the Rest opening; it asserts neither that the held continuation `C′w′ = Cw` improves
nor that any later perception changes. That the Rust's enclosures hold the true code lengths is
`HNN/Ratio.face_code_length_within_grain` and the owner's enclosure arithmetic; that the transient
Word re-reads the declared comparison is the Rust's construction, checked by its fixtures
(`hnn::tests::finite_decrease`).

| Lean | Rust |
|---|---|
| `split_spec`, `split_bounds`, `quot_ne_zero_of_half_lt`, `first_reach_endpoint`, `zero_direction_stays` | `hnn::constitution::first_reach_scan` over `Lattice::div_rem` |
| `cellExponent`, `cellCode`, `gauge`, `codeLength_shift`, `cellCode_gauge`, `Station`, `Witness`, `witness_code_eq`, `witness_total_eq` | `hnn::word::continuation::reading_identity` over `hnn::ratio::Face` |
| `Enclosure`, `strictlyBetter`, `Admission`, `admission_sound`, `equal_endpoints_need_the_witness` | `hnn::word::continuation::decide` with `holon::deposition::strictly_better` |

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.HNN.FiniteDecrease

/-! ## 1. The split and the first reach -/

/-- [proved-derived] **The split**: `q·u + r = x` (`LatticeDeposit.div_rem_spec`). -/
theorem split_spec (L : ℕ) (x : ℚ) :
    (LatticeDeposit.quot L x : ℚ) * LatticeDeposit.unit L + LatticeDeposit.rem L x = x :=
  (LatticeDeposit.div_rem_spec L x).symm

/-- [proved-derived] **The remainder lies in the half-open cell**
`−u/2 ≤ r < u/2` (`LatticeDeposit.rem_bounds`). -/
theorem split_bounds (L : ℕ) (x : ℚ) :
    -(LatticeDeposit.unit L / 2) ≤ LatticeDeposit.rem L x ∧
      LatticeDeposit.rem L x < LatticeDeposit.unit L / 2 :=
  LatticeDeposit.rem_bounds L x

/-- [proved-derived] **The first-reach bound**: a value more than half a unit from
zero leaves its cell, `|x| > u/2 ⇒ q ≠ 0`. -/
theorem quot_ne_zero_of_half_lt {L : ℕ} {x : ℚ} (h : LatticeDeposit.unit L / 2 < |x|) :
    LatticeDeposit.quot L x ≠ 0 := by
  intro hq
  have hspec := LatticeDeposit.div_rem_spec L x
  have hbounds := LatticeDeposit.rem_bounds L x
  have hx : x = LatticeDeposit.rem L x := by
    rw [hq, Int.cast_zero, zero_mul, zero_add] at hspec
    exact hspec
  rcases lt_abs.mp h with h1 | h1
  · linarith [hbounds.2]
  · linarith [hbounds.1]

/-- [proved-derived] **The scan's endpoint**: a carried remainder in its cell meets
a move of more than one unit, `|y| > u`, and the split leaves its cell: `|y + r| > u − u/2`. At
`k_max`, the least `k` with `2^k max_i |d_i| > u`, the widest entry's `y = 2^k d_i` is such a move. -/
theorem first_reach_endpoint {L : ℕ} {y r : ℚ}
    (hr : -(LatticeDeposit.unit L / 2) ≤ r ∧ r < LatticeDeposit.unit L / 2)
    (hy : LatticeDeposit.unit L < |y|) : LatticeDeposit.quot L (y + r) ≠ 0 := by
  apply quot_ne_zero_of_half_lt
  rcases lt_abs.mp hy with h | h
  · rw [lt_abs]
    left
    linarith [hr.1]
  · rw [lt_abs]
    right
    linarith [hr.2]

/-- [proved-derived] **A zero direction never reaches**: at every exponent its
split is the carried remainder's, which divides to zero (`LatticeDeposit.quot_eq_zero_of_bounds`),
so such a family is not in the candidate. -/
theorem zero_direction_stays {L : ℕ} {r : ℚ}
    (hr : -(LatticeDeposit.unit L / 2) ≤ r ∧ r < LatticeDeposit.unit L / 2) (k : ℤ) :
    LatticeDeposit.quot L ((2 : ℚ) ^ k * 0 + r) = 0 := by
  rw [mul_zero, zero_add]
  exact LatticeDeposit.quot_eq_zero_of_bounds hr

/-! ## 2. The reading-identity witness -/

/-- [definition] **The exponent a face reads from a cell** `(n, k)` at grain `L`: `n + k/L`. The
unresolved fibre is never read (`HNN/Ratio.face_constant_on_fibre`). -/
noncomputable def cellExponent (L : ℕ) (cell : ℤ × ℤ) : ℝ :=
  (cell.1 : ℝ) + (cell.2 : ℝ) / (L : ℝ)

/-- [definition] **The code length of class `t` read from cells** at grain `L`:
`HNN/Ratio.codeLength` at the cells' exponents. -/
noncomputable def cellCode {ι : Type*} [Fintype ι] (L : ℕ) (cells : ι → ℤ × ℤ) (t : ι) : ℝ :=
  Ratio.codeLength (fun c => cellExponent L (cells c)) t

/-- [definition] **The gauge-normalized cells** `(n_c − top, k_c)`. -/
def gauge {ι : Type*} (top : ℤ) (cells : ι → ℤ × ℤ) : ι → ℤ × ℤ :=
  fun c => ((cells c).1 - top, (cells c).2)

/-- [proved-derived] **A common shift of every exponent leaves each code length**:
`log₂ Σ_c 2^(f_c + s) = s + log₂ Σ_c 2^(f_c)`. -/
theorem codeLength_shift {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → ℝ) (s : ℝ) (t : ι) :
    Ratio.codeLength (fun c => f c + s) t = Ratio.codeLength f t := by
  have hS : 0 < ∑ c, (2 : ℝ) ^ f c :=
    Finset.sum_pos (fun c _ => by positivity) Finset.univ_nonempty
  have hsum : ∑ c, (2 : ℝ) ^ (f c + s) = (2 : ℝ) ^ s * ∑ c, (2 : ℝ) ^ f c := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Real.rpow_add (by norm_num)]
    ring
  simp only [Ratio.codeLength]
  rw [hsum, Real.logb_mul (by positivity) hS.ne', Real.logb_rpow (by norm_num) (by norm_num)]
  ring

/-- [proved-derived] **Normalizing by the largest carry is a gauge**: the code read
from `(n_c − top, k_c)` is the code read from `(n_c, k_c)`, whatever `top`. -/
theorem cellCode_gauge {ι : Type*} [Fintype ι] [Nonempty ι] (L : ℕ) (top : ℤ)
    (cells : ι → ℤ × ℤ) (t : ι) : cellCode L (gauge top cells) t = cellCode L cells t := by
  have h : (fun c => cellExponent L (gauge top cells c)) =
      fun c => cellExponent L (cells c) + -(top : ℝ) := by
    funext c
    simp only [cellExponent, gauge]
    push_cast
    ring
  unfold cellCode
  rw [h]
  exact codeLength_shift (fun c => cellExponent L (cells c)) (-(top : ℝ)) t

/-- [definition] **One compared station's reading inputs**: the grain, the target class, the
target phase, the branch, the largest carry value and every class's cell. -/
structure Station (ι : Type*) where
  grain : ℕ
  target : ι
  targetPhase : ℚ
  branch : ℤ
  top : ℤ
  cells : ι → ℤ × ℤ

/-- [definition] **The reading-identity witness** at one station: the same grain, target class,
target phase and branch, and the same gauge-normalized cell for every class. -/
def Witness {ι : Type*} (s s' : Station ι) : Prop :=
  s.grain = s'.grain ∧ s.target = s'.target ∧ s.targetPhase = s'.targetPhase ∧
    s.branch = s'.branch ∧ gauge s.top s.cells = gauge s'.top s'.cells

/-- [definition] The station's code expression, read from its gauge-normalized cells. -/
noncomputable def Station.code {ι : Type*} [Fintype ι] (s : Station ι) : ℝ :=
  cellCode s.grain (gauge s.top s.cells) s.target

/-- [proved-derived] The gauge-normalized code is the code of the raw cells. -/
theorem Station.code_eq_cells {ι : Type*} [Fintype ι] [Nonempty ι] (s : Station ι) :
    s.code = cellCode s.grain s.cells s.target :=
  cellCode_gauge s.grain s.top s.cells s.target

/-- [proved-derived] **The witness implies equal code expressions.** -/
theorem witness_code_eq {ι : Type*} [Fintype ι] {s s' : Station ι} (h : Witness s s') :
    s.code = s'.code := by
  unfold Witness at h
  obtain ⟨hL, ht, -, -, hg⟩ := h
  unfold Station.code
  rw [hL, ht, hg]

/-- [proved-derived] **Over the compared stations**, the witness at every station
gives equal summed code expressions. -/
theorem witness_total_eq {ι : Type*} [Fintype ι] {n : ℕ} (P Q : Fin n → Station ι)
    (h : ∀ j, Witness (P j) (Q j)) : ∑ j, (P j).code = ∑ j, (Q j).code :=
  Finset.sum_congr rfl fun j _ => witness_code_eq (h j)

/-! ## 3. The admission -/

/-- [definition] **An exact enclosure** `[lower, upper]` of a real reading. -/
structure Enclosure where
  lower : ℚ
  upper : ℚ

/-- [definition] The enclosure holds the reading. -/
def Enclosure.Holds (e : Enclosure) (x : ℝ) : Prop :=
  (e.lower : ℝ) ≤ x ∧ x ≤ (e.upper : ℝ)

/-- [definition] `holon::deposition::strictly_better(current, other)`: `other.upper < current.lower`. -/
def strictlyBetter (current other : Enclosure) : Prop :=
  other.upper < current.lower

/-- [definition] **The admission**: `upper(L′) < lower(L)` and `X′ ≤ X`, or the witness and
`X′ < X`. -/
def Admission (L L' : Enclosure) (X X' : ℚ) (W : Prop) : Prop :=
  (strictlyBetter L L' ∧ X' ≤ X) ∨ (W ∧ X' < X)

/-- [proved-derived] **The admission is sound**: when `L` and `L′` hold the true code
lengths `ℓ` and `ℓ′`, and the witness gives equal codes, an admitted candidate is no worse in both
parts and strictly better in one. -/
theorem admission_sound {L L' : Enclosure} {X X' : ℚ} {W : Prop} {ℓ ℓ' : ℝ}
    (hℓ : L.Holds ℓ) (hℓ' : L'.Holds ℓ') (hW : W → ℓ' = ℓ) (h : Admission L L' X X' W) :
    (ℓ' ≤ ℓ ∧ X' ≤ X) ∧ (ℓ' < ℓ ∨ X' < X) := by
  unfold Enclosure.Holds at hℓ hℓ'
  unfold Admission strictlyBetter at h
  rcases h with ⟨hs, hX⟩ | ⟨hw, hX⟩
  · have hcast : (L'.upper : ℝ) < (L.lower : ℝ) := by exact_mod_cast hs
    have hl : ℓ' < ℓ := by linarith [hℓ.1, hℓ'.2]
    exact ⟨⟨hl.le, hX⟩, Or.inl hl⟩
  · have he : ℓ' = ℓ := hW hw
    exact ⟨⟨he.le, hX.le⟩, Or.inr hX⟩

/-- [proved-derived] **Equal endpoints without the witness admit nothing**: an
enclosure is never strictly better than itself, so identical endpoints decide nothing. -/
theorem equal_endpoints_need_the_witness {L : Enclosure} {X X' : ℚ} (hL : L.lower ≤ L.upper) :
    ¬ Admission L L X X' False := by
  unfold Admission strictlyBetter
  rintro (⟨hs, -⟩ | ⟨hf, -⟩)
  · exact absurd hs (not_lt.mpr hL)
  · exact hf

end Holonics.HNN.FiniteDecrease
