import Holonics.Foundation.ContinuingTower

/-!
# The carry tower: finite carry charts are the `ZMod (b ^ n)` tower, lifted by Hensel's condition

[definition] Source: #410's box "The carry tower: finite carry charts joined to `Foundation/IwasawaTower.padicTower`
and `Foundation/ContinuingTower.CompatibleSection`, keeping the lifting condition and the nonunique fibre", carried
from packet 8 of the record `2026-09-21_WINDING_CARRY_FACES_AND_PLACEMENT_GENERALIZE_THE_HELICAL_PAIR` ("the carry
tower joined to `IwasawaTower.padicTower`"). The winding guide states the law in §6
(`docs/WINDING_CARRY_AND_PLACEMENT.md`: "A coherent thread through a tower lifts level by level, uniquely when the
required lifting condition holds (Hensel; …)"), and `CLAUDE.md`'s precision law states the word it reads: a value is
digits in a chosen basis chained with carries, and dropping a word's top is a quotient, a ring map. Atlas rows served:
`tower.hensel-thread`, `tower.continuing-tower`, `tower.gluing`, `tower.padic-plural`,
`tower.adjacent-surjective-section`, `radix.closing-edge` (the top carry released gives the path `ℤ/bⁿ`),
`radix.release-quotient-or-section`, `radix.leading-fibre` (the trailing face of a sum or product needs only the
trailing faces) and `radix.carry-cascade-consumer`.

The owners joined: `Foundation/PadicTower.padicTower` (the `ZMod (p ^ n)` tower under the cast maps; its signature
takes no primality, so `padicTower b` is the `b`-adic tower for every base and is used here as it stands), and in
`Foundation/ContinuingTower` the `Tower` carrier, `CompatibleSection`, `ObservationFibre`, `GluingResult`, `Migration`,
`padicSectionEquiv` (C2, cited by `IwasawaTower.gammaSectionEquiv` and `Transport/ContinuingTube.padicTube_end_equiv`),
`padicTower_plural` and `nonempty_compatibleSection_of_surjectiveAdjacent`. Nothing of the Iwasawa module is consumed.

[proved-derived; formal-checked] What is proved.

1. **The finite carry chart** (`value`, `value_lt`, `digit_eq_value`, `chartEquiv`): a word `w : Fin n → Fin b`,
   least significant digit first, reads `value w = Σ_k w_k bᵏ < bⁿ`, and `w ↦ value w` is a bijection onto
   `ZMod (b ^ n)` for every base `b ≥ 1` (through Mathlib's `finFunctionFinEquiv`), digit `k` being
   `value w / bᵏ mod b`.
2. **Addition with carry is the ring's addition, the top carry dropped** (`carry`, `addCarry`, `addCarry_digit`,
   `carry_zero`, `carry_succ`, `carry_le_one`, `lowValue_add`, `value_addCarry`, `topCarry_eq`,
   `value_addCarry_eq_mod`, `chartEquiv_addCarry`, `addCarry_eq_transport`): the adder is defined place by place,
   digit `k` of the sum is `(w_k + w'_k + c_k) mod b` with `c_0 = 0` and `c_(k+1) = (w_k + w'_k + c_k) / b`, every
   carry is a bit, the low values satisfy `low_k w + low_k w' = low_k (w + w') + c_k bᵏ`, and at the top
   `value (w + w') + c_n bⁿ = value w + value w'`: the chart carries the adder to addition in `ZMod (b ^ n)`, and
   the released top carry `c_n = ⌊(value w + value w')/bⁿ⌋` is the quotient. Multiplication is transported
   (`mulCarry`, `value_mulCarry`: the value is `value w · value w' mod bⁿ`).
3. **The carry tower is the `b`-adic tower** (`carryTower`, `truncate`, `value_truncate`, `wordFace_truncate`,
   `chartMigration`, `readMigration`, `sectionEquivPadicTower`): truncation to the first `m ≤ n` digits is a tower
   restriction, the chart reads it as `value mod bᵐ`, so the charts are a `Migration` to `padicTower b` with an inverse
   migration, face by face and compatibly with restriction, and the compatible sections of the two towers correspond.
   Truncation commutes with the adder (`carry_truncate`, `truncate_addCarry`: the carry into place `k` reads only the
   places below `k`) and with multiplication (`truncate_mulCarry`).
4. **The compatible sections are the digit streams, and at a prime they are `ℤ_[p]`** (`streamSection`,
   `sectionStream`, `streamEquiv`, `streamEquivPadic`, `toZModPow_streamEquivPadic`, `streamEquivPadic_symm_apply`):
   `(ℕ → Fin b) ≃ CompatibleSection`, and for `b = p` prime the composite with `padicSectionEquiv` is the `p`-adic
   digit expansion: the level-`n` face of the integer of a stream is the value of its first `n` digits, and digit `k`
   of `α` is `(toZModPow (k+1) α).val / pᵏ mod p`.
5. **The nonunique fibre** (`fibreEquiv`, `fibre_card_add`, `fibre_card`, `restrict_surjective`,
   `restrict_not_injective`, `carryTower_plural`, `carryTower_gluing`, `carryTower_plural_via_padic`,
   `observationFibre_reaches`): over each face at level `m` the fibre at level `n ≥ m` is the free choice of the
   upper `n − m` digits, exactly `b ^ (n − m)` lifts; restriction is surjective for `b ≥ 1` and not injective for
   `n > m` and `b ≥ 2`; the tower is plural for `b ≥ 2` (directly, and for `b = p` through `padicTower_plural`), and
   every lift is reached by a continuing object behind the face.
6. **The tail above a face** (`aboveTower`, `aboveSection`, `aboveSection_witness`, `aboveSectionEquiv`,
   `unique_of_bijectiveAdjacent`, `gluing_unique_of_bijectiveAdjacent`): for any tower over `ℕ`, the faces at levels
   `k + j` lying over one face `a` form a tower whose compatible sections are the observation fibre behind `a`; a tower
   with a one-point base and bijective adjacent restrictions has exactly one compatible section, existence through
   `nonempty_compatibleSection_of_surjectiveAdjacent`.
7. **The lifting condition (Hensel, level by level)** (`taylor_step`, `hensel_int_exists`, `hensel_int_unique`,
   `hensel_lift`, `rootTower`, `rootTower_lift_unique`, `hensel_adjacent_bijective`, `henselThread_gluing`,
   `hensel_observationFibre`, `hensel_thread_unique`, `hensel_thread_unique_one`): for `f ∈ ℤ[X]`, a prime `p` and
   `n ≥ 1`, `f(A + t pⁿ) ≡ f(A) + t pⁿ f'(A) (mod pⁿ⁺¹)`; a root `x` of `f` on the face `ZMod (p ^ n)` whose level-1
   face has `f'(x) ≠ 0` has exactly one root lift on the face `ZMod (p ^ (n+1))`. The roots form a sub-tower of
   `padicTower p` (`rootTower`); above a root `a` at level `k ≥ 1` meeting the condition, its adjacent restrictions
   are bijective, its tail lands in the `unique` arm of `GluingResult`, and exactly one compatible section of the root
   tower passes through `a`.
8. **The thread is a `p`-adic root** (`forgetRoots`, `rootSectionEquiv`, `rootSectionEquiv_witness`,
   `hensel_padic_root_unique`): the root tower's compatible sections are the roots of `f` in `ℤ_[p]`, so a root
   modulo `pᵏ` meeting the condition is the face of exactly one root in `ℤ_[p]`. This is the thread, read level by
   level; Mathlib's `hensels_lemma` is not used.
9. **Where the condition fails** (`square_lifting_condition_fails`, `square_root_lifts_twice`,
   `square_root_lift_not_unique`, `sqrtTwo_lifting_condition_fails`, `sqrtTwo_no_root_mod_four`,
   `sqrtTwo_rootTower_gluing`, `sqrtNegOne_lifting_condition_fails`, `sqrtNegOne_no_root_mod_four`): `X²` at `p = 2`
   has the root `0` modulo `2` with `f'(0) = 0` and two root lifts `0` and `2` modulo `4` (the lift is not unique);
   `X² − 2` (root `0`) and `X² + 1` (root `1`) at `p = 2` meet `f' ≡ 0` and have no root modulo `4` at all, so the
   root tower of `X² − 2` lands in the `obstructed` arm. Beside them the condition holds for `X² + 1` at `p = 5`
   (`sqrtNegOne_five_roots`, `sqrtNegOne_five_thread`, `sqrtNegOne_five_other_thread`, `sqrtNegOne_five_gluing`): the
   roots `2` and `3` modulo `5` each carry exactly one thread, and the root tower is `plural`. The three arms of
   `GluingResult` are each inhabited by a sub-tower of `padicTower`.

What is not claimed. The adder is stated on words of one length; addition of digit streams with their unending carry
is not stated, though `sectionEquivPadicTower` transports it. Multiplication carries no digit recurrence here, only
the transported product. The lifting condition is the simple-root form at a unit derivative; the general form
`|f(a)| < |f'(a)|²` and Newton's quadratic convergence are not stated. For `X²` at `p = 2` the root tower's threads are
not counted: its finite lifts are plural while its one thread is that of `0` (`α² = 0` forces `α = 0` in `ℤ_[2]`, read
through `rootSectionEquiv`), and that count is not written here. The obstructed arm here empties a finite level;
the obstruction with every level inhabited stays `shiftTower`'s. The retired Rust owners of the tower carrier are not
consulted.

The computational object is the helical pair interaction read on a radix register: each place is a ring of `b`
positions, a word is a strand of rings joined by carries (helix = circle + carry), the two summands' digits at one
place meet as a pair contact whose overflow is the carry passed to the next ring, and the top carry released is where
the place graph closes into `ℤ/bⁿ`. The Hensel lift is the same contact one level up: the next digit `t` of a root
solves `q + f'(a) t ≡ 0 (mod p)`, and it is determined exactly when the contact's coupling `f'(a)` is a unit. Of the
winding guide's six general objects this touches the helix (`carry`, `addCarry`), faces and placement (the chart onto
`ZMod (b ^ n)`, the faces of `padicTower`) and the tower thread (`carryTower`, `rootTower`, `aboveTower`, the unique and
plural threads); the pair is the place's two digits; the cell holonomy and the tube stay attached
(`Transport/ContinuingTube.padicTube` is the tube whose cross-section is this tower).

Neighbours: `Geometry/PhaseCarry` owns the one-level carry and odometer on `ℕ`, `Mathematics/ArithmeticContract` the
unbounded carry cascade on digit lists, `Geometry/SolenoidChart` the rational chart with a signed winding, and
`EllipticCurve/FamilyTunnellBrandtPadicHensel` one Hensel correction through Mathlib's `hensels_lemma`.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Foundation.CarryTower

open Holonics.Foundation.ContinuingTower

/-! ## 1. The finite carry chart -/

section Chart

variable (b : ℕ)

/-- [definition] The value a word presents, least significant digit first: `Σ_k w_k bᵏ`. -/
def value {n : ℕ} (w : Fin n → Fin b) : ℕ := ∑ k : Fin n, (w k : ℕ) * b ^ (k : ℕ)

/-- [proved-standard; formal-checked] The value is Mathlib's positional reading `finFunctionFinEquiv`. -/
theorem value_eq_finFunctionFinEquiv {n : ℕ} (w : Fin n → Fin b) :
    value b w = (finFunctionFinEquiv w : ℕ) := (finFunctionFinEquiv_apply w).symm

/-- [proved-standard; formal-checked] A word of `n` digits reads a value below `bⁿ`. -/
theorem value_lt {n : ℕ} (w : Fin n → Fin b) : value b w < b ^ n := by
  rw [value_eq_finFunctionFinEquiv]
  exact (finFunctionFinEquiv w).isLt

/-- [proved-standard; formal-checked] Digit `k` of a word is `value / bᵏ mod b`. -/
theorem digit_eq_value {n : ℕ} (w : Fin n → Fin b) (k : Fin n) :
    (w k : ℕ) = value b w / b ^ (k : ℕ) % b := by
  conv_lhs => rw [← finFunctionFinEquiv.symm_apply_apply w]
  rw [finFunctionFinEquiv_symm_apply_val, ← value_eq_finFunctionFinEquiv]

/-- [proved-standard; formal-checked] Two words of one length with one value are one word. -/
theorem value_injective (n : ℕ) : Function.Injective (value b (n := n)) := by
  intro w w' h
  apply finFunctionFinEquiv.injective
  apply Fin.ext
  rwa [← value_eq_finFunctionFinEquiv, ← value_eq_finFunctionFinEquiv]

/-- [definition] The face a word presents on `ZMod (b ^ n)`. -/
def wordFace {n : ℕ} (w : Fin n → Fin b) : ZMod (b ^ n) := (value b w : ZMod (b ^ n))

/-- [definition] The digits of a face of `ZMod (b ^ n)`: its canonical representative read in base `b`. -/
def digits [NeZero b] (n : ℕ) (x : ZMod (b ^ n)) : Fin n → Fin b :=
  finFunctionFinEquiv.symm ⟨x.val, ZMod.val_lt x⟩

/-- [proved-standard; formal-checked] The digits of a face read back its canonical representative. -/
theorem value_digits [NeZero b] (n : ℕ) (x : ZMod (b ^ n)) : value b (digits b n x) = x.val := by
  rw [value_eq_finFunctionFinEquiv, digits, Equiv.apply_symm_apply]

/-- [proved-standard; formal-checked] **The finite carry chart.** Words of `n` digits in base `b ≥ 1` are in
bijection with `ZMod (b ^ n)`: forward the face, backward the digits. -/
def chartEquiv [NeZero b] (n : ℕ) : (Fin n → Fin b) ≃ ZMod (b ^ n) where
  toFun := wordFace b
  invFun := digits b n
  left_inv w := by
    apply value_injective b n
    rw [value_digits, wordFace, ZMod.val_cast_of_lt (value_lt b w)]
  right_inv x := by
    rw [wordFace, value_digits]
    exact ZMod.natCast_zmod_val x

/-- [definition] Truncation to the first `m ≤ n` digits: the trailing face of a word. -/
def truncate {m n : ℕ} (h : m ≤ n) (w : Fin n → Fin b) : Fin m → Fin b :=
  fun i => w (Fin.castLE h i)

/-- [proved-standard; formal-checked] A word appended above another reads `value u + bᵐ · value v`. -/
theorem value_append {m k : ℕ} (u : Fin m → Fin b) (v : Fin k → Fin b) :
    value b (Fin.append u v) = value b u + b ^ m * value b v := by
  simp only [value, Fin.sum_univ_add, Fin.append_left, Fin.append_right, Fin.val_castAdd,
    Fin.val_natAdd, pow_add, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by ring

/-- [proved-standard; formal-checked] The truncated word reads the value modulo `bᵐ`. -/
theorem value_truncate {m n : ℕ} (h : m ≤ n) (w : Fin n → Fin b) :
    value b (truncate b h w) = value b w % b ^ m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  have hw : w = Fin.append (truncate b h w) (fun j => w (Fin.natAdd m j)) :=
    Fin.append_castAdd_natAdd.symm
  conv_rhs => rw [hw, value_append]
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (value_lt b _)]

/-- [proved-derived; formal-checked] Truncation is the restriction of `padicTower b` read through the chart. -/
theorem wordFace_truncate {m n : ℕ} (h : m ≤ n) (w : Fin n → Fin b) :
    wordFace b (truncate b h w) = (padicTower b).restrict h (wordFace b w) := by
  show ((value b (truncate b h w) : ℕ) : ZMod (b ^ m)) =
    ZMod.castHom (pow_dvd_pow b h) (ZMod (b ^ m)) ((value b w : ℕ) : ZMod (b ^ n))
  rw [map_natCast, value_truncate, ZMod.natCast_mod]

/-- [definition] **The carry tower**: the words of `n` digits at level `n`, restricted by truncation. -/
def carryTower : Tower.{0, 0} ℕ where
  Face n := Fin n → Fin b
  restrict h w := truncate b h w
  restrict_refl _ _ := rfl
  restrict_trans _ _ _ := rfl

/-- [proved-derived; formal-checked] The chart is a migration from the carry tower to `padicTower b`. -/
def chartMigration : Migration (carryTower b) (padicTower b) where
  index := id
  index_mono h := h
  face _ w := wordFace b w
  naturality h w := (wordFace_truncate b h w).symm

/-- [proved-derived; formal-checked] Reading the digits is a migration back, from `padicTower b` to the carry
tower. -/
def readMigration [NeZero b] : Migration (padicTower b) (carryTower b) where
  index := id
  index_mono h := h
  face n x := digits b n x
  naturality {i j} h x := by
    apply (chartEquiv b i).injective
    show wordFace b (truncate b h (digits b j x)) =
      wordFace b (digits b i ((padicTower b).restrict h x))
    rw [wordFace_truncate]
    exact congrArg _ ((chartEquiv b j).right_inv x) |>.trans ((chartEquiv b i).right_inv _).symm

/-- [proved-derived; formal-checked] **The carry tower is the `b`-adic tower**: the two migrations carry the
continuing objects of each tower to the other's, both ways. -/
def sectionEquivPadicTower [NeZero b] :
    (carryTower b).CompatibleSection ≃ (padicTower b).CompatibleSection where
  toFun := (chartMigration b).carrySection
  invFun := (readMigration b).carrySection
  left_inv s := Tower.CompatibleSection.ext fun n => (chartEquiv b n).left_inv (s.witness n)
  right_inv s := Tower.CompatibleSection.ext fun n => (chartEquiv b n).right_inv (s.witness n)

/-- [definition] The continuing object of a digit stream: its first `n` digits at level `n`. -/
def streamSection (d : ℕ → Fin b) : (carryTower b).CompatibleSection where
  witness _ := fun k => d k
  compatible _ := rfl

/-- [definition] The digit stream of a continuing object: digit `k` read at level `k + 1`. -/
def sectionStream (s : (carryTower b).CompatibleSection) : ℕ → Fin b :=
  fun k => s.witness (k + 1) (Fin.last k)

/-- [proved-derived; formal-checked] The compatible sections of the carry tower are the digit streams. -/
def streamEquiv : (ℕ → Fin b) ≃ (carryTower b).CompatibleSection where
  toFun := streamSection b
  invFun := sectionStream b
  left_inv _ := rfl
  right_inv s := Tower.CompatibleSection.ext fun n => funext fun k =>
    (congrFun (s.compatible (show (k : ℕ) + 1 ≤ n from k.isLt)) (Fin.last k)).symm

/-- [proved-standard; formal-checked] At a prime the digit streams are the `p`-adic integers, through
`padicSectionEquiv`. -/
noncomputable def streamEquivPadic (p : ℕ) [Fact p.Prime] : (ℕ → Fin p) ≃ ℤ_[p] :=
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  ((streamEquiv p).trans (sectionEquivPadicTower p)).trans (padicSectionEquiv p).symm

/-- [proved-standard; formal-checked] The level-`n` face of a stream's integer is the value of its first `n`
digits. -/
theorem toZModPow_streamEquivPadic (p : ℕ) [Fact p.Prime] (d : ℕ → Fin p) (n : ℕ) :
    PadicInt.toZModPow n (streamEquivPadic p d) = wordFace p (fun k : Fin n => d k) :=
  toZModPow_padicOfSection p _ n

/-- [proved-standard; formal-checked] Digit `k` of a `p`-adic integer is `(toZModPow (k+1) α).val / pᵏ mod p`. -/
theorem streamEquivPadic_symm_apply (p : ℕ) [Fact p.Prime] (a : ℤ_[p]) (k : ℕ) :
    ((streamEquivPadic p).symm a k : ℕ) = (PadicInt.toZModPow (k + 1) a).val / p ^ k % p :=
  finFunctionFinEquiv_symm_apply_val _ _

end Chart

/-! ## 2. Addition with carry, the top carry dropped -/

section Carry

variable (b : ℕ)

/-- [definition] The digit of a word at a place, zero above the word's top. -/
def digitAt {n : ℕ} (w : Fin n → Fin b) (k : ℕ) : ℕ := if h : k < n then (w ⟨k, h⟩ : ℕ) else 0

/-- [proved-standard; formal-checked] Every digit is below the base. -/
theorem digitAt_lt [NeZero b] {n : ℕ} (w : Fin n → Fin b) (k : ℕ) : digitAt b w k < b := by
  unfold digitAt
  split_ifs
  · exact (w _).isLt
  · exact NeZero.pos b

/-- [proved-standard; formal-checked] Inside the word the digit is the word's own. -/
theorem digitAt_fin {n : ℕ} (w : Fin n → Fin b) (k : Fin n) : digitAt b w k = w k :=
  dif_pos k.isLt

/-- [definition] The carry into place `k` of the sum of two words: `c_0 = 0`, `c_(k+1) = (w_k + w'_k + c_k) / b`. -/
def carry {n : ℕ} (w w' : Fin n → Fin b) : ℕ → ℕ
  | 0 => 0
  | k + 1 => (digitAt b w k + digitAt b w' k + carry w w' k) / b

/-- [definition] **Addition with carry**, place by place: digit `k` is `(w_k + w'_k + c_k) mod b`. -/
def addCarry [NeZero b] {n : ℕ} (w w' : Fin n → Fin b) : Fin n → Fin b :=
  fun k => ⟨(w k + w' k + carry b w w' k) % b, Nat.mod_lt _ (NeZero.pos b)⟩

/-- [proved-standard; formal-checked] The digit recurrence of the sum. -/
theorem addCarry_digit [NeZero b] {n : ℕ} (w w' : Fin n → Fin b) (k : Fin n) :
    (addCarry b w w' k : ℕ) = (w k + w' k + carry b w w' k) % b := rfl

/-- [proved-standard; formal-checked] No carry enters the lowest place. -/
theorem carry_zero {n : ℕ} (w w' : Fin n → Fin b) : carry b w w' 0 = 0 := rfl

/-- [proved-standard; formal-checked] The carry recurrence inside the word. -/
theorem carry_succ {n : ℕ} (w w' : Fin n → Fin b) (k : Fin n) :
    carry b w w' (k + 1) = (w k + w' k + carry b w w' k) / b := by
  rw [carry, digitAt_fin, digitAt_fin]

/-- [proved-standard; formal-checked] Every carry of two summands is a bit. -/
theorem carry_le_one [NeZero b] {n : ℕ} (w w' : Fin n → Fin b) : ∀ k, carry b w w' k ≤ 1
  | 0 => Nat.zero_le _
  | k + 1 => by
    have h1 := digitAt_lt b w k
    have h2 := digitAt_lt b w' k
    have h3 := carry_le_one w w' k
    have hlt : (digitAt b w k + digitAt b w' k + carry b w w' k) / b < 2 :=
      (Nat.div_lt_iff_lt_mul (NeZero.pos b)).mpr (by omega)
    exact Nat.lt_succ_iff.mp hlt

/-- [definition] The value of the places below `k`. -/
def lowValue {n : ℕ} (w : Fin n → Fin b) (k : ℕ) : ℕ := ∑ i ∈ Finset.range k, digitAt b w i * b ^ i

/-- [proved-standard; formal-checked] Below the top the low value is the word's value. -/
theorem lowValue_eq_value {n : ℕ} (w : Fin n → Fin b) : lowValue b w n = value b w := by
  rw [lowValue, ← Fin.sum_univ_eq_sum_range (fun i => digitAt b w i * b ^ i) n, value]
  exact Finset.sum_congr rfl fun i _ => by rw [digitAt_fin]

/-- [proved-standard; formal-checked] Below place `k ≤ n`: `low_k w + low_k w' = low_k (w + w') + c_k bᵏ`. -/
theorem lowValue_add [NeZero b] {n : ℕ} (w w' : Fin n → Fin b) :
    ∀ k, k ≤ n →
      lowValue b w k + lowValue b w' k = lowValue b (addCarry b w w') k + carry b w w' k * b ^ k
  | 0, _ => by simp [lowValue, carry]
  | k + 1, hk => by
    have hkn : k < n := hk
    have ih := lowValue_add w w' k (Nat.le_of_succ_le hk)
    have hs : digitAt b (addCarry b w w') k =
        (digitAt b w k + digitAt b w' k + carry b w w' k) % b := by
      simp only [digitAt, dif_pos hkn]
      rfl
    have hc : carry b w w' (k + 1) = (digitAt b w k + digitAt b w' k + carry b w w' k) / b := rfl
    have hmod := Nat.mod_add_div (digitAt b w k + digitAt b w' k + carry b w w' k) b
    simp only [lowValue, Finset.sum_range_succ] at ih ⊢
    rw [hs, hc, pow_succ]
    generalize (digitAt b w k + digitAt b w' k + carry b w w' k) % b = r at hmod ⊢
    generalize (digitAt b w k + digitAt b w' k + carry b w w' k) / b = q at hmod ⊢
    generalize ∑ i ∈ Finset.range k, digitAt b w i * b ^ i = L at ih ⊢
    generalize ∑ i ∈ Finset.range k, digitAt b w' i * b ^ i = L' at ih ⊢
    generalize ∑ i ∈ Finset.range k, digitAt b (addCarry b w w') i * b ^ i = S at ih ⊢
    generalize digitAt b w k = d at hmod ⊢
    generalize digitAt b w' k = d' at hmod ⊢
    generalize carry b w w' k = c at hmod ih ⊢
    generalize b ^ k = B at ih ⊢
    linear_combination ih - B * hmod

/-- [proved-standard; formal-checked] At the top: `value (w + w') + c_n bⁿ = value w + value w'`. -/
theorem value_addCarry [NeZero b] {n : ℕ} (w w' : Fin n → Fin b) :
    value b (addCarry b w w') + carry b w w' n * b ^ n = value b w + value b w' := by
  have h := lowValue_add b w w' n le_rfl
  rw [lowValue_eq_value, lowValue_eq_value, lowValue_eq_value] at h
  exact h.symm

/-- [proved-standard; formal-checked] The released top carry is `⌊(value w + value w') / bⁿ⌋`. -/
theorem topCarry_eq [NeZero b] {n : ℕ} (w w' : Fin n → Fin b) :
    carry b w w' n = (value b w + value b w') / b ^ n := by
  have hB : 0 < b ^ n := pow_pos (NeZero.pos b) n
  rw [← value_addCarry, Nat.add_mul_div_right _ _ hB, Nat.div_eq_of_lt (value_lt b _), zero_add]

/-- [proved-standard; formal-checked] The sum's value is the summands' value modulo `bⁿ`. -/
theorem value_addCarry_eq_mod [NeZero b] {n : ℕ} (w w' : Fin n → Fin b) :
    value b (addCarry b w w') = (value b w + value b w') % b ^ n := by
  rw [← value_addCarry, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (value_lt b _)]

/-- [proved-standard; formal-checked] **The chart carries the adder to addition in `ZMod (b ^ n)`.** -/
theorem chartEquiv_addCarry [NeZero b] {n : ℕ} (w w' : Fin n → Fin b) :
    chartEquiv b n (addCarry b w w') = chartEquiv b n w + chartEquiv b n w' := by
  show wordFace b (addCarry b w w') = wordFace b w + wordFace b w'
  rw [wordFace, wordFace, wordFace, ← Nat.cast_add, ← value_addCarry, Nat.cast_add, Nat.cast_mul,
    ZMod.natCast_self, mul_zero, add_zero]

/-- [proved-standard; formal-checked] The adder is the ring's addition transported by the chart. -/
theorem addCarry_eq_transport [NeZero b] {n : ℕ} (w w' : Fin n → Fin b) :
    addCarry b w w' = (chartEquiv b n).symm (chartEquiv b n w + chartEquiv b n w') := by
  rw [← chartEquiv_addCarry, Equiv.symm_apply_apply]

/-- [proved-standard; formal-checked] Truncation keeps the digits below its top. -/
theorem digitAt_truncate {m n : ℕ} (h : m ≤ n) (w : Fin n → Fin b) {k : ℕ} (hk : k < m) :
    digitAt b (truncate b h w) k = digitAt b w k := by
  simp only [digitAt, dif_pos hk, dif_pos (lt_of_lt_of_le hk h)]
  rfl

/-- [proved-standard; formal-checked] The carry into place `k ≤ m` reads only the places below it: carries flow up. -/
theorem carry_truncate {m n : ℕ} (h : m ≤ n) (w w' : Fin n → Fin b) :
    ∀ k, k ≤ m → carry b (truncate b h w) (truncate b h w') k = carry b w w' k
  | 0, _ => rfl
  | k + 1, hk => by
    have hkm : k < m := hk
    show (_ + _ + _) / b = (_ + _ + _) / b
    rw [digitAt_truncate b h w hkm, digitAt_truncate b h w' hkm,
      carry_truncate h w w' k (Nat.le_of_succ_le hk)]

/-- [proved-standard; formal-checked] **Truncation commutes with addition with carry.** -/
theorem truncate_addCarry [NeZero b] {m n : ℕ} (h : m ≤ n) (w w' : Fin n → Fin b) :
    truncate b h (addCarry b w w') = addCarry b (truncate b h w) (truncate b h w') := by
  funext k
  apply Fin.ext
  show (w (Fin.castLE h k) + w' (Fin.castLE h k) + carry b w w' k) % b =
    (w (Fin.castLE h k) + w' (Fin.castLE h k) + carry b (truncate b h w) (truncate b h w') k) % b
  rw [carry_truncate b h w w' k k.isLt.le]

/-- [definition] Multiplication of words, transported from `ZMod (b ^ n)` by the chart. -/
def mulCarry [NeZero b] {n : ℕ} (w w' : Fin n → Fin b) : Fin n → Fin b :=
  (chartEquiv b n).symm (chartEquiv b n w * chartEquiv b n w')

/-- [proved-standard; formal-checked] The product's value is `value w · value w' mod bⁿ`. -/
theorem value_mulCarry [NeZero b] {n : ℕ} (w w' : Fin n → Fin b) :
    value b (mulCarry b w w') = value b w * value b w' % b ^ n := by
  rw [mulCarry, show (chartEquiv b n).symm = digits b n from rfl, value_digits]
  show ((value b w : ZMod (b ^ n)) * (value b w' : ZMod (b ^ n))).val = _
  rw [← Nat.cast_mul, ZMod.val_natCast]

/-- [proved-standard; formal-checked] Truncation commutes with multiplication (the trailing face is a ring map). -/
theorem truncate_mulCarry [NeZero b] {m n : ℕ} (h : m ≤ n) (w w' : Fin n → Fin b) :
    truncate b h (mulCarry b w w') = mulCarry b (truncate b h w) (truncate b h w') := by
  apply (chartEquiv b m).injective
  show wordFace b (truncate b h (mulCarry b w w')) = chartEquiv b m (mulCarry b _ _)
  rw [wordFace_truncate, mulCarry, mulCarry, Equiv.apply_symm_apply]
  show (padicTower b).restrict h (chartEquiv b n ((chartEquiv b n).symm _)) = _
  rw [Equiv.apply_symm_apply]
  show ZMod.castHom (pow_dvd_pow b h) (ZMod (b ^ m)) (wordFace b w * wordFace b w') =
    wordFace b (truncate b h w) * wordFace b (truncate b h w')
  rw [map_mul, wordFace_truncate, wordFace_truncate]
  rfl

end Carry

/-! ## 3. The nonunique fibre -/

section Fibre

variable (b : ℕ)

/-- [proved-standard; formal-checked] The lifts of a level-`m` face to level `m + k` are the free choices of the
upper `k` digits. -/
def fibreEquiv {m k : ℕ} (face : Fin m → Fin b) :
    {w : Fin (m + k) → Fin b // (carryTower b).restrict (Nat.le_add_right m k) w = face} ≃
      (Fin k → Fin b) where
  toFun w j := w.1 (Fin.natAdd m j)
  invFun u := ⟨Fin.append face u, funext fun i => Fin.append_left face u i⟩
  left_inv w := by
    obtain ⟨w, rfl⟩ := w
    exact Subtype.ext Fin.append_castAdd_natAdd
  right_inv u := funext fun j => Fin.append_right face u j

/-- [proved-standard; formal-checked] Exactly `bᵏ` lifts at level `m + k`. -/
theorem fibre_card_add {m k : ℕ} (face : Fin m → Fin b) :
    Nat.card {w : Fin (m + k) → Fin b //
      (carryTower b).restrict (Nat.le_add_right m k) w = face} = b ^ k := by
  rw [Nat.card_congr (fibreEquiv b face), Nat.card_fun, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card, Fintype.card_fin, Fintype.card_fin]

/-- [proved-standard; formal-checked] **The nonunique fibre**: a level-`m` face has `b ^ (n − m)` lifts at `n`. -/
theorem fibre_card {m n : ℕ} (h : m ≤ n) (face : Fin m → Fin b) :
    Nat.card {w : Fin n → Fin b // (carryTower b).restrict h w = face} = b ^ (n - m) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_sub_cancel_left]
  exact fibre_card_add b face

/-- [proved-standard; formal-checked] For `b ≥ 1` every restriction of the carry tower is surjective. -/
theorem restrict_surjective [NeZero b] {m n : ℕ} (h : m ≤ n) :
    Function.Surjective fun w : Fin n → Fin b => (carryTower b).restrict h w := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  intro face
  refine ⟨Fin.append face (fun _ : Fin k => (0 : Fin b)), funext fun i => ?_⟩
  exact Fin.append_left face (fun _ : Fin k => (0 : Fin b)) i

/-- [proved-standard; formal-checked] For `b ≥ 2` and `n > m` no restriction of the carry tower is injective. -/
theorem restrict_not_injective (hb : 1 < b) {m n : ℕ} (h : m < n) :
    ¬ Function.Injective fun w : Fin n → Fin b => (carryTower b).restrict h.le w := by
  intro hinj
  have h0 : 0 < b := by omega
  have hr : (carryTower b).restrict h.le
      (fun i : Fin n => if (i : ℕ) = m then (⟨1, hb⟩ : Fin b) else ⟨0, h0⟩) =
      (carryTower b).restrict h.le (fun _ : Fin n => (⟨0, h0⟩ : Fin b)) := by
    funext i
    show (if ((Fin.castLE h.le i : Fin n) : ℕ) = m then (⟨1, hb⟩ : Fin b) else ⟨0, h0⟩) = ⟨0, h0⟩
    rw [if_neg (by simp only [Fin.val_castLE]; exact Nat.ne_of_lt i.isLt)]
  have := congrFun (hinj hr) ⟨m, h⟩
  rw [if_pos rfl] at this
  exact absurd (congrArg Fin.val this) one_ne_zero

/-- [proved-derived; formal-checked] For `b ≥ 2` the carry tower has more than one continuing object. -/
theorem carryTower_plural (hb : 1 < b) : ¬ Subsingleton (carryTower b).CompatibleSection := by
  intro hsub
  have h0 : 0 < b := by omega
  have := congrArg (fun s : (carryTower b).CompatibleSection => sectionStream b s 0)
    (Subsingleton.elim (streamSection b fun _ => ⟨0, h0⟩) (streamSection b fun _ => ⟨1, hb⟩))
  simp only [sectionStream, streamSection, Fin.mk.injEq, zero_ne_one] at this

/-- [proved-derived; formal-checked] For `b ≥ 2` the carry tower lands in the `plural` arm. -/
theorem carryTower_gluing (hb : 1 < b) : (carryTower b).GluingResult :=
  .plural ⟨streamSection b fun _ => ⟨0, by omega⟩⟩ (carryTower_plural b hb)

/-- [proved-derived; formal-checked] At a prime the plurality is `padicTower_plural`, carried by the migrations. -/
theorem carryTower_plural_via_padic (p : ℕ) [Fact p.Prime] :
    ¬ Subsingleton (carryTower p).CompatibleSection := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rw [(sectionEquivPadicTower p).subsingleton_congr]
  exact padicTower_plural p

/-- [proved-derived; formal-checked] Every lift of a face is reached by a continuing object behind that face. -/
theorem observationFibre_reaches [NeZero b] {m n : ℕ} (h : m ≤ n) (face : Fin m → Fin b)
    (x : Fin n → Fin b) (hx : (carryTower b).restrict h x = face) :
    ∃ s : (carryTower b).ObservationFibre m face, s.1.witness n = x := by
  obtain ⟨d, hd⟩ : ∃ d : ℕ → Fin b, d = fun k => if hk : k < n then x ⟨k, hk⟩ else 0 := ⟨_, rfl⟩
  have hw : (streamSection b d).witness n = x := funext fun k => by
    show d k = x k
    rw [hd]
    exact dif_pos k.isLt
  refine ⟨⟨streamSection b d, ?_⟩, hw⟩
  rw [← hx, ← (streamSection b d).compatible h, hw]

end Fibre

/-! ## 4. The tail of a tower above one face -/

section Above

universe v

variable (T : Tower.{0, v} ℕ)

/-- [definition] The tail above a face `a` at level `k`: at level `j`, the faces at `k + j` lying over `a`. -/
def aboveTower (k : ℕ) (a : T.Face k) : Tower.{0, v} ℕ where
  Face j := {x : T.Face (k + j) // T.restrict (Nat.le_add_right k j) x = a}
  restrict {i _} h x := ⟨T.restrict (Nat.add_le_add_left h k) x.1,
    (T.restrict_trans (Nat.le_add_right k i) (Nat.add_le_add_left h k) x.1).trans x.2⟩
  restrict_refl j x := Subtype.ext (T.restrict_refl (k + j) x.1)
  restrict_trans _ _ x := Subtype.ext (T.restrict_trans _ _ x.1)

/-- [definition] A continuing object of the tail read on the whole tower, each level restricted from above. -/
def aboveSection (k : ℕ) (a : T.Face k) (s : (aboveTower T k a).CompatibleSection) :
    T.CompatibleSection where
  witness n := T.restrict (Nat.le_add_left n k) (s.witness n).1
  compatible {i j} h := by
    have hs : T.restrict (Nat.add_le_add_left h k) (s.witness j).1 = (s.witness i).1 :=
      congrArg Subtype.val (s.compatible h)
    rw [T.restrict_trans, ← hs, T.restrict_trans]

/-- [proved-derived; formal-checked] That object presents `a` at level `k`. -/
theorem aboveSection_witness (k : ℕ) (a : T.Face k) (s : (aboveTower T k a).CompatibleSection) :
    (aboveSection T k a s).witness k = a := by
  have hs : T.restrict (Nat.add_le_add_left (Nat.zero_le k) k) (s.witness k).1 = (s.witness 0).1 :=
    congrArg Subtype.val (s.compatible (Nat.zero_le k))
  calc T.restrict (Nat.le_add_left k k) (s.witness k).1
      = T.restrict (Nat.le_add_right k 0)
          (T.restrict (Nat.add_le_add_left (Nat.zero_le k) k) (s.witness k).1) :=
        (T.restrict_trans _ _ _).symm
    _ = T.restrict (Nat.le_add_right k 0) (s.witness 0).1 := by rw [hs]
    _ = a := (s.witness 0).2

/-- [proved-derived; formal-checked] **The tail's continuing objects are the observation fibre behind `a`.** -/
def aboveSectionEquiv (k : ℕ) (a : T.Face k) :
    (aboveTower T k a).CompatibleSection ≃ T.ObservationFibre k a where
  toFun s := ⟨aboveSection T k a s, aboveSection_witness T k a s⟩
  invFun t :=
    { witness := fun j => ⟨t.1.witness (k + j), (t.1.compatible (Nat.le_add_right k j)).trans t.2⟩
      compatible := fun _ => Subtype.ext (t.1.compatible _) }
  left_inv s := Tower.CompatibleSection.ext fun j =>
    Subtype.ext (congrArg Subtype.val (s.compatible (Nat.le_add_left j k)))
  right_inv t :=
    Subtype.ext (Tower.CompatibleSection.ext fun n => t.1.compatible (Nat.le_add_left n k))

/-- [proved-derived; formal-checked] A one-point base and bijective adjacent restrictions give one section. -/
theorem unique_of_bijectiveAdjacent (hbase : Nonempty (T.Face 0)) (hsub : Subsingleton (T.Face 0))
    (hbij : ∀ n, Function.Bijective fun x : T.Face (n + 1) => T.restrict (Nat.le_succ n) x) :
    Nonempty T.CompatibleSection ∧ Subsingleton T.CompatibleSection := by
  refine ⟨Tower.nonempty_compatibleSection_of_surjectiveAdjacent T hbase fun n => (hbij n).2,
    ⟨fun s t => Tower.CompatibleSection.ext fun n => ?_⟩⟩
  induction n with
  | zero => exact Subsingleton.elim _ _
  | succ n ih =>
    exact (hbij n).1 ((s.compatible (Nat.le_succ n)).trans (ih.trans (t.compatible _).symm))

/-- [proved-derived; formal-checked] Such a tower lands in the `unique` arm. -/
theorem gluing_unique_of_bijectiveAdjacent (hbase : Nonempty (T.Face 0))
    (hsub : Subsingleton (T.Face 0))
    (hbij : ∀ n, Function.Bijective fun x : T.Face (n + 1) => T.restrict (Nat.le_succ n) x) :
    T.GluingResult :=
  .unique (unique_of_bijectiveAdjacent T hbase hsub hbij).1
    (unique_of_bijectiveAdjacent T hbase hsub hbij).2

end Above

/-! ## 5. The lifting condition -/

section Hensel

open Polynomial

/-- [proved-standard; formal-checked] Evaluation of an integer polynomial commutes with every ring map. -/
theorem aeval_ringHom {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (x : R) (f : ℤ[X]) :
    aeval (φ x) f = φ (aeval x f) :=
  aeval_algHom_apply φ.toIntAlgHom x f

/-- [proved-standard; formal-checked] At an integer the evaluation is the cast of the integer value. -/
theorem aeval_intCast {R : Type*} [CommRing R] (f : ℤ[X]) (A : ℤ) :
    aeval (A : R) f = ((f.eval A : ℤ) : R) := by
  have h := aeval_ringHom (Int.castRingHom R) A f
  rw [coe_aeval_eq_eval] at h
  exact h

variable (p : ℕ)

/-- [proved-standard; formal-checked] The restriction of `padicTower p` keeps an integer's cast. -/
theorem restrict_intCast {m n : ℕ} (h : m ≤ n) (A : ℤ) :
    (padicTower p).restrict h (A : ZMod (p ^ n)) = (A : ZMod (p ^ m)) :=
  map_intCast (ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ m))) A

/-- [proved-standard; formal-checked] An integer is a root on the face `ZMod (p ^ n)` iff `pⁿ ∣ f(A)`. -/
theorem aeval_intCast_eq_zero_iff (f : ℤ[X]) (n : ℕ) (A : ℤ) :
    aeval (A : ZMod (p ^ n)) f = 0 ↔ (p : ℤ) ^ n ∣ f.eval A := by
  rw [aeval_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd, Nat.cast_pow]

/-- [definition] **The root tower** of `f ∈ ℤ[X]`: the roots of `f` on each face of `padicTower p`, restricted as
`padicTower p` restricts. -/
def rootTower (f : ℤ[X]) : Tower.{0, 0} ℕ where
  Face n := {x : ZMod (p ^ n) // aeval x f = 0}
  restrict h x := ⟨(padicTower p).restrict h x.1, by
    show aeval (ZMod.castHom (pow_dvd_pow p h) _ x.1) f = 0
    rw [aeval_ringHom, x.2, map_zero]⟩
  restrict_refl n x := Subtype.ext ((padicTower p).restrict_refl n x.1)
  restrict_trans hij hjk x := Subtype.ext ((padicTower p).restrict_trans hij hjk x.1)

/-- [proved-standard; formal-checked] The Taylor step: for `n ≥ 1`, `f(A + t pⁿ) ≡ f(A) + t pⁿ f'(A) (mod pⁿ⁺¹)`. -/
theorem taylor_step (f : ℤ[X]) {n : ℕ} (hn : 1 ≤ n) (A t : ℤ) :
    (p : ℤ) ^ (n + 1) ∣
      f.eval (A + t * (p : ℤ) ^ n) - (f.eval A + t * (p : ℤ) ^ n * f.derivative.eval A) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨K, hK⟩ := binomExpansion f A (t * (p : ℤ) ^ (m + 1))
  rw [hK]
  exact ⟨K * t ^ 2 * (p : ℤ) ^ m, by ring⟩

/-- [proved-standard; formal-checked] Hensel's step on ℤ: a root mod `pⁿ` with `p ∤ f'(A)` lifts to mod `pⁿ⁺¹`. -/
theorem hensel_int_exists [Fact p.Prime] (f : ℤ[X]) {n : ℕ} (hn : 1 ≤ n) {A : ℤ}
    (hA : (p : ℤ) ^ n ∣ f.eval A) (hd : ¬ (p : ℤ) ∣ f.derivative.eval A) :
    ∃ B : ℤ, (p : ℤ) ^ n ∣ B - A ∧ (p : ℤ) ^ (n + 1) ∣ f.eval B := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp Fact.out
  obtain ⟨q, hq⟩ := hA
  obtain ⟨u, v, huv⟩ := (Irreducible.coprime_iff_not_dvd hp.irreducible).mpr hd
  refine ⟨A + -(q * v) * (p : ℤ) ^ (m + 1), ⟨-(q * v), by ring⟩, ?_⟩
  obtain ⟨K, hK⟩ := binomExpansion f A (-(q * v) * (p : ℤ) ^ (m + 1))
  rw [hK, hq]
  exact ⟨q * u + K * (q * v) ^ 2 * (p : ℤ) ^ m, by linear_combination (-(p : ℤ) ^ (m + 1) * q) * huv⟩

/-- [proved-standard; formal-checked] Hensel's step on ℤ, uniqueness: two such lifts agree modulo `pⁿ⁺¹`. -/
theorem hensel_int_unique [Fact p.Prime] (f : ℤ[X]) {n : ℕ} (hn : 1 ≤ n) {A : ℤ}
    (hd : ¬ (p : ℤ) ∣ f.derivative.eval A) {B₁ B₂ : ℤ} (h₁ : (p : ℤ) ^ n ∣ B₁ - A)
    (h₂ : (p : ℤ) ^ n ∣ B₂ - A) (r₁ : (p : ℤ) ^ (n + 1) ∣ f.eval B₁)
    (r₂ : (p : ℤ) ^ (n + 1) ∣ f.eval B₂) : (p : ℤ) ^ (n + 1) ∣ B₂ - B₁ := by
  have hp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp Fact.out
  have hd₁ : ¬ (p : ℤ) ∣ f.derivative.eval B₁ := by
    intro h
    apply hd
    have hpB : (p : ℤ) ∣ B₁ - A := (dvd_pow_self (p : ℤ) (by omega)).trans h₁
    have := dvd_sub h (hpB.trans (sub_dvd_eval_sub B₁ A f.derivative))
    rwa [sub_sub_cancel] at this
  obtain ⟨e, he⟩ : (p : ℤ) ^ n ∣ B₂ - B₁ := by
    have := dvd_sub h₂ h₁
    rwa [sub_sub_sub_cancel_right] at this
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨K, hK⟩ := binomExpansion f B₁ (B₂ - B₁)
  rw [add_sub_cancel] at hK
  have hlin : (p : ℤ) ^ (m + 1 + 1) ∣ f.derivative.eval B₁ * (B₂ - B₁) := by
    have hsq : (p : ℤ) ^ (m + 1 + 1) ∣ K * (B₂ - B₁) ^ 2 :=
      ⟨K * e ^ 2 * (p : ℤ) ^ m, by rw [he]; ring⟩
    have := dvd_sub (dvd_sub r₂ r₁) hsq
    rwa [hK, show f.eval B₁ + f.derivative.eval B₁ * (B₂ - B₁) + K * (B₂ - B₁) ^ 2 - f.eval B₁ -
      K * (B₂ - B₁) ^ 2 = f.derivative.eval B₁ * (B₂ - B₁) by ring] at this
  rw [he, pow_succ, mul_left_comm] at hlin
  have hpe : (p : ℤ) ∣ f.derivative.eval B₁ * e :=
    (mul_dvd_mul_iff_left (pow_ne_zero _ hp.ne_zero)).mp hlin
  rw [he, pow_succ]
  exact mul_dvd_mul_left _ ((hp.dvd_or_dvd hpe).resolve_left hd₁)

/-- [proved-standard; formal-checked] **Hensel's lift**: a root whose level-1 face has `f' ≠ 0` lifts in one way. -/
theorem hensel_lift [Fact p.Prime] (f : ℤ[X]) {n : ℕ} (hn : 1 ≤ n) (x : ZMod (p ^ n))
    (hx : aeval x f = 0) (hd : aeval (A := ZMod (p ^ 1)) ((padicTower p).restrict hn x) (derivative f) ≠ 0) :
    ∃! y : ZMod (p ^ (n + 1)), (padicTower p).restrict (Nat.le_succ n) y = x ∧ aeval y f = 0 := by
  obtain ⟨A, rfl⟩ := ZMod.intCast_surjective x
  rw [restrict_intCast] at hd
  have hd' : ¬ (p : ℤ) ∣ f.derivative.eval A := by
    intro h
    apply hd
    rw [aeval_intCast_eq_zero_iff, pow_one]
    exact h
  rw [aeval_intCast_eq_zero_iff] at hx
  obtain ⟨B, hBA, hB⟩ := hensel_int_exists p f hn hx hd'
  refine ⟨(B : ZMod (p ^ (n + 1))), ⟨?_, (aeval_intCast_eq_zero_iff p f _ B).mpr hB⟩, ?_⟩
  · rw [restrict_intCast]
    exact ((ZMod.intCast_eq_intCast_iff_dvd_sub A B (p ^ n)).mpr (by rw [Nat.cast_pow]; exact hBA)).symm
  · rintro y ⟨hy, hyr⟩
    obtain ⟨C, rfl⟩ := ZMod.intCast_surjective y
    rw [restrict_intCast] at hy
    have hy' := (ZMod.intCast_eq_intCast_iff_dvd_sub A C (p ^ n)).mp hy.symm
    rw [Nat.cast_pow] at hy'
    rw [aeval_intCast_eq_zero_iff] at hyr
    exact ((ZMod.intCast_eq_intCast_iff_dvd_sub B C (p ^ (n + 1))).mpr
      (by rw [Nat.cast_pow]; exact hensel_int_unique p f hn hd' hBA hy' hB hyr)).symm

/-- [proved-standard; formal-checked] The same lift read on the root tower's own faces. -/
theorem rootTower_lift_unique [Fact p.Prime] (f : ℤ[X]) {n : ℕ} (hn : 1 ≤ n)
    (x : (rootTower p f).Face n)
    (hd : aeval (A := ZMod (p ^ 1)) ((padicTower p).restrict hn x.1) (derivative f) ≠ 0) :
    ∃! y : (rootTower p f).Face (n + 1), (rootTower p f).restrict (Nat.le_succ n) y = x := by
  obtain ⟨z, ⟨hzx, hzr⟩, hz⟩ := hensel_lift p f hn x.1 x.2 hd
  exact ⟨⟨z, hzr⟩, Subtype.ext hzx, fun y hy => Subtype.ext (hz y.1 ⟨congrArg Subtype.val hy, y.2⟩)⟩

/-- [proved-standard; formal-checked] Restricting to level 1 passes through every level between. -/
theorem restrict_one_trans {k n : ℕ} (hk : 1 ≤ k) (h : k ≤ n) (x : ZMod (p ^ n)) :
    (padicTower p).restrict (le_trans hk h) x =
      (padicTower p).restrict hk ((padicTower p).restrict h x) :=
  ((padicTower p).restrict_trans hk h x).symm

/-- [proved-standard; formal-checked] Above a root meeting the condition the adjacent restrictions are bijective. -/
theorem hensel_adjacent_bijective [Fact p.Prime] (f : ℤ[X]) {k : ℕ} (hk : 1 ≤ k)
    (a : (rootTower p f).Face k)
    (hd : aeval (A := ZMod (p ^ 1)) ((padicTower p).restrict hk a.1) (derivative f) ≠ 0) (j : ℕ) :
    Function.Bijective fun x : (aboveTower (rootTower p f) k a).Face (j + 1) =>
      (aboveTower (rootTower p f) k a).restrict (Nat.le_succ j) x := by
  have hdx : ∀ x : (aboveTower (rootTower p f) k a).Face j,
      aeval (A := ZMod (p ^ 1)) ((padicTower p).restrict (le_trans hk (Nat.le_add_right k j)) x.1.1)
        (derivative f) ≠ 0 := by
    intro x
    rw [restrict_one_trans p hk (Nat.le_add_right k j)]
    have hxa : (padicTower p).restrict (Nat.le_add_right k j) x.1.1 = a.1 := congrArg Subtype.val x.2
    rw [hxa]
    exact hd
  constructor
  · intro y₁ y₂ hy
    obtain ⟨z, _, hz⟩ := hensel_lift p f (le_trans hk (Nat.le_add_right k j)) _
      ((aboveTower (rootTower p f) k a).restrict (Nat.le_succ j) y₁).1.2 (hdx _)
    have e₁ := hz y₁.1.1 ⟨rfl, y₁.1.2⟩
    have e₂ := hz y₂.1.1 ⟨congrArg (fun u => u.1.1) hy.symm, y₂.1.2⟩
    exact Subtype.ext (Subtype.ext (e₁.trans e₂.symm))
  · intro x
    obtain ⟨z, ⟨hzx, hzr⟩, _⟩ :=
      hensel_lift p f (le_trans hk (Nat.le_add_right k j)) x.1.1 x.1.2 (hdx x)
    have hzx' : (rootTower p f).restrict (Nat.le_succ (k + j)) ⟨z, hzr⟩ = x.1 := Subtype.ext hzx
    refine ⟨⟨⟨z, hzr⟩, ?_⟩, Subtype.ext hzx'⟩
    calc (rootTower p f).restrict (Nat.le_add_right k (j + 1)) ⟨z, hzr⟩
        = (rootTower p f).restrict (Nat.le_add_right k j)
            ((rootTower p f).restrict (Nat.le_succ (k + j)) ⟨z, hzr⟩) :=
          ((rootTower p f).restrict_trans _ _ _).symm
      _ = a := by rw [hzx']; exact x.2

/-- [proved-derived; formal-checked] The tail above a root has a one-point base: the root itself. -/
theorem henselThread_base (f : ℤ[X]) {k : ℕ} (a : (rootTower p f).Face k) :
    Nonempty ((aboveTower (rootTower p f) k a).Face 0) ∧
      Subsingleton ((aboveTower (rootTower p f) k a).Face 0) := by
  refine ⟨⟨⟨a, (rootTower p f).restrict_refl k a⟩⟩, ⟨fun x y => Subtype.ext ?_⟩⟩
  calc x.1 = (rootTower p f).restrict (Nat.le_add_right k 0) x.1 :=
        ((rootTower p f).restrict_self_eq_id (i := k) (Nat.le_add_right k 0) x.1).symm
    _ = (rootTower p f).restrict (Nat.le_add_right k 0) y.1 := x.2.trans y.2.symm
    _ = y.1 := (rootTower p f).restrict_self_eq_id (i := k) (Nat.le_add_right k 0) y.1

/-- [proved-standard; formal-checked] The thread above a root meeting the condition lands in the `unique` arm. -/
theorem henselThread_gluing [Fact p.Prime] (f : ℤ[X]) {k : ℕ} (hk : 1 ≤ k)
    (a : (rootTower p f).Face k)
    (hd : aeval (A := ZMod (p ^ 1)) ((padicTower p).restrict hk a.1) (derivative f) ≠ 0) :
    (aboveTower (rootTower p f) k a).GluingResult :=
  gluing_unique_of_bijectiveAdjacent _ (henselThread_base p f a).1 (henselThread_base p f a).2
    (hensel_adjacent_bijective p f hk a hd)

/-- [proved-standard; formal-checked] The root tower's observation fibre behind such a root has exactly one point. -/
theorem hensel_observationFibre [Fact p.Prime] (f : ℤ[X]) {k : ℕ} (hk : 1 ≤ k)
    (a : (rootTower p f).Face k)
    (hd : aeval (A := ZMod (p ^ 1)) ((padicTower p).restrict hk a.1) (derivative f) ≠ 0) :
    Nonempty ((rootTower p f).ObservationFibre k a) ∧
      Subsingleton ((rootTower p f).ObservationFibre k a) := by
  obtain ⟨hne, hss⟩ := unique_of_bijectiveAdjacent _ (henselThread_base p f a).1
    (henselThread_base p f a).2 (hensel_adjacent_bijective p f hk a hd)
  exact ⟨(aboveSectionEquiv _ k a).nonempty_congr.mp hne,
    (aboveSectionEquiv _ k a).subsingleton_congr.mp hss⟩

/-- [proved-standard; formal-checked] **Exactly one thread of roots passes through a root meeting the condition.** -/
theorem hensel_thread_unique [Fact p.Prime] (f : ℤ[X]) {k : ℕ} (hk : 1 ≤ k) (a : ZMod (p ^ k))
    (ha : aeval a f = 0)
    (hd : aeval (A := ZMod (p ^ 1)) ((padicTower p).restrict hk a) (derivative f) ≠ 0) :
    ∃! s : (rootTower p f).CompatibleSection, (s.witness k).1 = a := by
  obtain ⟨⟨s, hs⟩, hss⟩ := hensel_observationFibre p f hk ⟨a, ha⟩ hd
  refine ⟨s, congrArg Subtype.val hs, fun t ht => ?_⟩
  have := hss.elim ⟨t, Subtype.ext ht⟩ ⟨s, hs⟩
  exact congrArg Subtype.val this

/-- [definition] A thread of roots read as a thread of `padicTower p`. -/
def forgetRoots (f : ℤ[X]) (s : (rootTower p f).CompatibleSection) :
    (padicTower p).CompatibleSection where
  witness n := (s.witness n).1
  compatible h := congrArg Subtype.val (s.compatible h)

/-- [proved-standard; formal-checked] The root tower's compatible sections are the roots of `f` in `ℤ_[p]`. -/
noncomputable def rootSectionEquiv [Fact p.Prime] (f : ℤ[X]) :
    (rootTower p f).CompatibleSection ≃ {α : ℤ_[p] // aeval α f = 0} where
  toFun s := ⟨padicOfSection p (forgetRoots p f s), PadicInt.ext_of_toZModPow.mp fun n => by
    rw [← aeval_ringHom, toZModPow_padicOfSection, map_zero]
    exact (s.witness n).2⟩
  invFun α :=
    { witness := fun n => ⟨PadicInt.toZModPow n α.1, by rw [aeval_ringHom, α.2, map_zero]⟩
      compatible := fun h => Subtype.ext ((padicSection p α.1).compatible h) }
  left_inv s := Tower.CompatibleSection.ext fun n =>
    Subtype.ext (toZModPow_padicOfSection p (forgetRoots p f s) n)
  right_inv α := Subtype.ext ((padicSectionEquiv p).left_inv α.1)

/-- [proved-standard; formal-checked] The root a thread names presents the thread's face at every level. -/
theorem rootSectionEquiv_witness [Fact p.Prime] (f : ℤ[X]) (s : (rootTower p f).CompatibleSection)
    (n : ℕ) : PadicInt.toZModPow n (rootSectionEquiv p f s).1 = (s.witness n).1 :=
  toZModPow_padicOfSection p (forgetRoots p f s) n

/-- [proved-standard; formal-checked] **Hensel on `ℤ_[p]`**: such a root mod `pᵏ` is the face of one root in `ℤ_[p]`. -/
theorem hensel_padic_root_unique [Fact p.Prime] (f : ℤ[X]) {k : ℕ} (hk : 1 ≤ k) (a : ZMod (p ^ k))
    (ha : aeval a f = 0)
    (hd : aeval (A := ZMod (p ^ 1)) ((padicTower p).restrict hk a) (derivative f) ≠ 0) :
    ∃! α : ℤ_[p], aeval α f = 0 ∧ PadicInt.toZModPow k α = a := by
  obtain ⟨s, hs, hu⟩ := hensel_thread_unique p f hk a ha hd
  refine ⟨(rootSectionEquiv p f s).1, ⟨(rootSectionEquiv p f s).2,
    (rootSectionEquiv_witness p f s k).trans hs⟩, fun β ⟨hβ, hβk⟩ => ?_⟩
  have ht := hu ((rootSectionEquiv p f).symm ⟨β, hβ⟩) hβk
  have := congrArg (fun t => ((rootSectionEquiv p f) t).1) ht
  simpa only [Equiv.apply_symm_apply] using this

/-- [proved-standard; formal-checked] At level 1 the condition reads on the root itself: `f'(a) ≠ 0`. -/
theorem hensel_thread_unique_one [Fact p.Prime] (f : ℤ[X]) (a : ZMod (p ^ 1))
    (ha : aeval a f = 0) (hd : aeval a (derivative f) ≠ 0) :
    ∃! s : (rootTower p f).CompatibleSection, (s.witness 1).1 = a := by
  have hr : (padicTower p).restrict (le_refl 1) a = a := (padicTower p).restrict_refl 1 a
  exact hensel_thread_unique p f le_rfl a ha (by rw [hr]; exact hd)

end Hensel

/-! ## 6. Where the lifting condition fails, and where it holds -/

section Counterexamples

open Polynomial

/-- [proved-standard; formal-checked] `X²` at `p = 2`: `0` is a root modulo `2` and `f'(0) = 0` there. -/
theorem square_lifting_condition_fails :
    aeval (0 : ZMod (2 ^ 1)) (X ^ 2 : ℤ[X]) = 0 ∧
      aeval (0 : ZMod (2 ^ 1)) (derivative (X ^ 2 : ℤ[X])) = 0 := by
  constructor
  · simp
  · simp [map_ofNat (aeval (0 : ZMod (2 ^ 1)))]

/-- [proved-standard; formal-checked] The root `0` modulo `2` of `X²` has two root lifts modulo `4`, `0` and `2`. -/
theorem square_root_lifts_twice :
    ∃ y₀ y₂ : (rootTower 2 (X ^ 2 : ℤ[X])).Face 2, y₀ ≠ y₂ ∧
      ((rootTower 2 (X ^ 2 : ℤ[X])).restrict (Nat.le_succ 1) y₀).1 = 0 ∧
      ((rootTower 2 (X ^ 2 : ℤ[X])).restrict (Nat.le_succ 1) y₂).1 = 0 := by
  refine ⟨⟨0, by simp⟩, ⟨2, by rw [map_pow, aeval_X]; decide⟩, fun h => ?_, ?_, ?_⟩
  · exact absurd (congrArg Subtype.val h) (by decide)
  · show ZMod.castHom (pow_dvd_pow 2 (Nat.le_succ 1)) (ZMod (2 ^ 1)) (0 : ZMod (2 ^ 2)) = 0
    exact map_zero _
  · show ZMod.castHom (pow_dvd_pow 2 (Nat.le_succ 1)) (ZMod (2 ^ 1)) (2 : ZMod (2 ^ 2)) = 0
    rw [map_ofNat]
    decide

/-- [proved-standard; formal-checked] Without the condition the lift is not unique. -/
theorem square_root_lift_not_unique :
    ¬ ∃! y : (rootTower 2 (X ^ 2 : ℤ[X])).Face 2,
      ((rootTower 2 (X ^ 2 : ℤ[X])).restrict (Nat.le_succ 1) y).1 = 0 := by
  rintro ⟨y, _, hy⟩
  obtain ⟨y₀, y₂, hne, h₀, h₂⟩ := square_root_lifts_twice
  exact hne ((hy y₀ h₀).trans (hy y₂ h₂).symm)

/-- [proved-standard; formal-checked] `X² − 2` at `p = 2`: `0` is a root modulo `2` and `f'(0) = 0` there. -/
theorem sqrtTwo_lifting_condition_fails :
    aeval (0 : ZMod (2 ^ 1)) (X ^ 2 - 2 : ℤ[X]) = 0 ∧
      aeval (0 : ZMod (2 ^ 1)) (derivative (X ^ 2 - 2 : ℤ[X])) = 0 := by
  constructor
  · rw [map_sub, map_pow, aeval_X, map_ofNat]
    decide
  · simp [map_ofNat (aeval (0 : ZMod (2 ^ 1)))]

/-- [proved-standard; formal-checked] `X² − 2` has no root modulo `4`: the root modulo `2` is obstructed. -/
theorem sqrtTwo_no_root_mod_four : IsEmpty ((rootTower 2 (X ^ 2 - 2 : ℤ[X])).Face 2) := by
  refine ⟨fun y => ?_⟩
  obtain ⟨y, hy⟩ := y
  rw [map_sub, map_pow, aeval_X, map_ofNat] at hy
  revert y
  decide

/-- [proved-standard; formal-checked] The root tower of `X² − 2` at `p = 2` lands in the `obstructed` arm. -/
theorem sqrtTwo_rootTower_gluing : (rootTower 2 (X ^ 2 - 2 : ℤ[X])).GluingResult :=
  .obstructed ⟨fun s => sqrtTwo_no_root_mod_four.false (s.witness 2)⟩

/-- [proved-standard; formal-checked] `X² + 1` at `p = 2`: `1` is a root modulo `2` and `f'(1) = 2 ≡ 0` there. -/
theorem sqrtNegOne_lifting_condition_fails :
    aeval (1 : ZMod (2 ^ 1)) (X ^ 2 + 1 : ℤ[X]) = 0 ∧
      aeval (1 : ZMod (2 ^ 1)) (derivative (X ^ 2 + 1 : ℤ[X])) = 0 := by
  constructor
  · rw [map_add, map_pow, aeval_X, map_one]
    decide
  · simp [map_ofNat (aeval (1 : ZMod (2 ^ 1)))]
    decide

/-- [proved-standard; formal-checked] `X² + 1` has no root modulo `4`. -/
theorem sqrtNegOne_no_root_mod_four : IsEmpty ((rootTower 2 (X ^ 2 + 1 : ℤ[X])).Face 2) := by
  refine ⟨fun y => ?_⟩
  obtain ⟨y, hy⟩ := y
  rw [map_add, map_pow, aeval_X, map_one] at hy
  revert y
  decide

/-- [proved-standard; formal-checked] `X² + 1` at `p = 5`: `2` and `3` are roots modulo `5` with `f' ≠ 0`. -/
theorem sqrtNegOne_five_roots :
    aeval (2 : ZMod (5 ^ 1)) (X ^ 2 + 1 : ℤ[X]) = 0 ∧
      aeval (2 : ZMod (5 ^ 1)) (derivative (X ^ 2 + 1 : ℤ[X])) ≠ 0 ∧
      aeval (3 : ZMod (5 ^ 1)) (X ^ 2 + 1 : ℤ[X]) = 0 ∧
      aeval (3 : ZMod (5 ^ 1)) (derivative (X ^ 2 + 1 : ℤ[X])) ≠ 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [map_add, map_pow, aeval_X, map_one]
    decide
  · simp [map_ofNat (aeval (2 : ZMod (5 ^ 1)))]
    decide
  · rw [map_add, map_pow, aeval_X, map_one]
    decide
  · simp [map_ofNat (aeval (3 : ZMod (5 ^ 1)))]
    decide

/-- [proved-standard; formal-checked] Exactly one thread of roots of `X² + 1` passes through `2` modulo `5`. -/
theorem sqrtNegOne_five_thread :
    ∃! s : (rootTower 5 (X ^ 2 + 1 : ℤ[X])).CompatibleSection, (s.witness 1).1 = 2 :=
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  hensel_thread_unique_one 5 _ 2 sqrtNegOne_five_roots.1 sqrtNegOne_five_roots.2.1

/-- [proved-standard; formal-checked] Exactly one thread of roots of `X² + 1` passes through `3` modulo `5`. -/
theorem sqrtNegOne_five_other_thread :
    ∃! s : (rootTower 5 (X ^ 2 + 1 : ℤ[X])).CompatibleSection, (s.witness 1).1 = 3 :=
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  hensel_thread_unique_one 5 _ 3 sqrtNegOne_five_roots.2.2.1 sqrtNegOne_five_roots.2.2.2

/-- [proved-standard; formal-checked] The root tower of `X² + 1` at `p = 5` is `plural`, each thread unique. -/
theorem sqrtNegOne_five_gluing : (rootTower 5 (X ^ 2 + 1 : ℤ[X])).GluingResult := by
  obtain ⟨s₂, h₂, _⟩ := sqrtNegOne_five_thread
  obtain ⟨s₃, h₃, _⟩ := sqrtNegOne_five_other_thread
  have hne : (2 : ZMod (5 ^ 1)) ≠ 3 := by decide
  refine .plural ⟨s₂⟩ fun hsub => hne ?_
  rw [← h₂, ← h₃, hsub.elim s₂ s₃]

end Counterexamples

end Holonics.Foundation.CarryTower
