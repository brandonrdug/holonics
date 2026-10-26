import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Tactic

/-!
# The agreement release: where `k` independent draws agree, the class is drawn from `pᵢᵏ / Σ pⱼᵏ`

The record `research/records/2026-10-23_THE_MOMENT_TOWER_LEARNS_GSM8K_BYTES_ONCE_ITS_MODES_ARE_PASSIVE_AND_ITS_CONTACTS_READ_A_RATIO.md`
("Release by agreement"; atlas `receiver.agreement-release`, `hnn.tower-looking`) releases a class
where `k` independent draws from one face agree, and reads it as drawn from `p_i^k / Σ_j p_j^k`
(`agreement_face`, `agreeing_class`). #410 owes that law; this file proves it with the words of `k`
draws as the exact sample space, in any field, so it holds over `ℚ` with no float.

A word `c : Fin k → ι` of `k` independent draws from the face `p` has mass `∏_m p(c_m)`.

[proved-standard; formal-checked] What is proved.

1. **The words carry the face's total to the `k`-th power** (`word_mass_total`):
   `Σ_c ∏_m p(c_m) = (Σ_i p_i)ᵏ`, so a normalized face gives a normalized law on words.
2. **All `k` draws are `i` with mass `p_iᵏ`** (`all_equal_mass`).
3. **The `k` draws agree with mass `Σ_j p_jᵏ`** (`all_agree_mass`, for `k ≥ 1`).
4. **The agreement release** (`agreement_release`): the mass of "all equal `i`" over the mass of
   "all agree" is `p_iᵏ / Σ_j p_jᵏ`. At `k = 1` it is the face, at `k = 2` its collision face.

Consumers: the atlas rows `receiver.agreement-release` and `hnn.tower-looking`.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.HNN.AgreementRelease

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {F : Type*} [Field F]

/-- [definition] The mass of a word of `k` independent draws from the face `p`. -/
def wordMass (p : ι → F) {k : ℕ} (c : Fin k → ι) : F := ∏ m, p (c m)

omit [DecidableEq ι] in
/-- [proved-standard; formal-checked] **The words carry the face's total to the `k`-th power.** -/
theorem word_mass_total (p : ι → F) (k : ℕ) :
    ∑ c : Fin k → ι, wordMass p c = (∑ i, p i) ^ k := by
  rw [← Fin.prod_const, Fintype.prod_sum]
  rfl

/-- [proved-standard; formal-checked] **All `k` draws are `i` with mass `p_iᵏ`.** -/
theorem all_equal_mass (p : ι → F) (k : ℕ) (i : ι) :
    ∑ c ∈ univ.filter (fun c : Fin k → ι => ∀ m, c m = i), wordMass p c = p i ^ k := by
  have hset : univ.filter (fun c : Fin k → ι => ∀ m, c m = i) = {fun _ => i} := by
    ext c
    simp [funext_iff]
  rw [hset, sum_singleton, wordMass, Fin.prod_const]

/-- [proved-standard; formal-checked] **The `k ≥ 1` draws agree with mass `Σ_j p_jᵏ`.** -/
theorem all_agree_mass (p : ι → F) {k : ℕ} (hk : 0 < k) :
    ∑ c ∈ univ.filter (fun c : Fin k → ι => ∃ i, ∀ m, c m = i), wordMass p c =
      ∑ j, p j ^ k := by
  have hset : univ.filter (fun c : Fin k → ι => ∃ i, ∀ m, c m = i) =
      univ.image (fun i : ι => fun _ : Fin k => i) := by
    ext c
    simp only [mem_filter, mem_univ, true_and, mem_image]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨i, funext fun m => (hi m).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨i, fun _ => rfl⟩
  have hinj : Set.InjOn (fun i : ι => fun _ : Fin k => i) (univ : Finset ι) := by
    intro a _ b _ hab
    exact congrFun hab ⟨0, hk⟩
  rw [hset, sum_image hinj]
  refine sum_congr rfl fun j _ => ?_
  rw [wordMass, Fin.prod_const]

/-- [proved-standard; formal-checked] **The agreement release:** where `k ≥ 1` independent draws
from `p` agree, the class is `i` with conditional mass `p_iᵏ / Σ_j p_jᵏ`. -/
theorem agreement_release (p : ι → F) {k : ℕ} (hk : 0 < k) (i : ι) :
    (∑ c ∈ univ.filter (fun c : Fin k → ι => ∀ m, c m = i), wordMass p c) /
        (∑ c ∈ univ.filter (fun c : Fin k → ι => ∃ i, ∀ m, c m = i), wordMass p c) =
      p i ^ k / ∑ j, p j ^ k := by
  rw [all_equal_mass, all_agree_mass p hk]

end Holonics.HNN.AgreementRelease
