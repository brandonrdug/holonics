import Holonics.Compression.Landmark.Context.Population
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.GroupTheory.Index
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

/-!
# Unicity: when the readings leave one key

[definition] Brandon, September 30: "How many times does an organism that has never witnessed a
classification of motion need to observe the motion before it can refine an internal model of how
the motion reproduces? … When can you hear the music?" Shannon's name for the answer is the
**unicity distance** (*Communication Theory of Secrecy Systems*, 1949). Learning is locating keys
(the Bombe, `hnn::keys`). A key is a navigator's initial configuration. A receiver reads the
navigator's passage, one reading a step. The keys consistent with the readings shrink until one
class is left: the class no future reading separates.
([record](../../../research/records/2026-09-30_UNICITY_THE_READINGS_LEAVE_ONE_KEY_AND_THE_HELIXS_CELLS_ARE_THE_FAREY_SEQUENCE.md))

The survivors (`Population.survivors`, the keys whose readings agree with every received one) are
the consistent set, and the uniform mixture over them is already exact there: its face of a reading
is the surviving fraction `#S_(t+1)/#S_t`, its product telescopes to `#S_n/|K|`, its code is
`log₂ |K| − log₂ #S_n` (`survivor_code`), a product key space multiplies its survivors
(`survivors_product`), and under any prior the mixture codes within `−log₂ π(key)` of the true key
(`population_mixture`). So **the surprise a reading carries is the log of the ratio of the
consistent counts before and after it**: the loss is the log of a ratio of two counts.

[proved-derived; formal-checked] This module adds the unicity laws, all counts with no logarithm
taken:
- **A null reading** (`survivors_card_succ_eq_iff`): a reading constrains nothing (face one,
  surprise zero) exactly when every survivor makes it.
- **The class that never collapses** (`Indistinguishable`, `eventually_survivors_iff`,
  `eventually_survivors_eq_class`): after finitely many readings the survivors are exactly the true
  key's class under "every reading agrees", and the code stays `log₂ |K| − log₂ |class|`.
  Identification is only ever up to that quotient.
- **The pigeonhole count** (`classes_le_pow_of_separating`, `clog_classes_le_of_separating`):
  separating every class takes at least `clog_{|C|}` of the class count readings.
- **Residues** (`kernelChain`). For keys in an additive group read by additive maps, the
  consistent set is a coset of the kernel chain (`consistent_iff_sub_mem`). The key count factors
  exactly, `|X| = |fibre after n| · ∏ ratios` (`card_eq_fibre_mul_prod`: Lagrange along the
  chain). Each ratio divides the reading's alphabet (`relIndex_dvd_card_reading`), so reaching a
  fibre of index `I` takes at least `clog_{|V|} I` readings (`clog_index_le`).
- **The helix** (`floor_ne_iff_exists_between`, `readings_agree_iff`). A rotation key `α` read
  by its whole windings `⌊n α⌋` (circle and carry) leaves, after `N` readings, exactly the keys in
  its Farey cell of order `N`. Two keys are separated exactly when a fraction `k/n` with `n ≤ N`
  lies in the half-open interval between them. Rational keys of height `≤ N` are separated by `N`
  readings (`rational_keys_separated`). Farey neighbours `p/q < p'/q'` stay unseparated for
  every `N < q'` (`farey_neighbours_agree_below`) and are separated at `q'`
  (`farey_neighbours_separate_at`). Within the rationals of height at most `Q`, every two keys are
  separated within `Q` readings, and the partition after `N` readings is the Farey sequence `F_N`.
  A real key's cell keeps positive measure: a continuous key never becomes a singleton.

[proved-standard; not formalized here] Franel and Landau (1924): RH holds if and only if the Farey
sequence's discrepancy from equal spacing is `O(N^(1/2+ε))` (Landau's `L¹` form). By the helix's
law above, that is a statement about the helix's unicity cells: the gap between the number of
cells below each key and the number the uniform density predicts. The record grades the reading.
-/

namespace Holonics.Foundation.Unicity

open Finset

open Holonics.Compression.Landmark.Context.Population

section Survivors

variable {κ C : Type*} [Fintype κ] [DecidableEq C]

/-- **A reading constrains nothing exactly when every survivor makes it**: the survivor count is
unchanged (the uniform mixture's face of the reading is one, its surprise zero) if and only if no
surviving key is separated from the truth by it. -/
theorem survivors_card_succ_eq_iff (e : κ → ℕ → C) (x : ℕ → C) (t : ℕ) :
    (survivors e x (t + 1)).card = (survivors e x t).card ↔
      ∀ k ∈ survivors e x t, e k t = x t := by
  rw [survivors_succ, Finset.card_filter_eq_iff]

/-- Two keys no reading separates. -/
def Indistinguishable (e : κ → ℕ → C) (k j : κ) : Prop :=
  ∀ t, e k t = e j t

/-- **The class that never collapses**: after finitely many readings the survivors are exactly
the keys indistinguishable from the true one. Identification is only ever up to that class. -/
theorem eventually_survivors_iff (e : κ → ℕ → C) (key : κ) :
    ∃ N, ∀ n ≥ N, ∀ k, k ∈ survivors e (e key) n ↔ Indistinguishable e k key := by
  classical
  let idx : κ → ℕ := fun k => if h : ∃ t, e k t ≠ e key t then Nat.find h else 0
  refine ⟨univ.sup fun k => idx k + 1, fun n hn k => ⟨fun hk => ?_, fun hind => ?_⟩⟩
  · by_contra hnot
    have hex : ∃ t, e k t ≠ e key t := by simpa [Indistinguishable] using hnot
    have hidx : idx k = Nat.find hex := by simp [idx, hex]
    have hlt : Nat.find hex < n := by
      have := Finset.le_sup (f := fun k => idx k + 1) (mem_univ k)
      omega
    have hagree := (mem_filter.mp hk).2 _ hlt
    exact Nat.find_spec hex hagree
  · simp only [survivors, mem_filter, mem_univ, true_and]
    exact fun s _ => hind s

/-- **Unicity is reached**: from some reading on, the survivors are the true key's class, so the
uniform mixture's code (`survivor_code`) stays `log₂ |K| − log₂ |class|` for ever. -/
theorem eventually_survivors_eq_class (e : κ → ℕ → C) (key : κ) :
    ∃ N, ∀ n ≥ N, survivors e (e key) n =
      haveI := Classical.decPred (fun k => Indistinguishable e k key)
      univ.filter fun k => Indistinguishable e k key := by
  classical
  obtain ⟨N, hN⟩ := eventually_survivors_iff e key
  refine ⟨N, fun n hn => ?_⟩
  ext k
  simp only [mem_filter, mem_univ, true_and]
  convert hN n hn k

omit [DecidableEq C] in
/-- **The pigeonhole count**: if `n` readings separate every two keys that any reading separates,
the number of distinguishable classes is at most `|C|ⁿ`. -/
theorem classes_le_pow_of_separating [Fintype C] (e : κ → ℕ → C) (n : ℕ)
    (hsep : ∀ k j, (∀ t < n, e k t = e j t) → Indistinguishable e k j) :
    haveI := Classical.decEq (ℕ → C)
    (univ.image e).card ≤ Fintype.card C ^ n := by
  classical
  have hinj : Set.InjOn (fun f : ℕ → C => fun i : Fin n => f i) (univ.image e) := by
    intro f hf g hg hfg
    obtain ⟨k, -, rfl⟩ := mem_image.mp hf
    obtain ⟨j, -, rfl⟩ := mem_image.mp hg
    funext i
    exact hsep k j (fun s hs => congrFun hfg ⟨s, hs⟩) i
  have := Finset.card_le_card_of_injOn (fun f : ℕ → C => fun i : Fin n => f i)
    (t := Finset.univ) (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)) hinj
  simpa [Fintype.card_fun, Fintype.card_fin] using this

omit [DecidableEq C] in
/-- **Unicity's lower bound**: separating every class takes at least `clog_{|C|}` of the class
count readings. -/
theorem clog_classes_le_of_separating [Fintype C] (e : κ → ℕ → C) (n : ℕ)
    (hsep : ∀ k j, (∀ t < n, e k t = e j t) → Indistinguishable e k j) :
    haveI := Classical.decEq (ℕ → C)
    Nat.clog (Fintype.card C) (univ.image e).card ≤ n :=
  Nat.clog_le_of_le_pow (classes_le_pow_of_separating e n hsep)

end Survivors

section Residue

variable {X V : Type*} [AddCommGroup X] [AddCommGroup V]

/-- The kernel chain: the differences that none of the first `n` readings distinguishes. -/
def kernelChain (read : ℕ → X →+ V) : ℕ → AddSubgroup X
  | 0 => ⊤
  | n + 1 => kernelChain read n ⊓ (read n).ker

variable (read : ℕ → X →+ V)

theorem mem_kernelChain_iff (n : ℕ) (x : X) :
    x ∈ kernelChain read n ↔ ∀ i < n, read i x = 0 := by
  induction n with
  | zero => simp [kernelChain]
  | succ n ih =>
    simp only [kernelChain, AddSubgroup.mem_inf, ih, AddMonoidHom.mem_ker]
    constructor
    · rintro ⟨h, hn⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact h i hi
      · exact hn
    · intro h
      exact ⟨fun i hi => h i (Nat.lt_succ_of_lt hi), h n (Nat.lt_succ_self n)⟩

/-- **The consistent set is a coset of the kernel chain.** -/
theorem consistent_iff_sub_mem (n : ℕ) (key k : X) :
    (∀ i < n, read i k = read i key) ↔ k - key ∈ kernelChain read n := by
  rw [mem_kernelChain_iff]
  simp only [map_sub, sub_eq_zero]

theorem kernelChain_succ_le (n : ℕ) : kernelChain read (n + 1) ≤ kernelChain read n :=
  inf_le_left

/-- The index of the fibre after `n` readings is the product of the readings' ratios. -/
theorem index_kernelChain (n : ℕ) :
    (kernelChain read n).index =
      ∏ i ∈ range n, (kernelChain read (i + 1)).relIndex (kernelChain read i) := by
  induction n with
  | zero => simp [kernelChain]
  | succ n ih =>
    rw [prod_range_succ, ← ih,
      ← AddSubgroup.relIndex_mul_index (kernelChain_succ_le read n), mul_comm]

/-- **The key count factors exactly** (Lagrange along the chain): the keys number the surviving
fibre times the product of the readings' ratios. -/
theorem card_eq_fibre_mul_prod (n : ℕ) :
    Nat.card X = Nat.card (kernelChain read n) *
      ∏ i ∈ range n, (kernelChain read (i + 1)).relIndex (kernelChain read i) := by
  rw [← index_kernelChain, AddSubgroup.card_mul_index]

/-- **Each reading's ratio divides its alphabet**: the constraint a residue reading places is a
divisor of the reading's modulus. -/
theorem relIndex_dvd_card_reading [Finite V] (n : ℕ) :
    (kernelChain read (n + 1)).relIndex (kernelChain read n) ∣ Nat.card V := by
  set K := kernelChain read n
  have hsub : (kernelChain read (n + 1)).addSubgroupOf K = ((read n).comp K.subtype).ker := by
    change (K ⊓ (read n).ker).addSubgroupOf K = _
    rw [AddSubgroup.inf_addSubgroupOf_left]
    exact AddMonoidHom.comap_ker _ _
  rw [AddSubgroup.relIndex, hsub, AddSubgroup.index_ker]
  exact AddSubgroup.card_addSubgroup_dvd_card _

/-- The fibre's index after `n` readings is at most the alphabet's `n`-th power. -/
theorem index_kernelChain_le_pow [Finite V] (n : ℕ) :
    (kernelChain read n).index ≤ Nat.card V ^ n := by
  calc (kernelChain read n).index
      = ∏ i ∈ range n, (kernelChain read (i + 1)).relIndex (kernelChain read i) :=
        index_kernelChain read n
    _ ≤ ∏ _i ∈ range n, Nat.card V :=
        Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
          (fun i _ => Nat.le_of_dvd Nat.card_pos (relIndex_dvd_card_reading read i))
    _ = Nat.card V ^ n := by rw [Finset.prod_const, Finset.card_range]

/-- **Residue unicity's lower bound**: reaching a fibre of index `I` takes at least
`clog_{|V|} I` readings. -/
theorem clog_index_le [Finite V] (n : ℕ) :
    Nat.clog (Nat.card V) (kernelChain read n).index ≤ n :=
  Nat.clog_le_of_le_pow (index_kernelChain_le_pow read n)

end Residue

section Helix

/-- **One reading of the helix separates two keys exactly when a fraction lies between them**:
for `α ≤ β` and `n > 0`, the whole windings `⌊n α⌋` and `⌊n β⌋` differ if and only if some
`k/n` lies in `(α, β]`. -/
theorem floor_ne_iff_exists_between {α β : ℝ} (hαβ : α ≤ β) {n : ℕ} (hn : 0 < n) :
    ⌊(n : ℝ) * α⌋ ≠ ⌊(n : ℝ) * β⌋ ↔ ∃ k : ℤ, α < k / n ∧ (k : ℝ) / n ≤ β := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  constructor
  · intro hne
    have hle : ⌊(n : ℝ) * α⌋ ≤ ⌊(n : ℝ) * β⌋ :=
      Int.floor_mono (mul_le_mul_of_nonneg_left hαβ hn'.le)
    have hlt : ⌊(n : ℝ) * α⌋ < ⌊(n : ℝ) * β⌋ := lt_of_le_of_ne hle hne
    refine ⟨⌊(n : ℝ) * β⌋, ?_, ?_⟩
    · rw [lt_div_iff₀ hn', mul_comm]
      have := Int.lt_floor_add_one ((n : ℝ) * α)
      have h1 : ((⌊(n : ℝ) * α⌋ : ℤ) : ℝ) + 1 ≤ ((⌊(n : ℝ) * β⌋ : ℤ) : ℝ) := by
        exact_mod_cast hlt
      linarith
    · rw [div_le_iff₀ hn', mul_comm]
      exact Int.floor_le _
  · rintro ⟨k, hk1, hk2⟩
    rw [lt_div_iff₀ hn', mul_comm] at hk1
    rw [div_le_iff₀ hn', mul_comm] at hk2
    have h1 : ⌊(n : ℝ) * α⌋ < k := Int.floor_lt.mpr hk1
    have h2 : k ≤ ⌊(n : ℝ) * β⌋ := Int.le_floor.mpr hk2
    omega

/-- **The helix's unicity cells are the Farey intervals**: `N` readings leave `α ≤ β`
unseparated exactly when no fraction `k/n` with `0 < n ≤ N` lies in `(α, β]`. -/
theorem readings_agree_iff {α β : ℝ} (hαβ : α ≤ β) (N : ℕ) :
    (∀ n, 0 < n → n ≤ N → ⌊(n : ℝ) * α⌋ = ⌊(n : ℝ) * β⌋) ↔
      ¬ ∃ n : ℕ, ∃ k : ℤ, 0 < n ∧ n ≤ N ∧ α < k / n ∧ (k : ℝ) / n ≤ β := by
  constructor
  · rintro h ⟨n, k, hn, hnN, hk1, hk2⟩
    exact (floor_ne_iff_exists_between hαβ hn).mpr ⟨k, hk1, hk2⟩ (h n hn hnN)
  · intro h n hn hnN
    by_contra hne
    obtain ⟨k, hk1, hk2⟩ := (floor_ne_iff_exists_between hαβ hn).mp hne
    exact h ⟨n, k, hn, hnN, hk1, hk2⟩

/-- **A rational key of height `≤ N` is separated from every smaller key by `N` readings.** -/
theorem rational_keys_separated {α : ℝ} {p : ℤ} {q N : ℕ} (hq : 0 < q) (hqN : q ≤ N)
    (hlt : α < (p : ℝ) / q) :
    ∃ n, 0 < n ∧ n ≤ N ∧ ⌊(n : ℝ) * α⌋ ≠ ⌊(n : ℝ) * ((p : ℝ) / q)⌋ :=
  ⟨q, hq, hqN, (floor_ne_iff_exists_between hlt.le hq).mpr ⟨p, hlt, le_rfl⟩⟩

/-- **Farey neighbours stay unseparated below the larger denominator**: if `p' q − p q' = 1`,
every `N < q'` readings of `p/q` and `p'/q'` agree. (Any fraction strictly between them has
denominator at least `q + q'`, and `p'/q'` is in lowest terms.) -/
theorem farey_neighbours_agree_below {p p' : ℤ} {q q' : ℕ} (hq : 0 < q) (hq' : 0 < q')
    (hdet : p' * q - p * q' = 1) {N : ℕ} (hN : N < q') :
    ∀ n, 0 < n → n ≤ N → ⌊(n : ℝ) * ((p : ℝ) / q)⌋ = ⌊(n : ℝ) * ((p' : ℝ) / q')⌋ := by
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hq'r : (0 : ℝ) < q' := by exact_mod_cast hq'
  have hle : (p : ℝ) / q ≤ (p' : ℝ) / q' := by
    rw [div_le_div_iff₀ hqr hq'r]
    have : ((p' * q - p * q' : ℤ) : ℝ) = 1 := by exact_mod_cast hdet
    push_cast at this
    linarith
  refine (readings_agree_iff hle N).mpr ?_
  rintro ⟨n, k, hn, hnN, hk1, hk2⟩
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  rw [div_lt_div_iff₀ hqr hnr] at hk1
  rw [div_le_div_iff₀ hnr hq'r] at hk2
  have hA : p * (n : ℤ) < k * q := by exact_mod_cast hk1
  have hB : k * (q' : ℤ) ≤ p' * n := by exact_mod_cast hk2
  -- n = n (p' q − p q') = q (p' n − k q') + q' (k q − p n) ≥ q'
  have hid : (n : ℤ) = q * (p' * n - k * q') + q' * (k * q - p * n) := by
    linear_combination (-(n : ℤ)) * hdet
  have hnq' : (q' : ℤ) ≤ n := by nlinarith
  omega

/-- Farey neighbours are separated at the larger denominator. -/
theorem farey_neighbours_separate_at {p p' : ℤ} {q q' : ℕ} (hq : 0 < q) (hq' : 0 < q')
    (hdet : p' * q - p * q' = 1) :
    ⌊(q' : ℝ) * ((p : ℝ) / q)⌋ ≠ ⌊(q' : ℝ) * ((p' : ℝ) / q')⌋ := by
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hq'r : (0 : ℝ) < q' := by exact_mod_cast hq'
  have hlt : (p : ℝ) / q < (p' : ℝ) / q' := by
    rw [div_lt_div_iff₀ hqr hq'r]
    have : ((p' * q - p * q' : ℤ) : ℝ) = 1 := by exact_mod_cast hdet
    push_cast at this
    linarith
  exact (floor_ne_iff_exists_between hlt.le hq').mpr ⟨p', hlt, le_rfl⟩

end Helix

section Instances

/-- The order-2 terrain's declared key family ("which earlier cell, and which map of `ℤ/4`"):
`40 · 4⁴ = 10240 = 2¹¹ · 5` keys. -/
theorem order2_family_count : 40 * 4 ^ 4 = 10240 ∧ (10240 : ℕ) = 2 ^ 11 * 5 := by
  norm_num

/-- Reading its keys takes at least seven readings of a four-letter alphabet. -/
theorem order2_unicity_lower : Nat.clog 4 10240 = 7 := by
  apply le_antisymm
  · exact Nat.clog_le_of_le_pow (by norm_num)
  · exact (Nat.lt_clog_iff_pow_lt (by norm_num)).mpr (by norm_num)

end Instances

end Holonics.Foundation.Unicity
