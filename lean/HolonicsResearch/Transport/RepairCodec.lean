import HolonicsResearch.Transport.Fold
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# The repair codec is a transition: the damage, the key and the patches reopen every passage, and the patches over
# one fibre are a prefix code whose longest word has at least `⌈log₂ N⌉` bits

The repair record of October 5
(`research/records/2026-10-05_REPAIR_BY_REFLECTION_THE_LOCATED_PAIR_RESTRICTS_THE_ERASED_CELLS_FROM_BOTH_SIDES.md`,
§2 "The codec" and §8 item 2; #410's box "The repair codec is a Fold transition", from comment c6001825514) encodes a
damaged passage by its located key, sent once, and a passage's patches: while a cell is held, the index of the truth in
the first held family. The damage is the transition that drops the erased cells, and the key and the patches reopen
them, `reopen(damage x, key, residual x) = x`. The decoder reads a passage's patches and no further, so the patches
over one fibre of the damage are a prefix code: Kraft's sum is at most one, and the longest is at least `⌈log₂ N⌉`
for a fibre of `N` passages.

This file states the codec on any source, target and key, its decoder reading its own patches and no further (the
record's reason for the prefix property), and proves the record's two clauses.

[proved-derived; formal-checked] What is proved.

1. **The reopen law** (`reopen_damage`, `toTransition`, `toTransition_reopen_apply`): the codec is a
   `Foundation/ContinuingTower.Transition` with `apply` the damage and `residual` the key with the patches, as
   `Transport/Fold.Crease.foldTransition` is one with the side; `reopen(damage x, key, patches x) = x`.
2. **The patches separate a fibre** (`patches_injective_on_fibre`): through `Transport/Fold.residual_injective_on_fibre`
   on the codec's transition, two passages with one damage and one patch word are one passage.
3. **The patches over one fibre are a prefix code** (`patches_prefix_eq`, `prefixFree_patches`, `injOn_fibre`): a
   decoder that reads its patches and no further makes a passage's word a prefix of another's in the same fibre only
   when they are one passage.
4. **Kraft on a prefix code** (`kraft_nat`, `kraft`, `card_le_two_pow`): a prefix-free finite set of binary words of
   lengths at most `L` has `Σ 2^(L − |w|) ≤ 2^L`, so `Σ 2^(−|w|) ≤ 1` and it has at most `2^L` words (each word's
   extensions to length `L` are disjoint).
5. **The longest patch** (`kraft_on_fibre`, `exists_long_patch`): over any `N` passages of one fibre the patches'
   Kraft sum is at most one, and some passage's patch has at least `⌈log₂ N⌉ = Nat.clog 2 N` bits.

The computational object is the helical pair interaction read through its key: the located pair is the relation the
patches restrict along, and the codec's residual is what the damage dropped and the key does not determine. Of the
winding guide's six general objects this touches faces and placement (the damage is a face of the passage, the patches
its residual) and the pair (the key is the located pair); the helix, the cell holonomy, the tube and the tower thread
stay attached.

Consumers: #410's box "The repair codec is a Fold transition"; the record's §2 and §8 item 2; the atlas row
`compression.pair-repair`; `Transport/Fold.residual_injective_on_fibre`, which item 2 reads on the codec.

What stands beside it: the restriction itself (arc consistency is global consistency on a forest, the record's §8
item 1), which fixes which patches a passage needs and so how near the longest patch comes to `⌈log₂ N⌉`; and
Mathlib's `InformationTheory.kraft_mcmillan_inequality`, Kraft's sum for every uniquely decodable code, of which item
4 is the prefix-free case proved by extension.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Transport.RepairCodec

open Holonics.Foundation.ContinuingTower

universe u v w

/-! ## Kraft on a prefix code -/

/-- [definition] A set of binary words is **prefix-free** when a word opens another only by being it. -/
def PrefixFree (S : Finset (List Bool)) : Prop := ∀ w ∈ S, ∀ w' ∈ S, w <+: w' → w = w'

/-- Two prefixes of one word are comparable. -/
lemma prefix_or_prefix {w w' v v' : List Bool} (h : w ++ v = w' ++ v') : w <+: w' ∨ w' <+: w := by
  have h1 : w <+: w' ++ v' := ⟨v, h⟩
  have h2 : w' <+: w' ++ v' := ⟨v', rfl⟩
  rcases le_total w.length w'.length with hl | hl
  · exact Or.inl (List.prefix_of_prefix_length_le h1 h2 hl)
  · exact Or.inr (List.prefix_of_prefix_length_le h2 h1 hl)

/-- [proved-standard; formal-checked] **Kraft on a prefix code, counted**: a prefix-free finite set of binary words of
lengths at most `L` has `Σ_w 2^(L − |w|) ≤ 2^L`, each word's extensions to length `L` being disjoint. -/
theorem kraft_nat {S : Finset (List Bool)} (hS : PrefixFree S) {L : ℕ} (hL : ∀ w ∈ S, w.length ≤ L) :
    ∑ w ∈ S, 2 ^ (L - w.length) ≤ 2 ^ L := by
  classical
  let ext : (Σ w : S, List.Vector Bool (L - w.1.length)) → List.Vector Bool L := fun p =>
    ⟨p.1.1 ++ p.2.1, by rw [List.length_append, p.2.2, Nat.add_sub_cancel' (hL p.1.1 p.1.2)]⟩
  have hinj : Function.Injective ext := by
    rintro ⟨⟨w, hw⟩, ⟨v, hv⟩⟩ ⟨⟨w', hw'⟩, ⟨v', hv'⟩⟩ h
    have h' : w ++ v = w' ++ v' := congrArg Subtype.val h
    have hww : w = w' := by
      rcases prefix_or_prefix h' with hp | hp
      · exact hS w hw w' hw' hp
      · exact (hS w' hw' w hw hp).symm
    subst hww
    have hvv : v = v' := List.append_cancel_left h'
    subst hvv
    rfl
  have hcard := Fintype.card_le_of_injective ext hinj
  rw [Fintype.card_sigma, card_vector, Fintype.card_bool] at hcard
  simp only [card_vector, Fintype.card_bool] at hcard
  calc ∑ w ∈ S, 2 ^ (L - w.length) = ∑ w : S, 2 ^ (L - w.1.length) :=
        (Finset.sum_coe_sort S fun w => 2 ^ (L - w.length)).symm
    _ ≤ 2 ^ L := hcard

/-- [proved-standard; formal-checked] **Kraft's inequality on a prefix code**: `Σ_w 2^(−|w|) ≤ 1`. -/
theorem kraft {S : Finset (List Bool)} (hS : PrefixFree S) : ∑ w ∈ S, (1 / 2 : ℝ) ^ w.length ≤ 1 := by
  set L := S.sup List.length
  have hL : ∀ w ∈ S, w.length ≤ L := fun w hw => Finset.le_sup (f := List.length) hw
  have hk := kraft_nat hS hL
  have hk' : (∑ w ∈ S, (2 : ℝ) ^ (L - w.length)) ≤ (2 : ℝ) ^ L := by exact_mod_cast hk
  have h2L : (0 : ℝ) < 2 ^ L := by positivity
  have hterm : ∀ w ∈ S, (1 / 2 : ℝ) ^ w.length = (2 : ℝ) ^ (L - w.length) / 2 ^ L := by
    intro w hw
    rw [eq_div_iff h2L.ne', one_div, inv_pow, ← pow_sub_mul_pow (2 : ℝ) (hL w hw)]
    field_simp
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div, div_le_one h2L]
  exact hk'

/-- [proved-standard; formal-checked] A prefix-free set of binary words of lengths at most `L` has at most `2^L`
words. -/
theorem card_le_two_pow {S : Finset (List Bool)} (hS : PrefixFree S) {L : ℕ} (hL : ∀ w ∈ S, w.length ≤ L) :
    S.card ≤ 2 ^ L := by
  calc S.card = ∑ _w ∈ S, 1 := by simp
    _ ≤ ∑ w ∈ S, 2 ^ (L - w.length) := Finset.sum_le_sum fun w _ => Nat.one_le_two_pow
    _ ≤ 2 ^ L := kraft_nat hS hL

/-- [definition] **The repair codec**: the damage that drops the erased cells, the located key, each passage's patches
as a binary word, and a decoder that, given the damage, the key and a stream that opens with a passage's patches,
returns the passage and the stream it did not read. -/
structure Codec (Source : Type u) (Target : Type v) (Key : Type w) where
  /-- The damage: what of a passage survives. -/
  damage : Source → Target
  /-- The located key, sent once. -/
  key : Key
  /-- A passage's patches. -/
  patches : Source → List Bool
  /-- The decoder: the passage reopened and the unread rest of the stream. -/
  decode : Target → Key → List Bool → Source × List Bool
  /-- The decoder reopens each passage from its patches and reads no further. -/
  decode_reads_no_further : ∀ x r, decode (damage x) key (patches x ++ r) = (x, r)

namespace Codec

variable {Source : Type u} {Target : Type v} {Key : Type w} (C : Codec Source Target Key)

/-- [definition] Reopen a passage from its damage, the key and its patches. -/
def reopen (t : Target) (k : Key) (p : List Bool) : Source := (C.decode t k p).1

/-- [proved-derived; formal-checked] **The reopen law**: `reopen(damage x, key, patches x) = x`. -/
theorem reopen_damage (x : Source) : C.reopen (C.damage x) C.key (C.patches x) = x := by
  have h := C.decode_reads_no_further x []
  rw [List.append_nil] at h
  simp [reopen, h]

/-- [definition] **The repair codec as a transition**: `apply` is the damage, the residual is the key with the
patches, and `reopen` is the decoder's passage. -/
def toTransition : Transition Source Target where
  Residual := Key × List Bool
  apply := C.damage
  residual x := (C.key, C.patches x)
  reopen t p := C.reopen t p.1 p.2
  reopen_apply := C.reopen_damage

/-- [proved-derived; formal-checked] The transition's own reopen law is the codec's. -/
theorem toTransition_reopen_apply (x : Source) :
    C.toTransition.reopen (C.toTransition.apply x) (C.toTransition.residual x) = x :=
  C.toTransition.reopen_apply x

/-- [proved-derived; formal-checked] **The patches separate a fibre**, through
`Transport/Fold.residual_injective_on_fibre`. -/
theorem patches_injective_on_fibre {Source Target : Type u} (C : Codec Source Target Key) (t : Target) :
    Function.Injective (fun x : { x : Source // C.damage x = t } => C.patches x.1) := by
  intro x y h
  apply Holonics.Transport.Fold.residual_injective_on_fibre C.toTransition t
  show (C.key, C.patches x.1) = (C.key, C.patches y.1)
  rw [show C.patches x.1 = C.patches y.1 from h]

/-- [proved-derived; formal-checked] **A prefix inside one fibre is the passage itself**: if one passage's patches open
another's in the same fibre, the two are one passage and the words are equal. -/
theorem patches_prefix_eq {x y : Source} (hd : C.damage x = C.damage y) (hp : C.patches x <+: C.patches y) :
    x = y ∧ C.patches x = C.patches y := by
  obtain ⟨r, hr⟩ := hp
  have h1 := C.decode_reads_no_further x r
  have h2 := C.decode_reads_no_further y []
  rw [hd, hr] at h1
  rw [List.append_nil, h1] at h2
  obtain ⟨hxy, hr0⟩ := Prod.mk.inj h2
  refine ⟨hxy, ?_⟩
  rw [← hr, hr0, List.append_nil]

/-- [proved-derived; formal-checked] The patches over a finite set of passages of one fibre are prefix-free. -/
theorem prefixFree_patches (s : Finset Source) {t : Target} (hs : ∀ x ∈ s, C.damage x = t) :
    PrefixFree (s.image C.patches) := by
  intro w hw w' hw' hp
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hw
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hw'
  exact (C.patches_prefix_eq ((hs x hx).trans (hs y hy).symm) hp).2

/-- [proved-derived; formal-checked] The patches are injective on any set of passages of one fibre (from the prefix
law, in every universe). -/
theorem injOn_fibre (s : Finset Source) {t : Target} (hs : ∀ x ∈ s, C.damage x = t) : Set.InjOn C.patches s :=
  fun x hx y hy h => (C.patches_prefix_eq ((hs x hx).trans (hs y hy).symm) (h ▸ List.prefix_refl _)).1

/-! ## The longest patch -/

/-- [proved-derived; formal-checked] **Kraft over a fibre**: over passages of one fibre, `Σ_x 2^(−|patches x|) ≤ 1`. -/
theorem kraft_on_fibre (s : Finset Source) {t : Target} (hs : ∀ x ∈ s, C.damage x = t) :
    ∑ x ∈ s, (1 / 2 : ℝ) ^ (C.patches x).length ≤ 1 := by
  classical
  have hinj := C.injOn_fibre s hs
  have h := kraft (C.prefixFree_patches s hs)
  rwa [Finset.sum_image (f := fun w => (1 / 2 : ℝ) ^ w.length) hinj] at h

/-- [proved-derived; formal-checked] **The longest patch has at least `⌈log₂ N⌉` bits**: over any `N ≥ 1` passages of
one fibre, some passage's patch is at least `Nat.clog 2 N` long. -/
theorem exists_long_patch (s : Finset Source) {t : Target} (hs : ∀ x ∈ s, C.damage x = t) (hne : s.Nonempty) :
    ∃ x ∈ s, Nat.clog 2 s.card ≤ (C.patches x).length := by
  classical
  obtain ⟨x, hx, hmax⟩ := s.exists_max_image (fun y => (C.patches y).length) hne
  refine ⟨x, hx, Nat.clog_le_of_le_pow ?_⟩
  have hinj := C.injOn_fibre s hs
  have hL : ∀ w ∈ s.image C.patches, w.length ≤ (C.patches x).length := by
    intro w hw
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hw
    exact hmax y hy
  have h := card_le_two_pow (C.prefixFree_patches s hs) hL
  rwa [Finset.card_image_of_injOn hinj] at h

end Codec

end Holonics.Transport.RepairCodec
