import Mathlib

/-!
# A code read without its key is a cipher: fair bits at the source's own model, a uniform reading under a group key, and the founding criterion as a unicity inequality

The record of November 16 (`research/records/2026-11-16_A_CODE_READ_WITHOUT_ITS_KEY_IS_A_CIPHER_…`, §3; atlas
`code.compression-is-a-cipher-without-its-decoder`, `unicity.readings-are-description-over-reading`,
`unicity.gene-partial-key`, with the criterion of `contact.lap-founds-reachable`) joined Brandon's lens that
cryptanalysis, compression and encryption are one subject: a code at the source's own model emits fair bits, so a
compressor and a cipher differ only in who holds the decoder, and the readings a key needs are its description over
what each reading tells. The record's rulers were host arithmetic. This file states the finite part in Lean.

[proved-standard; formal-checked] What is proved.

1. **A code at the source's own model emits fair bits** (`CodeTree`). On a binary code tree, a law that is dyadic at its
   leaves' depths gives every subtree at depth `d` the mass `2^(−d)` (`CodeTree.mass_of_dyadic`; at the root this is
   Kraft's equality, `CodeTree.kraft_of_dyadic`), so each node's two subtrees carry half its mass each
   (`CodeTree.bit_fair`). For an unending stream of independent symbols coded one after another, every bit string `b` is
   the stream's opening with mass `2^(−|b|)` (`CodeTree.stream_uniform`), so each bit is fair given every earlier bit,
   across codeword boundaries (`CodeTree.stream_bit_fair`): to a receiver without the tree the stream is fair coin flips.
   A receiver with the tree reads each codeword back and keeps the rest of the stream (`CodeTree.decodeOne_path`).
   Conversely the bits are fair at every node if and only if the law is the tree's dyadic law
   (`CodeTree.fair_iff_dyadic`). Rulers: `(1/2, 1/4, 1/8, 1/8)` under `(0, 10, 110, 111)` is dyadic and so fair at every
   prefix of every length (`rulerTree_dyadic`, `ruler_stream_uniform`); the same code on `(2/5, 3/10, 1/5, 1/10)` puts
   mass `3/5` on a first bit of 1 (`skew_first_bit`) and is not fair (`skew_not_fair`).
2. **A stream read without its key is uniform** (`pad_bijective`, `pad_keys_card`, `pad_reading_share`,
   `pad_reading_independent`): over a finite group each message's map `key ↦ message + key` is a bijection, so one key
   carries a message `m` to a reading `c` for every pair `(m, c)`, the same count for every `m`. A scheme in which every
   message reaches every reading needs at least as many keys as readings (`keys_ge_readings`), and with each key's map
   decodable at least as many keys as messages (`keys_ge_messages`; Shannon 1949).
3. **The founding criterion is a unicity inequality** (`tension_ratio`, `founding_iff_unicity`): for `0 ≤ drop < S`,
   `ρ = drop/S`, `P > 0` and `N ≥ 1`, `(S/(S − drop))^N > N·P² ⇔ (N/2)·log₂(1/(1 − ρ)) > log₂ P + ½·log₂ N`. The
   record's three rulers are least elements over `N ≥ 1` (`founding_ruler_42`, `founding_ruler_212`,
   `founding_ruler_1522`), read through `ruler_iff` on integers.
4. **A gene is a partial key** (`gene_shortens`, `gene_worth`): with `n₀ = H/D` and the gene leaving `H − I` of the key's
   description, the readings saved are `I/D`, and a gene of description `ℓ` saves more readings than it costs just
   when `ℓ < I`. This is algebra on the definitions; no entropy is constructed here. Rulers:
   `2^76 < 60·26³·26²·150738274937250 < 2^77` (`enigma_key_bits`), `2^78 < C(1024, 10) < 2^79`
   (`support_description_bits`) and `2^66 < (1024/10)^10 < 2^67` (`sensing_count_bits`).

Limits. Statement 1 is for independent symbols and a dyadic law; the bias bound for a Markov source mapped to its
code's dyadic law (Cooper–Fickes, Theorem 3.3) is not stated. Statement 2 is the group key alone; no entropy, no
unicity distance for a random cipher and no statement about a linear secret code's leaked power is made. Statement 3's
least elements are over `N ≥ 1`: at `N = 0` the criterion reads `1 > 0` and holds emptily, so the record's
"`N* = min such N`" is the least positive one. Statement 4 takes `H`, `I` and `D` as given reals. The subject is the
inference; no deployed cipher is a target and nothing here is an attack.

Neighbours, not repeated here: `Holonics/Foundation/Unicity.lean` (the survivors of a key after finitely many
readings, the pigeonhole count), `HolonicsResearch/Compression/Relabelling.lean` (`passageMass_dyadic`: a whole
passage's mass under a code's dyadic law is `2^(−L)`; this file adds the fairness of every bit at every prefix),
`Holonics/Compression/Core/Cost.lean` (a navigator's description bits).

The computational object is the helical pair interaction: a codeword is an address read one contact at a time, and a
key is a navigator's initial configuration. Of the winding guide's six general objects this touches faces and
placement (a bit is a two-sided face of the stream at a prefix) and the helix (a group key is a shift along it); the
pair, cell holonomy, tube and tower thread stay attached.

Consumers: the atlas rows named above; the founding test of the record's §6 (a face's founding place count against
`N*`).

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Compression.CipherCode

open Finset

/-! ## 1. A code at the source's own model emits fair bits -/

/-- [definition] A binary code tree: a leaf holds a symbol, and a node's two branches are the next bit's two faces
(`false` to the first branch, `true` to the second). Every node has both branches, so the code is complete. -/
inductive CodeTree (α : Type*) where
  | leaf : α → CodeTree α
  | node : CodeTree α → CodeTree α → CodeTree α

namespace CodeTree

variable {α : Type*}

/-- [definition] The mass a law `p` gives a subtree: the sum of its leaves' masses. -/
def mass (p : α → ℚ) : CodeTree α → ℚ
  | leaf a => p a
  | node l r => mass p l + mass p r

/-- [definition] A law is **dyadic on a tree** standing at depth `d` when each leaf's mass is `2^(−depth)`, the
depth counted from the root: `p(x) = 2^(−ℓ(x))`. -/
def Dyadic (p : α → ℚ) : ℕ → CodeTree α → Prop
  | d, leaf a => p a = (1 / 2) ^ d
  | d, node l r => Dyadic p (d + 1) l ∧ Dyadic p (d + 1) r

/-- [definition] A law is **fair on a tree** when at every node the two branches carry equal mass: the next bit is as
likely 0 as 1 at every prefix. -/
def Fair (p : α → ℚ) : CodeTree α → Prop
  | leaf _ => True
  | node l r => mass p l = mass p r ∧ Fair p l ∧ Fair p r

/-- [definition] A tree that is not a single leaf: its code emits at least one bit a symbol. -/
def IsNode : CodeTree α → Prop
  | leaf _ => False
  | node _ _ => True

/-- [proved-standard; formal-checked] Under a dyadic law a subtree at depth `d` has mass `2^(−d)`. -/
theorem mass_of_dyadic (p : α → ℚ) :
    ∀ (t : CodeTree α) (d : ℕ), Dyadic p d t → mass p t = (1 / 2) ^ d
  | leaf _, _, h => h
  | node l r, d, h => by
      rw [mass, mass_of_dyadic p l (d + 1) h.1, mass_of_dyadic p r (d + 1) h.2]
      ring

/-- [proved-standard; formal-checked] **Kraft's equality**: a law dyadic on a complete tree sums to one,
`Σ 2^(−ℓ) = 1`. -/
theorem kraft_of_dyadic (p : α → ℚ) (t : CodeTree α) (h : Dyadic p 0 t) : mass p t = 1 := by
  simpa using mass_of_dyadic p t 0 h

/-- [proved-standard; formal-checked] **A bit is fair at every node**: under a dyadic law the branch of bit 1 carries
half its node's mass, `P(b = 1 | prefix) = 1/2`. -/
theorem bit_fair (p : α → ℚ) (l r : CodeTree α) (d : ℕ) (h : Dyadic p d (node l r)) :
    mass p r / mass p (node l r) = 1 / 2 := by
  rw [mass_of_dyadic p _ d h, mass_of_dyadic p r (d + 1) h.2]
  have : ((1 : ℚ) / 2) ^ d ≠ 0 := by positivity
  field_simp
  ring

/-- [proved-standard; formal-checked] A dyadic law is fair at every node. -/
theorem fair_of_dyadic (p : α → ℚ) :
    ∀ (t : CodeTree α) (d : ℕ), Dyadic p d t → Fair p t
  | leaf _, _, _ => trivial
  | node l r, d, h => by
      refine ⟨?_, fair_of_dyadic p l (d + 1) h.1, fair_of_dyadic p r (d + 1) h.2⟩
      rw [mass_of_dyadic p l (d + 1) h.1, mass_of_dyadic p r (d + 1) h.2]

/-- [proved-derived; formal-checked] A law fair at every node of a subtree of mass `2^(−d)` is dyadic there. -/
theorem dyadic_of_fair (p : α → ℚ) :
    ∀ (t : CodeTree α) (d : ℕ), Fair p t → mass p t = (1 / 2) ^ d → Dyadic p d t
  | leaf _, _, _, hm => hm
  | node l r, d, h, hm => by
      have hl : mass p l = (1 / 2) ^ (d + 1) := by
        have := h.1
        simp only [mass] at hm
        rw [pow_succ]; linarith
      have hr : mass p r = (1 / 2) ^ (d + 1) := by rw [← h.1, hl]
      exact ⟨dyadic_of_fair p l (d + 1) h.2.1 hl, dyadic_of_fair p r (d + 1) h.2.2 hr⟩

/-- [proved-derived; formal-checked] **The bits are fair at the code's own model alone**: for a law of total mass
one, every node's bit is fair iff the law is the tree's dyadic law. A source the code was not built for leaves a bias,
the redundancy from which a key is located. -/
theorem fair_iff_dyadic (p : α → ℚ) (t : CodeTree α) (hm : mass p t = 1) :
    Fair p t ↔ Dyadic p 0 t :=
  ⟨fun h => dyadic_of_fair p t 0 h (by simpa using hm), fair_of_dyadic p t 0⟩

/-- [definition] The mass with which the coded stream of independent symbols, each drawn by `p` and coded by `root`,
opens with the bit string `b`, the reading standing at the subtree `cur`: each bit descends one branch, a leaf reached
pays its symbol's mass and returns the reading to the root, and at the string's end the subtree's mass remains. -/
def streamMass (p : α → ℚ) (root : CodeTree α) : CodeTree α → List Bool → ℚ
  | cur, [] => mass p cur
  | leaf _, _ :: _ => 0
  | node l r, x :: b =>
      match (if x then r else l) with
      | leaf a => p a * streamMass p root root b
      | node l' r' => streamMass p root (node l' r') b

/-- [proved-standard; formal-checked] Under a dyadic law, from a node at depth `d` the stream continues with any bit
string `b` at mass `2^(−(d + |b|))`. -/
theorem streamMass_dyadic (p : α → ℚ) (root : CodeTree α) (hroot : Dyadic p 0 root)
    (hnode : IsNode root) :
    ∀ (b : List Bool) (cur : CodeTree α) (d : ℕ), Dyadic p d cur → IsNode cur →
      streamMass p root cur b = (1 / 2) ^ (d + b.length)
  | [], cur, d, h, _ => by
      simpa [streamMass] using mass_of_dyadic p cur d h
  | _ :: _, leaf _, _, _, hn => absurd hn (by simp [IsNode])
  | x :: b, node l r, d, h, _ => by
      have hc : Dyadic p (d + 1) (if x then r else l) := by
        cases x <;> simp [h.1, h.2]
      rw [streamMass]
      cases hch : (if x then r else l) with
      | leaf a =>
          rw [hch] at hc
          have ha : p a = (1 / 2) ^ (d + 1) := hc
          simp only []
          rw [ha, streamMass_dyadic p root hroot hnode b root 0 hroot hnode]
          simp only [List.length_cons]
          ring
      | node l' r' =>
          rw [hch] at hc
          simp only []
          rw [streamMass_dyadic p root hroot hnode b (node l' r') (d + 1) hc trivial]
          simp only [List.length_cons]
          ring

/-- [proved-standard; formal-checked] **The stream of a code at its source's own model is uniform**: every bit string
`b` opens the stream with mass `2^(−|b|)`, whatever codeword boundaries it crosses. -/
theorem stream_uniform (p : α → ℚ) (root : CodeTree α) (hroot : Dyadic p 0 root) (hnode : IsNode root)
    (b : List Bool) : streamMass p root root b = (1 / 2) ^ b.length := by
  simpa using streamMass_dyadic p root hroot hnode b root 0 hroot hnode

/-- [proved-standard; formal-checked] **Every bit is fair given every earlier bit**: `P(b_j = x | b₁ … b_(j−1)) = 1/2`
for both faces `x`. To a receiver without the tree the stream is fair coin flips. -/
theorem stream_bit_fair (p : α → ℚ) (root : CodeTree α) (hroot : Dyadic p 0 root) (hnode : IsNode root)
    (b : List Bool) (x : Bool) :
    streamMass p root root (b ++ [x]) / streamMass p root root b = 1 / 2 := by
  rw [stream_uniform p root hroot hnode, stream_uniform p root hroot hnode, List.length_append,
    List.length_singleton, pow_succ]
  have : ((1 : ℚ) / 2) ^ b.length ≠ 0 := by positivity
  field_simp

/-- [definition] A tree's symbols with their codewords: the bits of the path from the root to each leaf. -/
def paths : CodeTree α → List (α × List Bool)
  | leaf a => [(a, [])]
  | node l r =>
      (paths l).map (fun aw => (aw.1, false :: aw.2)) ++ (paths r).map (fun aw => (aw.1, true :: aw.2))

/-- [definition] The receiver that holds the tree: it walks the stream down the tree and returns the first symbol
with the rest of the stream. -/
def decodeOne : CodeTree α → List Bool → Option (α × List Bool)
  | leaf a, b => some (a, b)
  | node _ _, [] => none
  | node l r, x :: b => decodeOne (if x then r else l) b

/-- [proved-standard; formal-checked] **With the tree the stream is the passage**: a codeword followed by anything is
read back as its symbol, the rest left for the next reading. -/
theorem decodeOne_path :
    ∀ (t : CodeTree α) (a : α) (w : List Bool), (a, w) ∈ paths t →
      ∀ rest : List Bool, decodeOne t (w ++ rest) = some (a, rest)
  | leaf a', a, w, h, rest => by
      simp only [paths, List.mem_singleton, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [decodeOne]
  | node l r, a, w, h, rest => by
      simp only [paths, List.mem_append, List.mem_map] at h
      rcases h with ⟨⟨a', w'⟩, hmem, heq⟩ | ⟨⟨a', w'⟩, hmem, heq⟩
      · simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        simpa [decodeOne] using decodeOne_path l a' w' hmem rest
      · simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        simpa [decodeOne] using decodeOne_path r a' w' hmem rest

end CodeTree

open CodeTree

/-- [definition] The record's ruler: the code `(0, 10, 110, 111)` on four symbols. -/
def rulerTree : CodeTree (Fin 4) :=
  node (leaf 0) (node (leaf 1) (node (leaf 2) (leaf 3)))

/-- [definition] The dyadic source of the ruler, `(1/2, 1/4, 1/8, 1/8)`. -/
def dyadicLaw : Fin 4 → ℚ := ![1 / 2, 1 / 4, 1 / 8, 1 / 8]

/-- [definition] A source the ruler's code was not built for, `(2/5, 3/10, 1/5, 1/10)`. -/
def skewLaw : Fin 4 → ℚ := ![2 / 5, 3 / 10, 1 / 5, 1 / 10]

/-- [formal-checked] The ruler's code is the dyadic source's own: each symbol's mass is `2^(−length)`. -/
theorem rulerTree_dyadic : CodeTree.Dyadic dyadicLaw 0 rulerTree := by
  simp [rulerTree, CodeTree.Dyadic, dyadicLaw]
  norm_num

/-- [formal-checked] The ruler: on `(1/2, 1/4, 1/8, 1/8)` every opening bit string has mass `2^(−length)`, so every
bit is fair given its prefix, the record's first six among them. -/
theorem ruler_stream_uniform (b : List Bool) :
    streamMass dyadicLaw rulerTree rulerTree b = (1 / 2) ^ b.length :=
  stream_uniform dyadicLaw rulerTree rulerTree_dyadic trivial b

/-- [formal-checked] The ruler: the same code on `(2/5, 3/10, 1/5, 1/10)` makes the first bit 1 with mass `3/5`. -/
theorem skew_first_bit : streamMass skewLaw rulerTree rulerTree [true] = 3 / 5 := by
  simp [streamMass, rulerTree, mass, skewLaw]
  norm_num

/-- [formal-checked] On the skew source the code's bits are not fair: the first node's branches carry `2/5` and
`3/5`. -/
theorem skew_not_fair : ¬ Fair skewLaw rulerTree := by
  simp [rulerTree, CodeTree.Fair, mass, skewLaw]

/-! ## 2. A stream read without its key is uniform -/

section Pad

variable {G : Type*} [AddGroup G]

/-- [proved-standard; formal-checked] Under a group key each message's map `key ↦ message + key` is a bijection of
the keys onto the readings. -/
theorem pad_bijective (m : G) : Function.Bijective fun k : G => m + k :=
  (Equiv.addLeft m).bijective

variable [Fintype G] [DecidableEq G]

/-- [proved-standard; formal-checked] **One key carries each message to each reading**: the count of keys taking a
message `m` to a reading `c` is one for every pair. -/
theorem pad_keys_card (m c : G) : (univ.filter fun k : G => m + k = c).card = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨-m + c, ?_⟩
  ext k
  simp only [mem_filter, mem_univ, true_and, mem_singleton]
  constructor
  · rintro rfl; simp
  · rintro rfl; simp

/-- [proved-standard; formal-checked] **The reading says nothing of the message**: the count of keys taking `m` to `c`
is the same for every message. -/
theorem pad_reading_independent (m m' c : G) :
    (univ.filter fun k : G => m + k = c).card = (univ.filter fun k : G => m' + k = c).card := by
  rw [pad_keys_card, pad_keys_card]

/-- [proved-standard; formal-checked] With every key as likely as another, each reading has the share `1/|G|` under
every message: the stream is uniform to a receiver without the key. -/
theorem pad_reading_share (m c : G) :
    ((univ.filter fun k : G => m + k = c).card : ℚ) / Fintype.card G = 1 / Fintype.card G := by
  rw [pad_keys_card]; simp

end Pad

/-- [proved-standard; formal-checked] A scheme in which some message reaches every reading under some key has at least
as many keys as readings. -/
theorem keys_ge_readings {K M C : Type*} [Fintype K] [Fintype C] (enc : K → M → C) (m : M)
    (h : ∀ c, ∃ k, enc k m = c) : Fintype.card C ≤ Fintype.card K :=
  Fintype.card_le_of_surjective (fun k => enc k m) h

/-- [proved-standard; formal-checked] **A key no shorter than the message** (Shannon 1949): if each key's map is
decodable and every message reaches every reading under some key, there are at least as many keys as messages. -/
theorem keys_ge_messages {K M C : Type*} [Fintype K] [Fintype M] [Fintype C] [Nonempty K]
    (enc : K → M → C) (hdec : ∀ k, Function.Injective (enc k))
    (h : ∀ m c, ∃ k, enc k m = c) : Fintype.card M ≤ Fintype.card K := by
  obtain ⟨k₀⟩ := ‹Nonempty K›
  rcases isEmpty_or_nonempty M with hM | ⟨⟨m⟩⟩
  · simp
  · exact (Fintype.card_le_of_injective (enc k₀) (hdec k₀)).trans (keys_ge_readings enc m (h m))

/-! ## 3. The founding criterion is a unicity inequality -/

/-- [proved-derived; formal-checked] The tension's ratio in the share's chart: `S/(S − drop) = 1/(1 − ρ)`,
`ρ = drop/S`. -/
theorem tension_ratio {S drop : ℝ} (hdrop : 0 ≤ drop) (hS : drop < S) :
    S / (S - drop) = 1 / (1 - drop / S) := by
  have hSpos : 0 < S := lt_of_le_of_lt hdrop hS
  have hden : S - drop ≠ 0 := (sub_pos.mpr hS).ne'
  field_simp

/-- [proved-derived; formal-checked] **The founding criterion is a unicity inequality**: a face removing the share
`ρ = drop/S` of the tension over `N` places founds against a pool of `P` members, `(S/(S − drop))^N > N·P²`, if and
only if the redundancy removed, `½·log₂(1/(1 − ρ))` bits a place over `N` places, pays the key's description,
`log₂ P + ½·log₂ N`. -/
theorem founding_iff_unicity {S drop P : ℝ} {N : ℕ} (hdrop : 0 ≤ drop) (hS : drop < S)
    (hP : 0 < P) (hN : 1 ≤ N) :
    (N : ℝ) * P ^ 2 < (S / (S - drop)) ^ N ↔
      Real.logb 2 P + (1 / 2) * Real.logb 2 N < (N / 2) * Real.logb 2 (1 / (1 - drop / S)) := by
  have hSpos : 0 < S := lt_of_le_of_lt hdrop hS
  have hden : 0 < S - drop := sub_pos.mpr hS
  have ha : 0 < S / (S - drop) := div_pos hSpos hden
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  rw [← Real.logb_lt_logb_iff (b := 2) (by norm_num) (by positivity) (pow_pos ha N),
    Real.logb_mul hNpos.ne' (pow_ne_zero 2 hP.ne'), Real.logb_pow, Real.logb_pow,
    ← tension_ratio hdrop hS]
  push_cast
  constructor <;> intro h <;> linarith

/-- [proved-derived; formal-checked] The criterion at a rational tension ratio `a/b`, read on integers:
`N·c < (a/b)^N ⇔ N·c·b^N < a^N`. -/
theorem ruler_iff (a b c N : ℕ) (hb : 0 < b) :
    ((N : ℚ) * c < ((a : ℚ) / b) ^ N) ↔ N * c * b ^ N < a ^ N := by
  have hbq : (0 : ℚ) < (b : ℚ) ^ N := by positivity
  rw [div_pow, lt_div_iff₀ hbq]
  exact_mod_cast Iff.rfl

/-- [proved-derived; formal-checked] A least founding count over `N ≥ 1`, from its integer reading. -/
theorem isLeast_ruler (a b c n : ℕ) (hb : 0 < b) (hn : 1 ≤ n) (h : n * c * b ^ n < a ^ n)
    (hlt : ∀ N < n, 1 ≤ N → ¬ (N * c * b ^ N < a ^ N)) :
    IsLeast {N : ℕ | 1 ≤ N ∧ (N : ℚ) * c < ((a : ℚ) / b) ^ N} n := by
  refine ⟨⟨hn, (ruler_iff a b c n hb).mpr h⟩, ?_⟩
  rintro N ⟨hN1, hN⟩
  by_contra hcon
  exact hlt N (not_le.mp hcon) hN1 ((ruler_iff a b c N hb).mp hN)

/-- [formal-checked] The ruler `ρ = 1/4`, `|P| = 2⁶` (so `S/(S − drop) = 4/3`, `|P|² = 2¹²`): the least founding
count is `42 = 2·3·7`. -/
theorem founding_ruler_42 : IsLeast {N : ℕ | 1 ≤ N ∧ (N : ℚ) * 2 ^ 12 < (4 / 3) ^ N} 42 := by
  have h := isLeast_ruler 4 3 (2 ^ 12) 42 (by norm_num) (by norm_num) (by decide +kernel)
    (by decide +kernel)
  push_cast at h
  exact h

/-- [formal-checked] The ruler `ρ = 1/16`, `|P| = 2⁶` (`16/15`, `2¹²`): the least founding count is
`212 = 2²·53`. -/
theorem founding_ruler_212 : IsLeast {N : ℕ | 1 ≤ N ∧ (N : ℚ) * 2 ^ 12 < (16 / 15) ^ N} 212 := by
  have h := isLeast_ruler 16 15 (2 ^ 12) 212 (by norm_num) (by norm_num) (by decide +kernel)
    (by decide +kernel)
  push_cast at h
  exact h

/-- [formal-checked] The ruler `ρ = 1/64`, `|P| = 2¹²` (`64/63`, `2²⁴`): the least founding count is
`1522 = 2·761`. -/
theorem founding_ruler_1522 : IsLeast {N : ℕ | 1 ≤ N ∧ (N : ℚ) * 2 ^ 24 < (64 / 63) ^ N} 1522 := by
  have h := isLeast_ruler 64 63 (2 ^ 24) 1522 (by norm_num) (by norm_num) (by decide +kernel)
    (by decide +kernel)
  push_cast at h
  exact h

/-- [formal-checked] The factorizations the atlas row carries. -/
theorem founding_counts_factored : 42 = 2 * 3 * 7 ∧ 212 = 2 ^ 2 * 53 ∧ 1522 = 2 * 761 := by
  norm_num

/-! ## 4. A gene is a partial key -/

/-- [proved-derived; formal-checked] **What a gene saves**: with the unicity count `n₀ = H/D` and a gene leaving
`H − I` of the key's description to locate, the readings saved are `n₀ − n₀(G) = I/D`. Algebra on the definitions
(`H(K | G) = H(K) − I(K; G)`). -/
theorem gene_shortens (H I D : ℝ) : H / D - (H - I) / D = I / D := by ring

/-- [proved-derived; formal-checked] **A gene is worth its description** if and only if it says more of the key than it
costs to state: at a redundancy `D > 0` a reading, a gene of description `ℓ` costs `ℓ/D` readings and saves `I/D`,
and `ℓ/D < n₀ − n₀(G) ⇔ ℓ < I`. -/
theorem gene_worth (H I D ℓ : ℝ) (hD : 0 < D) : ℓ / D < H / D - (H - I) / D ↔ ℓ < I := by
  rw [gene_shortens, div_lt_div_iff_of_pos_right hD]

/-- [formal-checked] The ruler of a rotor machine's key (rotor order, start, ring and plugboard): its count lies
between `2^76` and `2^77`, a description of 76 to 77 bits. -/
theorem enigma_key_bits : 2 ^ 76 < 60 * 26 ^ 3 * 26 ^ 2 * 150738274937250 ∧
    60 * 26 ^ 3 * 26 ^ 2 * 150738274937250 < 2 ^ 77 := by norm_num

/-- [formal-checked] The ruler of a sparse support: `C(1024, 10) = 334265867498622145619456` lies between `2^78` and
`2^79`, a description of 78 to 79 bits. -/
theorem support_description_bits :
    Nat.choose 1024 10 = 334265867498622145619456 ∧
      2 ^ 78 < Nat.choose 1024 10 ∧ Nat.choose 1024 10 < 2 ^ 79 := by
  have h : Nat.choose 1024 10 = 334265867498622145619456 := by
    rw [Nat.choose_eq_descFactorial_div_factorial]
    norm_num [Nat.descFactorial, Nat.factorial]
  rw [h]; norm_num

/-- [formal-checked] The ruler of the sensing count: `k·log₂(n/k)` at `n = 1024`, `k = 10` lies between 66 and 67,
`2^66 < (1024/10)^10 < 2^67` cleared of its denominator. -/
theorem sensing_count_bits : 2 ^ 66 * 10 ^ 10 < 1024 ^ 10 ∧ 1024 ^ 10 < 2 ^ 67 * 10 ^ 10 := by
  norm_num

end Holonics.Compression.CipherCode
