import Holonics.Foundation.NavigatorInference
import Holonics.Foundation.ReceiverCodeCost
import Mathlib.Data.Nat.Log

/-!
# The cost of a compression: the bits of an actual code, against the literal

[definition] Rebuild step 3 (#145) and `docs/canon/TABLET_THE_COMPRESSION.md` §1: **a compression
is a codec pivot carrying its decoder.** Here the pivot is a navigator codec: a navigator step, its
initial configuration (the key) and the decoder's receiver face read at every tick, so the material
is regenerated causally (`decode_succ`, `decode_take`). Every bit counted is a bit written:

```text
CodecFamily   declared finite families of steps, configurations and reads (the reference machine
              coder and decoder share)
description   the codec's three indices in fixed width: ⌈log₂ #steps⌉ + ⌈log₂ #configurations⌉
              + ⌈log₂ #reads⌉ bits (describe), read back by readIndex / ofDescription
literal       each symbol's index in fixed width ⌈log₂ |A|⌉ (literalCode), read back by readLiteral
Kt            |code| + ⌈log₂ t⌉, t the navigator's ticks (one reading per tick)
pays off      Kt < ℓ, the literal's code length: an integer comparison of two codes
```

The material's length is the receiver's request, declared to both presentations and written by
neither. `Kt` is Levin's form; `⌈log₂ t⌉` is `Nat.clog 2 t`, the least `k` with `t ≤ 2ᵏ`.

[proved-derived; formal-checked] What is proved.

1. **The description is a code.** Its length is the family's `descriptionBits`
   (`describe_length`), and the decoder reads the codec back from it, followed by any continuation
   (`readIndex_describe`, `ofDescription_describe`), so `describe` is injective
   (`describe_injective`). Only a code of exactly that length decodes: a truncated field is refused
   (`readField_length`, `ofDescription_length`, `oneBit_truncated_refused`). A pivot's code alone releases its material (`CodecPivot.release_code`).
   The literal is a code too (`literalCode_length`, `readLiteral_literalCode`).
2. **RIDE and FOUND in bits** (the partial pivot). The code of any codec on any material is its
   description, the count of the faces it does not regenerate, and one `(position, symbol)` patch
   per such face; the decoder releases the material from that code alone
   (`partialRelease_partialCode`). Its length is
   `descriptionBits + ⌈log₂(n+1)⌉ + #founded · (⌈log₂ n⌉ + ⌈log₂ |A|⌉)` (`partialCode_length`):
   the faces the navigator regenerates ride on its description at no further bit, and each face
   outside its image founds exactly one patch. The founded faces are empty exactly when the codec
   regenerates the material (`foundedFaces_eq_nil_iff`). Only the codec's residual is priced: no
   exchange rate between the resonance work form (`Core/Resonance`) and bits is asserted, and the
   exact rational residual of a linear face map (`Core/FaceMap.cokernel_ledger`) has no fixed bit
   price, so it is not priced here.
3. **The Perron navigator's code of a walk** (`Foundation/ReceiverCodeCost`). For a positive
   eigenvector `v` of a weighted adjacency with eigenvalue `λ`, whose transitions normalize
   (`perronTransition_normalized`, the Kraft equality that makes `−log₂ P` a code length), the code
   of a walk of `n` steps telescopes by `perron_edge_code_balance` to
   `n·log₂ λ − Σ log₂ w + log₂ v_start − log₂ v_end` (`perron_walk_code_length`).
4. The Gibbs/MDL posterior of `Foundation/NavigatorInference` on the two presentations prefers the
   navigator exactly when the pivot pays off (`posterior_prefers_iff_pays_off`): the instance of
   `posterior_mass_le_iff` at two candidates, whose objective is each presentation's bits.

[counterexample; formal-checked] The one-bit family (every map `Bool → Bool` as step and as read,
both initial configurations; `descriptionBits = 5`, `oneBit_descriptionBits`).
- **The alternator** `not` from `false`, read by the identity, regenerates the alternating word of
  every length (`alternator_regenerates`). `Kt(n) = 5 + ⌈log₂ n⌉` against `ℓ = n`: it pays off
  exactly from length `10` (`alternator_pays_off_iff`), on lengths `2^m` exactly from `m = 4`
  (`alternator_pays_off_iff_pow`). At `64`: `11 < 64`; at `8` it breaks even (`8 = 8`); at `4`:
  `7 > 4` (`alternation_witnesses`).
- **One founded face** in `64`: the partial code costs `Kt = 5 + 7 + 7 + 6 = 25 < 64`
  (`one_founded_face_pays_off`).
- **Material outside the family's image**: no navigator of the one-bit table regenerates
  `(false, false, true)` (`no_one_bit_navigator_regenerates`), and every partial code of the family
  for it costs at least its literal (`outside_material_stays_literal`).
- **The Perron code halves the literal** on a two-regular graph of four states: every walk of `n`
  steps costs exactly `n` bits against the literal's `2n` (`two_regular_perron_code`).

[definition] `Kt` is one limit reading of the receipt `(description, residual, work)`; the axes do
not exchange at a fixed rate and no single scalar of progress is asserted
(`docs/ELEMENTARY_OBJECTS.md`, "Emanation and resonance").
-/

noncomputable section

namespace Holonics.Compression.Core.Cost

open Holonics.Foundation.NavigatorInference
open Holonics.Foundation.ReceiverCodeCost

/-! ## 1. Fixed-width codes -/

/-- [definition] The `w`-bit code of `n`, most significant bit first. -/
def toBits : ℕ → ℕ → List Bool
  | 0, _ => []
  | w + 1, n => decide (n / 2 ^ w % 2 = 1) :: toBits w n

/-- [definition] The number a bit string names, most significant bit first. -/
def ofBits : List Bool → ℕ
  | [] => 0
  | b :: l => b.toNat * 2 ^ l.length + ofBits l

theorem toBits_length (w n : ℕ) : (toBits w n).length = w := by
  induction w with
  | zero => rfl
  | succ w ih => simp [toBits, ih]

theorem ofBits_toBits (w n : ℕ) : ofBits (toBits w n) = n % 2 ^ w := by
  induction w with
  | zero => simp [toBits, ofBits, Nat.mod_one]
  | succ w ih =>
    rw [toBits, ofBits, toBits_length, ih, Nat.mod_pow_succ]
    have h : (decide (n / 2 ^ w % 2 = 1)).toNat = n / 2 ^ w % 2 := by
      rcases Nat.mod_two_eq_zero_or_one (n / 2 ^ w) with h | h <;> simp [h]
    rw [h]
    ring

/-- [definition] The fixed width of an index below a population: `⌈log₂ population⌉` bits. -/
abbrev width (population : ℕ) : ℕ := Nat.clog 2 population

theorem ofBits_toBits_of_lt {population i : ℕ} (h : i < population) :
    ofBits (toBits (width population) i) = i := by
  rw [ofBits_toBits, Nat.mod_eq_of_lt (lt_of_lt_of_le h (Nat.le_pow_clog one_lt_two _))]

/-- [definition] Read one fixed-width index below `population` from the front of a code, refusing
a code shorter than the field. -/
def readField (population : ℕ) (code : List Bool) : Option (Fin population × List Bool) :=
  if h : width population ≤ code.length ∧ ofBits (code.take (width population)) < population then
    some (⟨_, h.2⟩, code.drop (width population))
  else none

/-- [proved-derived; formal-checked] A fixed-width field reads back its index and leaves the rest
of the code. -/
theorem readField_toBits {population : ℕ} (i : Fin population) (rest : List Bool) :
    readField population (toBits (width population) i ++ rest) = some (i, rest) := by
  have hlen := toBits_length (width population) i
  have hval : ofBits (toBits (width population) i) = i := ofBits_toBits_of_lt i.isLt
  have hcond : width population ≤ (toBits (width population) i ++ rest).length ∧
      ofBits ((toBits (width population) i ++ rest).take (width population)) < population := by
    refine ⟨?_, ?_⟩
    · rw [List.length_append, hlen]
      omega
    · rw [List.take_left' hlen, hval]
      exact i.isLt
  unfold readField
  rw [dif_pos hcond]
  simp [List.take_left' hlen, List.drop_left' hlen, hval]

/-- [proved-derived; formal-checked] **A field is read only from a code at least its width long**:
the code is the field's width followed by what remains, so a truncated code is refused (the Rust
decoder's `TruncatedCode`). -/
theorem readField_length {population : ℕ} {code : List Bool} {a : Fin population × List Bool}
    (h : readField population code = some a) : code.length = width population + a.2.length := by
  unfold readField at h
  split_ifs at h with hc
  obtain rfl := Option.some_inj.mp h
  simp only [List.length_drop]
  omega

/-! ## 2. The navigator codec and its causal decoder -/

/-- [definition] **A navigator codec**: a navigator step, its initial configuration (the key) and
the decoder's receiver face, read at each tick. -/
structure NavigatorCodec (Configuration Symbol : Type*) where
  /-- The navigator: one tick of its clock. -/
  step : Configuration → Configuration
  /-- Its initial configuration (the key). -/
  initial : Configuration
  /-- The decoder's receiver face, read at each tick. -/
  read : Configuration → Symbol

namespace NavigatorCodec

variable {Configuration Symbol : Type*} (c : NavigatorCodec Configuration Symbol)

/-- [definition] The decoder's release of `n` faces over `n` ticks of the navigator's clock. -/
def decode (n : ℕ) : List Symbol := List.ofFn fun k : Fin n => c.read (c.step^[k] c.initial)

theorem decode_length (n : ℕ) : (c.decode n).length = n := List.length_ofFn

/-- [proved-derived; formal-checked] **The decompression is causal**: the next face is the reading
at the next tick, appended to what was already released. -/
theorem decode_succ (n : ℕ) :
    c.decode (n + 1) = c.decode n ++ [c.read (c.step^[n] c.initial)] := by
  unfold decode
  rw [List.ofFn_succ_last]
  simp

/-- [proved-derived; formal-checked] The first `n` released faces do not depend on later ticks. -/
theorem decode_take (n m : ℕ) : (c.decode (n + m)).take n = c.decode n := by
  induction m with
  | zero => simp [List.take_of_length_le, decode_length]
  | succ m ih =>
    rw [← Nat.add_assoc, decode_succ, List.take_append_of_le_length (by simp [decode_length]), ih]

/-- [definition] The codec regenerates the material. -/
def Regenerates (material : List Symbol) : Prop := c.decode material.length = material

end NavigatorCodec

/-! ## 3. A codec family and the description code -/

/-- [definition] **A codec family**: the declared finite families of navigator steps, initial
configurations and receiver reads that coder and decoder share. -/
structure CodecFamily (Configuration Symbol : Type*) where
  steps : ℕ
  configurations : ℕ
  reads : ℕ
  step : Fin steps → Configuration → Configuration
  configuration : Fin configurations → Configuration
  read : Fin reads → Configuration → Symbol

namespace CodecFamily

variable {Configuration Symbol : Type*} (F : CodecFamily Configuration Symbol)

/-- [definition] A codec of the family, named by its three indices. -/
@[ext]
structure Index where
  step : Fin F.steps
  initial : Fin F.configurations
  read : Fin F.reads

/-- [definition] The navigator codec an index names. -/
def codec (i : F.Index) : NavigatorCodec Configuration Symbol :=
  ⟨F.step i.step, F.configuration i.initial, F.read i.read⟩

/-- [definition] The family's description bits: the three fixed widths. -/
def descriptionBits : ℕ := width F.steps + width F.configurations + width F.reads

/-- [definition] **The description of a codec**: its three indices in fixed width. -/
def describe (i : F.Index) : List Bool :=
  toBits (width F.steps) i.step ++ toBits (width F.configurations) i.initial ++
    toBits (width F.reads) i.read

/-- [proved-derived; formal-checked] Every description has the family's `descriptionBits`. -/
theorem describe_length (i : F.Index) : (F.describe i).length = F.descriptionBits := by
  simp [describe, descriptionBits, toBits_length, Nat.add_assoc]

/-- [definition] **The decoder of a description**: read the three indices from the front of a
code. -/
def readIndex (code : List Bool) : Option (F.Index × List Bool) :=
  (readField F.steps code).bind fun a =>
    (readField F.configurations a.2).bind fun b =>
      (readField F.reads b.2).map fun c => (⟨a.1, b.1, c.1⟩, c.2)

/-- [proved-derived; formal-checked] **The decoder reads the codec back from its description**,
followed by any continuation of the code. -/
theorem readIndex_describe (i : F.Index) (rest : List Bool) :
    F.readIndex (F.describe i ++ rest) = some (i, rest) := by
  simp only [readIndex, describe, List.append_assoc, readField_toBits, Option.bind_some,
    Option.map_some]

/-- [proved-derived; formal-checked] The decoder reads exactly the family's `descriptionBits` from
the front of a code. -/
theorem readIndex_length {code : List Bool} {a : F.Index × List Bool}
    (h : F.readIndex code = some a) : code.length = F.descriptionBits + a.2.length := by
  simp only [readIndex, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨x, hx, y, hy, z, hz, rfl⟩ := h
  have h1 := readField_length hx
  have h2 := readField_length hy
  have h3 := readField_length hz
  simp only [descriptionBits]
  omega

/-- [definition] The codec a whole code describes, refusing trailing bits. -/
def ofDescription (code : List Bool) : Option F.Index :=
  (F.readIndex code).bind fun a => if a.2 = [] then some a.1 else none

theorem ofDescription_describe (i : F.Index) : F.ofDescription (F.describe i) = some i := by
  rw [ofDescription, ← List.append_nil (F.describe i), readIndex_describe]
  simp

/-- [proved-derived; formal-checked] **Only a code of exactly `descriptionBits` describes a
codec**: a truncated code and one with trailing bits are both refused. -/
theorem ofDescription_length {code : List Bool} {i : F.Index} (h : F.ofDescription code = some i) :
    code.length = F.descriptionBits := by
  simp only [ofDescription, Option.bind_eq_some_iff] at h
  obtain ⟨a, ha, hi⟩ := h
  split_ifs at hi with hrest
  rw [F.readIndex_length ha, hrest, List.length_nil, Nat.add_zero]

/-- [proved-derived; formal-checked] Distinct codecs have distinct descriptions. -/
theorem describe_injective : Function.Injective F.describe := by
  intro i j h
  have := F.ofDescription_describe i
  rw [h, ofDescription_describe] at this
  exact (Option.some_injective _ this).symm

/-- [definition] **The decompression a description carries**: decode the codec, then release `n`
faces over the navigator's ticks. -/
def release (code : List Bool) (n : ℕ) : Option (List Symbol) :=
  (F.ofDescription code).map fun i => (F.codec i).decode n

end CodecFamily

/-! ## 4. The codec pivot, the literal and `Kt` -/

/-- [definition] **A codec pivot** of a material within a family: a codec of the family whose
causal release is exactly the material. -/
structure CodecPivot {Configuration Symbol : Type*} (F : CodecFamily Configuration Symbol)
    (material : List Symbol) where
  index : F.Index
  regenerates : (F.codec index).Regenerates material

namespace CodecPivot

variable {Configuration Symbol : Type*} {F : CodecFamily Configuration Symbol}
  {material : List Symbol} (p : CodecPivot F material)

/-- [definition] The pivot's code: the description of its codec. -/
def code : List Bool := F.describe p.index

/-- [definition] **Levin's cost** `Kt = |code| + ⌈log₂ t⌉`, with `t` the navigator's ticks, one
reading per tick. -/
def kt : ℕ := p.code.length + Nat.clog 2 material.length

theorem kt_eq : p.kt = F.descriptionBits + Nat.clog 2 material.length := by
  rw [kt, code, CodecFamily.describe_length]

/-- [proved-derived; formal-checked] **The pivot carries its decoder**: its code alone releases
the material. -/
theorem release_code : F.release p.code material.length = some material := by
  rw [CodecFamily.release, code, CodecFamily.ofDescription_describe, Option.map_some,
    p.regenerates]

end CodecPivot

section Literal

variable {Symbol : Type*} [Fintype Symbol]

/-- [definition] The fixed-width index of a symbol in its alphabet. -/
def symbolIndex (s : Symbol) : Fin (Fintype.card Symbol) := Fintype.equivFin Symbol s

/-- [definition] **The literal code**: every symbol's index in fixed width. -/
def literalCode : List Symbol → List Bool
  | [] => []
  | s :: m => toBits (width (Fintype.card Symbol)) (symbolIndex s) ++ literalCode m

/-- [definition] The literal's code length: `⌈log₂ |alphabet|⌉` bits per symbol. -/
def literalBits (Symbol : Type*) [Fintype Symbol] (material : List Symbol) : ℕ :=
  width (Fintype.card Symbol) * material.length

theorem literalCode_length (material : List Symbol) :
    (literalCode material).length = literalBits Symbol material := by
  induction material with
  | nil => simp [literalCode, literalBits]
  | cons s m ih =>
    rw [literalCode, List.length_append, toBits_length, ih, literalBits, literalBits,
      List.length_cons]
    ring

/-- [definition] The literal decoder: read `n` symbols, refusing trailing bits. -/
def readLiteral : ℕ → List Bool → Option (List Symbol)
  | 0, code => if code = [] then some [] else none
  | n + 1, code => (readField (Fintype.card Symbol) code).bind fun a =>
      (readLiteral n a.2).map fun m => (Fintype.equivFin Symbol).symm a.1 :: m

/-- [proved-derived; formal-checked] The literal code reads back its material. -/
theorem readLiteral_literalCode (material : List Symbol) :
    readLiteral material.length (literalCode material) = some material := by
  induction material with
  | nil => simp [readLiteral, literalCode]
  | cons s m ih =>
    simp only [List.length_cons, readLiteral, literalCode, readField_toBits, Option.bind_some, ih,
      Option.map_some, symbolIndex, Equiv.symm_apply_apply]

/-- [definition] **The pivot pays off**: `Kt` is below the literal's code length. -/
def CodecPivot.PaysOff {Configuration : Type*} {F : CodecFamily Configuration Symbol}
    {material : List Symbol} (p : CodecPivot F material) : Prop :=
  p.kt < literalBits Symbol material

/-- [proved-derived; formal-checked] Paying off is the comparison of the two actual codes. -/
theorem CodecPivot.paysOff_iff_code_shorter {Configuration : Type*}
    {F : CodecFamily Configuration Symbol} {material : List Symbol} (p : CodecPivot F material) :
    p.PaysOff ↔ p.code.length + Nat.clog 2 material.length < (literalCode material).length := by
  rw [CodecPivot.PaysOff, literalCode_length]
  rfl

end Literal

/-! ## 5. RIDE and FOUND in bits: the partial pivot -/

section Partial

variable {Configuration Symbol : Type*} [Fintype Symbol] [DecidableEq Symbol]

/-- [definition] **The founded faces**: the positions where the codec's release differs from the
material, which the residual must carry. -/
def foundedFaces (c : NavigatorCodec Configuration Symbol) (material : List Symbol) :
    List (Fin material.length) :=
  (List.finRange material.length).filter fun k =>
    (c.decode material.length)[(k : ℕ)]? ≠ material[(k : ℕ)]?

omit [Fintype Symbol] in
/-- [proved-derived; formal-checked] **A codec founds no face exactly when it regenerates the
material.** -/
theorem foundedFaces_eq_nil_iff (c : NavigatorCodec Configuration Symbol)
    (material : List Symbol) : foundedFaces c material = [] ↔ c.Regenerates material := by
  rw [foundedFaces, List.filter_eq_nil_iff, NavigatorCodec.Regenerates]
  constructor
  · intro h
    apply List.ext_getElem?
    intro k
    by_cases hk : k < material.length
    · have := h ⟨k, hk⟩ (List.mem_finRange _)
      simpa using this
    · rw [List.getElem?_eq_none (by rw [NavigatorCodec.decode_length]; omega),
        List.getElem?_eq_none (by omega)]
  · intro h k _
    simp [h]

/-- [definition] One patch: a founded position and its symbol, in fixed width. -/
def patchCode (material : List Symbol) (k : Fin material.length) : List Bool :=
  toBits (width material.length) k ++
    toBits (width (Fintype.card Symbol)) (symbolIndex material[(k : ℕ)])

/-- [definition] **The partial code** of a codec on a material: its description, the count of
founded faces, and one patch per founded face. -/
def CodecFamily.partialCode (F : CodecFamily Configuration Symbol) (i : F.Index)
    (material : List Symbol) : List Bool :=
  F.describe i ++ toBits (width (material.length + 1)) (foundedFaces (F.codec i) material).length ++
    (foundedFaces (F.codec i) material).flatMap (patchCode material)

/-- [proved-derived; formal-checked] **The RIDE/FOUND ledger in bits.** The partial code costs the
description, the count field, and one patch of `⌈log₂ n⌉ + ⌈log₂ |A|⌉` bits for each founded face;
a regenerated face costs nothing further. -/
theorem CodecFamily.partialCode_length (F : CodecFamily Configuration Symbol) (i : F.Index)
    (material : List Symbol) :
    (F.partialCode i material).length =
      F.descriptionBits + width (material.length + 1) +
        (foundedFaces (F.codec i) material).length *
          (width material.length + width (Fintype.card Symbol)) := by
  rw [CodecFamily.partialCode, List.length_append, List.length_append, F.describe_length,
    toBits_length, List.length_flatMap]
  simp [patchCode, toBits_length, List.map_const', List.sum_replicate]

/-- [definition] Read `count` patches at positions below `n`. -/
def readPatches (n : ℕ) : ℕ → List Bool → Option (List (ℕ × Symbol) × List Bool)
  | 0, code => some ([], code)
  | count + 1, code => (readField n code).bind fun a =>
      (readField (Fintype.card Symbol) a.2).bind fun b =>
        (readPatches n count b.2).map fun r =>
          (((a.1 : ℕ), (Fintype.equivFin Symbol).symm b.1) :: r.1, r.2)

/-- [definition] Write each patch's symbol at its position. -/
def applyPatches (released : List Symbol) (patches : List (ℕ × Symbol)) : List Symbol :=
  patches.foldl (fun acc p => acc.set p.1 p.2) released

/-- [definition] **The partial decoder**: the codec, the count, the patches, then release and
patch; trailing bits are refused. -/
def CodecFamily.partialRelease (F : CodecFamily Configuration Symbol) (code : List Bool)
    (n : ℕ) : Option (List Symbol) :=
  (F.readIndex code).bind fun a =>
    (readField (n + 1) a.2).bind fun b =>
      (readPatches n b.1 b.2).bind fun c =>
        if c.2 = [] then some (applyPatches ((F.codec a.1).decode n) c.1) else none

omit [DecidableEq Symbol] in
theorem readPatches_flatMap (material : List Symbol) (ks : List (Fin material.length))
    (rest : List Bool) :
    readPatches material.length ks.length (ks.flatMap (patchCode material) ++ rest) =
      some (ks.map fun k : Fin material.length => ((k : ℕ), material[(k : ℕ)]'k.isLt), rest) := by
  induction ks with
  | nil => simp [readPatches]
  | cons k ks ih =>
    simp only [List.length_cons, readPatches, List.flatMap_cons, patchCode, List.append_assoc,
      readField_toBits, Option.bind_some, ih, Option.map_some, symbolIndex,
      Equiv.symm_apply_apply, List.map_cons]

omit [Fintype Symbol] [DecidableEq Symbol] in
theorem applyPatches_eq {material : List Symbol} :
    ∀ (patches : List (ℕ × Symbol)) (acc : List Symbol), acc.length = material.length →
      (∀ p ∈ patches, material[p.1]? = some p.2) →
      (∀ k < material.length, (∃ p ∈ patches, p.1 = k) ∨ acc[k]? = material[k]?) →
      applyPatches acc patches = material := by
  intro patches
  induction patches with
  | nil =>
    intro acc hlen _ hcover
    rw [applyPatches, List.foldl_nil]
    apply List.ext_getElem?
    intro k
    by_cases hk : k < material.length
    · rcases hcover k hk with ⟨p, hp, _⟩ | h
      · simp at hp
      · exact h
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
  | cons p patches ih =>
    intro acc hlen hsym hcover
    rw [applyPatches, List.foldl_cons]
    apply ih
    · rw [List.length_set, hlen]
    · exact fun q hq => hsym q (List.mem_cons_of_mem _ hq)
    · intro k hk
      by_cases hpk : p.1 = k
      · right
        subst hpk
        have hp := hsym p List.mem_cons_self
        have hlt : p.1 < acc.length := by
          rw [hlen]; exact (List.getElem?_eq_some_iff.mp hp).1
        rw [List.getElem?_set_self hlt, hp]
      · rcases hcover k hk with ⟨q, hq, hqk⟩ | h
        · left
          rcases List.mem_cons.mp hq with rfl | hq
          · exact absurd hqk hpk
          · exact ⟨q, hq, hqk⟩
        · right
          rw [List.getElem?_set_ne hpk, h]

/-- [proved-derived; formal-checked] **The partial pivot carries its decoder**: for every codec of
the family and every material, the partial code alone releases the material. -/
theorem CodecFamily.partialRelease_partialCode (F : CodecFamily Configuration Symbol)
    (i : F.Index) (material : List Symbol) :
    F.partialRelease (F.partialCode i material) material.length = some material := by
  set ks := foundedFaces (F.codec i) material with hks
  have hcount : ks.length < material.length + 1 := by
    have h1 : ks.length ≤ (List.finRange material.length).length := by
      rw [hks, foundedFaces]
      exact List.length_filter_le _ _
    rw [List.length_finRange] at h1
    omega
  have hread := F.readIndex_describe i
    (toBits (width (material.length + 1)) ks.length ++ ks.flatMap (patchCode material))
  have hfield := readField_toBits (population := material.length + 1) ⟨ks.length, hcount⟩
    (ks.flatMap (patchCode material))
  have hpatch := readPatches_flatMap material ks []
  rw [List.append_nil] at hpatch
  rw [CodecFamily.partialRelease, CodecFamily.partialCode, ← hks, List.append_assoc, hread]
  simp only [Option.bind_some]
  rw [hfield]
  simp only [Option.bind_some]
  rw [hpatch]
  simp only [Option.bind_some, if_true]
  congr 1
  apply applyPatches_eq
  · exact NavigatorCodec.decode_length _ _
  · intro p hp
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hp
    simp
  · intro k hk
    by_cases hf : (⟨k, hk⟩ : Fin material.length) ∈ ks
    · left
      exact ⟨(k, material[k]), List.mem_map.mpr ⟨⟨k, hk⟩, hf, rfl⟩, rfl⟩
    · right
      rw [hks, foundedFaces, List.mem_filter] at hf
      simpa [List.mem_finRange] using hf

end Partial

/-! ## 6. The Perron navigator's code of a walk (`Foundation/ReceiverCodeCost`) -/

section Perron

open Finset

variable {Index : Type*}

/-- [definition] **The Perron code length** of the first `n` steps of a walk, in bits:
`Σ −log₂ P(w_k → w_(k+1))` with `P` the normalized Perron transition. -/
def perronCodeLength (weight : Index → Index → ℝ) (mode : Index → ℝ) (eigenvalue : ℝ)
    (walk : ℕ → Index) (n : ℕ) : ℝ :=
  ∑ k ∈ range n, -Real.log (perronTransition (weight (walk k) (walk (k + 1))) (mode (walk k))
    (mode (walk (k + 1))) eigenvalue) / Real.log 2

/-- [proved-derived; formal-checked] **The Perron code of a walk telescopes** by
`perron_edge_code_balance`: `n·log₂ λ − Σ log₂ w + log₂ v_start − log₂ v_end`. -/
theorem perron_walk_code_length (weight : Index → Index → ℝ) (mode : Index → ℝ)
    {eigenvalue : ℝ} (hl : 0 < eigenvalue) (hv : ∀ i, 0 < mode i) (walk : ℕ → Index) (n : ℕ)
    (hw : ∀ k < n, 0 < weight (walk k) (walk (k + 1))) :
    perronCodeLength weight mode eigenvalue walk n =
      n * (Real.log eigenvalue / Real.log 2) -
        ∑ k ∈ range n, Real.log (weight (walk k) (walk (k + 1))) / Real.log 2 +
        Real.log (mode (walk 0)) / Real.log 2 - Real.log (mode (walk n)) / Real.log 2 := by
  induction n with
  | zero => simp [perronCodeLength]
  | succ n ih =>
    have ih' := ih fun k hk => hw k (by omega)
    rw [perronCodeLength, sum_range_succ, ← perronCodeLength, ih',
      perron_edge_code_balance (hw n (by omega)) (hv _) (hv _) hl, sum_range_succ]
    push_cast
    ring

/-- The two-regular graph on four states: `i → i + 1` and `i → i + 2`, unit weights. -/
def twoRegular (i j : Fin 4) : ℝ := if j = i + 1 ∨ j = i + 2 then 1 else 0

/-- [counterexample; formal-checked] **The Perron code halves the literal.** On the two-regular
graph of four states, `v ≡ 1` is a positive eigenvector at `λ = 2`, each row of transitions
normalizes, and every walk along its edges costs exactly `n` bits, against the literal's
`⌈log₂ 4⌉ · n = 2n`. -/
theorem two_regular_perron_code (walk : ℕ → Fin 4)
    (hwalk : ∀ k, twoRegular (walk k) (walk (k + 1)) = 1) (n : ℕ) :
    (∀ i, ∑ j, twoRegular i j * (fun _ => (1 : ℝ)) j = 2 * (fun _ => (1 : ℝ)) i) ∧
      (∀ i, ∑ j, perronTransition (twoRegular i j) 1 1 2 = 1) ∧
      perronCodeLength twoRegular (fun _ => 1) 2 walk n = n ∧ width 4 * n = 2 * n := by
  have hrow : ∀ i, ∑ j, twoRegular i j * (fun _ => (1 : ℝ)) j = 2 * (fun _ => (1 : ℝ)) i := by
    intro i
    rw [Fin.sum_univ_four]
    fin_cases i <;> simp (config := { decide := true }) [twoRegular] <;> norm_num
  refine ⟨hrow, fun i => ?_, ?_, ?_⟩
  · have := perronTransition_normalized twoRegular (fun _ => (1 : ℝ)) 2 i one_ne_zero two_ne_zero
      (hrow i)
    simpa using this
  · rw [perron_walk_code_length twoRegular _ two_pos (fun _ => one_pos) walk n
      (fun k _ => by rw [hwalk k]; exact one_pos)]
    simp only [hwalk, Real.log_one, zero_div, Finset.sum_const_zero, sub_zero, add_zero]
    field_simp [Real.log_pos one_lt_two]
  · have : width 4 = 2 := by decide
    rw [this]

end Perron

/-! ## 7. The posterior reading -/

/-- [definition] The two presentations of one material. -/
inductive Presentation
  | navigator
  | literal
  deriving DecidableEq

instance : Fintype Presentation :=
  ⟨{.navigator, .literal}, by intro x; cases x <;> simp⟩

instance : Nonempty Presentation := ⟨.literal⟩

/-- [definition] Each presentation's bits as the inference objective. -/
def presentationBits (navigatorBits literal : ℕ) : Presentation → ℝ
  | .navigator => navigatorBits
  | .literal => literal

/-- [proved-derived; formal-checked] The instance of `NavigatorInference.posterior_mass_le_iff` at
two candidates: the bit-objective posterior prefers the navigator exactly when the pivot pays
off. -/
theorem posterior_prefers_iff_pays_off {Configuration Symbol : Type*} [Fintype Symbol]
    {F : CodecFamily Configuration Symbol} {material : List Symbol}
    (p : CodecPivot F material) :
    (posterior (presentationBits p.kt (literalBits Symbol material))).mass .literal <
        (posterior (presentationBits p.kt (literalBits Symbol material))).mass .navigator ↔
      p.PaysOff := by
  rw [← not_le, posterior_mass_le_iff, not_le, CodecPivot.PaysOff]
  simp [presentationBits]

/-! ## 8. The one-bit family and the alternator -/

/-- The one-bit maps: `const false`, `const true`, `id`, `not`. -/
def oneBitMaps : Fin 4 → Bool → Bool := ![fun _ => false, fun _ => true, id, not]

/-- [definition] **The one-bit family**: every one-bit map as step and as read, both initial
configurations. -/
def oneBit : CodecFamily Bool Bool where
  steps := 4
  configurations := 2
  reads := 4
  step := oneBitMaps
  configuration := ![false, true]
  read := oneBitMaps

theorem oneBit_descriptionBits : oneBit.descriptionBits = 5 := by decide

/-- [proved-derived; formal-checked] **A truncated one-bit code is refused**: no code shorter than
the five description bits decodes (the Rust `TruncatedCode`). -/
theorem oneBit_truncated_refused (code : List Bool) (h : code.length < 5) :
    oneBit.ofDescription code = none := by
  cases hc : oneBit.ofDescription code with
  | none => rfl
  | some i =>
    have := oneBit.ofDescription_length hc
    rw [oneBit_descriptionBits] at this
    omega

/-- [definition] The alternator's index: the step `not`, the initial configuration `false`, the
read `id`. -/
def alternatorIndex : oneBit.Index := ⟨⟨3, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩⟩

theorem alternator_codec : oneBit.codec alternatorIndex = ⟨not, false, id⟩ := rfl

/-- [definition] The alternating word of length `n`: `false, true, false, …`. -/
def alternating (n : ℕ) : List Bool := List.ofFn fun k : Fin n => decide (k.val % 2 = 1)

theorem not_iterate_false (k : ℕ) : not^[k] false = decide (k % 2 = 1) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    by_cases h : k % 2 = 1
    · have h' : ¬ (k + 1) % 2 = 1 := by omega
      simp [h, h']
    · have h' : (k + 1) % 2 = 1 := by omega
      simp [h, h']

/-- [proved-derived; formal-checked] The alternator regenerates the alternating word of every
length. -/
theorem alternator_regenerates (n : ℕ) :
    (oneBit.codec alternatorIndex).Regenerates (alternating n) := by
  rw [alternator_codec]
  simp only [NavigatorCodec.Regenerates, alternating, List.length_ofFn, NavigatorCodec.decode]
  congr 1
  funext k
  simp [not_iterate_false]

/-- The alternator as a codec pivot of the alternating word. -/
def alternatorPivot (n : ℕ) : CodecPivot oneBit (alternating n) :=
  ⟨alternatorIndex, alternator_regenerates n⟩

theorem alternatorPivot_kt (n : ℕ) : (alternatorPivot n).kt = 5 + Nat.clog 2 n := by
  rw [CodecPivot.kt_eq, oneBit_descriptionBits, alternating, List.length_ofFn]

theorem literalBits_alternating (n : ℕ) : literalBits Bool (alternating n) = n := by
  have h : width (Fintype.card Bool) = 1 := by decide
  rw [literalBits, h, alternating, List.length_ofFn, one_mul]

theorem le_two_pow_sub_six {n : ℕ} (hn : 10 ≤ n) : n ≤ 2 ^ (n - 6) := by
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [show n + 1 - 6 = (n - 6) + 1 by omega, pow_succ]
    omega

/-- [proved-derived; formal-checked] **The alternator pays off exactly from length `10`**:
`5 + ⌈log₂ n⌉ < n ⇔ n ≥ 10`. -/
theorem alternator_pays_off_iff (n : ℕ) : (alternatorPivot n).PaysOff ↔ 10 ≤ n := by
  rw [CodecPivot.PaysOff, alternatorPivot_kt, literalBits_alternating]
  constructor
  · intro h
    by_contra hn
    have hlt : n < 10 := by omega
    have h2 : ∀ y, 2 ^ y < n → y < Nat.clog 2 n := fun y hy =>
      (Nat.lt_clog_iff_pow_lt one_lt_two).mpr hy
    interval_cases n <;> first
      | omega
      | (have := h2 2 (by norm_num); omega)
      | (have := h2 3 (by norm_num); omega)
  · intro hn
    have := Nat.clog_le_of_le_pow (le_two_pow_sub_six hn)
    omega

theorem five_add_lt_two_pow_iff (m : ℕ) : 5 + m < 2 ^ m ↔ 4 ≤ m := by
  constructor
  · intro h
    by_contra hm
    interval_cases m <;> norm_num at h
  · intro hm
    induction m, hm using Nat.le_induction with
    | base => norm_num
    | succ m _ ih =>
      rw [pow_succ]
      omega

/-- [proved-derived; formal-checked] On lengths `2^m` the alternator pays off exactly from
`m = 4`. -/
theorem alternator_pays_off_iff_pow (m : ℕ) : (alternatorPivot (2 ^ m)).PaysOff ↔ 4 ≤ m := by
  rw [CodecPivot.PaysOff, alternatorPivot_kt, literalBits_alternating,
    Nat.clog_pow 2 m one_lt_two, five_add_lt_two_pow_iff]

/-- [counterexample; formal-checked] **The alternator against the literal**: on `64` symbols
`Kt = 11 < 64`; on `8` it breaks even, `8 = 8`; on `4`, `Kt = 7 > 4`. -/
theorem alternation_witnesses :
    (alternatorPivot 64).kt = 11 ∧ literalBits Bool (alternating 64) = 64 ∧
      (alternatorPivot 64).PaysOff ∧
      (alternatorPivot 8).kt = 8 ∧ ¬ (alternatorPivot 8).PaysOff ∧
      (alternatorPivot 4).kt = 7 ∧ ¬ (alternatorPivot 4).PaysOff := by
  refine ⟨?_, literalBits_alternating 64, (alternator_pays_off_iff 64).mpr (by norm_num), ?_,
    fun h => absurd ((alternator_pays_off_iff 8).mp h) (by norm_num), ?_,
    fun h => absurd ((alternator_pays_off_iff 4).mp h) (by norm_num)⟩ <;>
    rw [alternatorPivot_kt] <;> decide

/-- [counterexample; formal-checked] **Material outside the navigator family's image.** No
navigator of the one-bit table, from either initial configuration and with any one-bit read,
regenerates `(false, false, true)`: no codec pivot of this family exists for it. -/
theorem no_one_bit_navigator_regenerates :
    ∀ c : NavigatorCodec Bool Bool, ¬ c.Regenerates [false, false, true] := by
  intro c hc
  have key : ∀ (step read : Bool → Bool) (initial : Bool),
      (List.ofFn fun k : Fin 3 => read (step^[k] initial)) ≠ [false, false, true] := by
    decide
  exact key c.step c.read c.initial hc

/-- [counterexample; formal-checked] **Residual outside the image stays literal.** Every partial
code of the one-bit family for `(false, false, true)` costs at least its literal's `3` bits. -/
theorem outside_material_stays_literal (i : oneBit.Index) :
    literalBits Bool [false, false, true] ≤
      (oneBit.partialCode i [false, false, true]).length + Nat.clog 2 3 := by
  rw [CodecFamily.partialCode_length, oneBit_descriptionBits]
  have : literalBits Bool [false, false, true] = 3 := by decide
  omega

/-- The alternating word of length `64` with the face at `10` flipped. -/
def flippedAlternating : List Bool := (alternating 64).set 10 true

/-- [counterexample; formal-checked] **One founded face still pays off.** The alternator founds
exactly the flipped face, and its partial code costs `5 + 7 + 7 = 19` bits, so
`Kt = 19 + 6 = 25 < 64`. -/
theorem one_founded_face_pays_off :
    (foundedFaces (oneBit.codec alternatorIndex) flippedAlternating).length = 1 ∧
      (oneBit.partialCode alternatorIndex flippedAlternating).length + Nat.clog 2 64 = 25 ∧
      25 < literalBits Bool flippedAlternating := by
  have hlen : flippedAlternating.length = 64 := by simp [flippedAlternating, alternating]
  have hdec : (oneBit.codec alternatorIndex).decode flippedAlternating.length = alternating 64 := by
    have h := alternator_regenerates 64
    unfold NavigatorCodec.Regenerates at h
    rw [hlen]
    rwa [show (alternating 64).length = 64 by simp [alternating]] at h
  have key : ∀ j : ℕ, ((alternating 64)[j]? ≠ flippedAlternating[j]? ↔ j = 10) := by
    intro j
    rw [flippedAlternating, List.getElem?_set]
    by_cases h : j = 10
    · subst h
      simp [alternating]
    · simp [Ne.symm h, h]
  have h10 : 10 < flippedAlternating.length := by rw [hlen]; norm_num
  have hfounded : (foundedFaces (oneBit.codec alternatorIndex) flippedAlternating).length = 1 := by
    rw [foundedFaces, ← List.countP_eq_length_filter]
    have hc : List.countP (fun k : Fin flippedAlternating.length =>
        decide (((oneBit.codec alternatorIndex).decode flippedAlternating.length)[(k : ℕ)]? ≠
          flippedAlternating[(k : ℕ)]?)) (List.finRange flippedAlternating.length) =
        List.countP (fun k => k == ⟨10, h10⟩) (List.finRange flippedAlternating.length) := by
      apply List.countP_congr
      intro k _
      simp only [decide_eq_true_eq, beq_iff_eq, Fin.ext_iff]
      rw [hdec]
      exact key k
    rw [hc]
    exact List.count_finRange _
  refine ⟨hfounded, ?_, ?_⟩
  · rw [CodecFamily.partialCode_length, hfounded, oneBit_descriptionBits, hlen]
    have h65 : Nat.clog 2 65 = 7 := by decide
    have h64 : Nat.clog 2 64 = 6 := by decide
    have h2 : width (Fintype.card Bool) = 1 := by decide
    simp only [width, h65, h64] at *
    rw [h2]
  · rw [literalBits, hlen]
    decide

section Audit

#print axioms readField_toBits
#print axioms readField_length
#print axioms CodecFamily.readIndex_length
#print axioms CodecFamily.ofDescription_length
#print axioms oneBit_truncated_refused
#print axioms NavigatorCodec.decode_succ
#print axioms NavigatorCodec.decode_take
#print axioms CodecFamily.readIndex_describe
#print axioms CodecFamily.describe_injective
#print axioms CodecPivot.release_code
#print axioms readLiteral_literalCode
#print axioms foundedFaces_eq_nil_iff
#print axioms CodecFamily.partialCode_length
#print axioms CodecFamily.partialRelease_partialCode
#print axioms perron_walk_code_length
#print axioms two_regular_perron_code
#print axioms posterior_prefers_iff_pays_off
#print axioms alternator_pays_off_iff
#print axioms alternator_pays_off_iff_pow
#print axioms alternation_witnesses
#print axioms no_one_bit_navigator_regenerates
#print axioms outside_material_stays_literal
#print axioms one_founded_face_pays_off

end Audit

end Holonics.Compression.Core.Cost
