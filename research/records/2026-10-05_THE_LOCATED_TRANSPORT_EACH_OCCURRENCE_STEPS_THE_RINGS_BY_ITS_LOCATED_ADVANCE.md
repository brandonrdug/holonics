# The located transport: each occurrence steps the rings by its located advance

**Date.** October 5. **Issues.** #73, #148, #63, #62. **Lanes.** E and B of U6 (THE_REBUILD, "U6's
order from October 5"): the helical encoding's missing operation. **Grade.** [definition;
agent-inferred] for the pins of §0, fixed and committed before any read; [proved-derived] where
marked; [measured] for the counts of the later sections.

**Occasion.** The field's selective step advances ring `g` by `[port_g(u) ∈ N_g] + carry`, and its
port chart is the residue chart `port_g(u) = u mod d_g` (`hnn::field::Field::selective_step`,
`PortChart::residue`): the codec chooses which cells step which rings. Guard 9 of
[THE_MACHINE](../../docs/THE_MACHINE.md#guards-that-make-the-rejected-forms-impossible) refuses
that chart and asks that the code length not see the labels, `L(field; π∘x) = L(field; x)`. The
operation that replaces it, how far an occurrence of `u` advances ring `g`, has no owner. This loop
builds it as key location on a known-truth terrain whose truth is that transport.

## 0. The claim and the pins, fixed before any read

### 0.1 The law, as derived from the records

[proved-derived; the records cited] An occurrence `k` of a source enters at the navigators' phases
after its admitted steps, `m_g = Σ_k Ĝ_g(τ_g(k))⁻¹ E(u_k)` (`Transport/SourceMoment`, `hnn::moment`;
the [retention audit](2026-09-22_RETENTION_IS_A_QUOTIENT_NOT_A_TAPE_AND_THE_SOURCE_ENTERS_AS_PHASE_CARRIED_MOMENTS.md)).
The phases are one lift `ℓ ∈ ℤ/D`, `D = ∏ d_g`, of the rings' joint clock, and the missing
operation is the cell's **located transport** `A(u) ∈ ℤ/D`:

```text
ℓ(k+1) = ℓ(k) + A(u_k)                                   the address: ℓ(k) = ℓ(0) + Σ_(j<k) A(u_j)
odometer chart (ring 0 least significant, w_g = ∏_(h<g) d_h):
  τ_g(k+1) = τ_g(k) + a_g(u_k) + carry_g(k)  (mod d_g),   carry_(g+1)(k) = ⌊(τ_g(k) + a_g(u_k) + carry_g(k)) / d_g⌋
  A(u) = Σ_g a_g(u) w_g                                     (winding_add: the carry is the defect of additivity)
CRT chart (pairwise coprime d_g):  r_g(k+1) = r_g(k) + (A(u_k) mod d_g),  no carry
```

Two corrections to the brief's wording, each derived:
1. **The two charts are one lift.** "Order carried by the passage clock's residues across coprime
   rings (CRT) and the carry cocycle" holds as two charts of the same address, not as a residue
   plus a carry: the CRT chart carries `ℓ(k) mod d_g` with no carry, the odometer chart its digits
   with the carry. The occurrence count's residues `k mod d_g` carry order only at the identity
   advance (`A ≡ 1`); under a located transport the lift is the source word's address.
2. **What a receiver can locate is `A(u)` up to the receiving ring's gauge, which is dihedral.**
   When the emission reads the receiving ring's digit (§0.2), the rings below it are read only
   through their joint winding, the carry word into the receiving ring (J2 of the
   [gap record](2026-10-05_THE_GHOST_LIVES_IN_THE_GAP_THE_JOINTS_OF_THE_LENS.md): the winding is the
   carry), so the located object is `A(u) ∈ ℤ/D` and each digit `a_g(u)` follows from the
   mixed-radix bijection. Its gauge is the receiving ring's rotation `ℓ ↦ ℓ + j·D_low` with
   `λ ↦ λ∘ρ^(−j)`, and also the reflection `ℓ ↦ D_low − 1 − ℓ`, `A ↦ −A`, `λ ↦ λ∘(c ↦ −c)`
   [proved-derived: the digits of `D − 1 − ℓ` are `d_g − 1 − τ_g`, so the receiving digit reflects
   and the step negates; checked by the owner's brute-force test]: every passage is read alike under
   both, as the turn menu's reflector gauge pairs `c` with `−c`.

The located `A` is the Enigma's stepping inferred (which cells step which rotors, and by how much),
not its plugboard: a permutation chart `S⁻¹ U S` on the classes stays bijective, while under a
located transport one class is followed by different classes as the carry differs (a many-to-many
relation on the classes).

### 0.2 The terrain [definition; agent-inferred]

- **The navigators**: three closing rings of pairwise coprime periods `(3, 4, 5)` in the odometer
  chart, `D = 60 = 2²·3·5` (the order-2 declaration's ring period; by CRT `ℤ/60 ≅ ℤ/3 × ℤ/4 × ℤ/5`).
  Rings 0 and 1 are hidden; ring 2 is the receiving ring. Its digit is the lift read at the grain
  `D_low = 12`: `c(ℓ) = ⌊ℓ / 12⌋`.
- **The truth**, drawn by the exact routine (`Draw::new(seed)`, in this order): the transport
  `A(u) ∈ ℤ/60` for each class `u ∈ ℤ/5`, a bijection `λ: ℤ/5 → ℤ/5` (the receiving chart's labels,
  cell to class), and each passage's key `ℓ_p(0) ∈ ℤ/60`.
- **The passage** (autonomous): `u_k = λ(c(ℓ(k)))`, `ℓ(k+1) = ℓ(k) + A(u_k)`. The machine reads only
  the emitted classes, never `A`, `λ` or a key. `|A| = 5`.
- **The read set**: 16 passages of 60 cells each (one turn of the joint clock), 960 observations.
- **The seeds**, searched in every ref's history, the tree and the receipts (`2_026_100_9xx` appears
  nowhere): development `2_026_100_901` (timing and checks); **the read, once each**, the draws
  `2_026_100_911`, `912`, `913`, `914`; their repair passages' keys from `2_026_100_921`, `922`,
  `923`, `924`.

### 0.3 The path [definition; agent-inferred]

1. **Locate** (`compression::keys::transport`, the library owner). Survivor elimination over the
   machine's own family (rings of the declared periods with carry; every transport, every label
   bijection, every key): a survivor is a partial transport, a partial label map and the set of
   lifts it still admits. Each emission is one observation and closes the loop since its class's
   last visit: the lift must lie in the cell its class is labelled with, so a recurrence `u_k = u_k′`
   declares `c(ℓ(0) + Σ_(j<k) A(u_j)) = c(ℓ(0) + Σ_(j<k′) A(u_j))` and a non-recurrence its negation
   (labels injective). A class's first step branches its advance over `ℤ/60`; nothing is set by a
   class's code. The rotation gauge is fixed by the convention that the read set's first emission
   reads the receiving digit `0`; the reflection is kept, and the fibre is read in its classes, the
   representative chosen in first-occurrence order (label-free).
2. **Relabel.** For every permutation `π` of `ℤ/5` (all 120), the same location on `π∘x`.
3. **Found** (`hnn::encoding`, read-only). The passage chart `ℚ^60` with the admitted transports
   `T_u e_ℓ = e_(ℓ + A(u))` (the located advances), the receiving forms `ρ_c = Σ_(ℓ: λ(c(ℓ)) = c) e_ℓ*`
   (the located labels) and the openings `e_(ℓ_p(0))` (the located keys), founded by
   `Encoding::found`; its squares checked by `Encoding::squares`.
4. **Code** (an actual prefix code over declared `D`, `|A|`, the passage count and length): the
   transport per receiving digit in `⌈log₂ D⌉` bits each, the labels as a permutation index in
   `⌈log₂ |A|!⌉` bits, each passage's key in `⌈log₂ D⌉` bits, then the residual: a patch count in
   `⌈log₂(n + 1)⌉` bits and each patch as its position in `⌈log₂ n⌉` bits and its class among the
   other `|A| − 1` in `⌈log₂(|A| − 1)⌉` bits. The decoder steps the lift by the decoded cell's advance
   (the source steps the rings) and reads the next cell through the labels. Beside it, the residue
   chart's navigator: `A_res(u) = Σ_g [u mod d_g ∈ N_g] w_g` with the field's single notch
   `N_g = {0}` (its description: the lock sets, `3 + 4 + 5 = 12` bits), its labels and keys chosen
   to minimize its patches.
5. **Repair.** 16 fresh passages per draw (same `A`, `λ`; keys from the repair seed), the declared
   damage erasing cells `{3} ∪ [6, 10) ∪ [20, 25) ∪ [33, 37) ∪ [44, 48) ∪ [55, 60)` (23 erased, 37
   intact; the tail is continuation as the special case). With the transport and labels located on
   the draw's read set, each passage's lift family is restricted from both sides through the
   located navigator `F(ℓ) = ℓ + A(λ(c(ℓ)))` (an intact cell admits its cell's 12 lifts, an erased
   one all 60), the fixed point certified against the joint fibre (the keys the intact cells
   admit), and each erased cell released through `receiver::release` at tolerance zero when its
   class family is one class, held otherwise. Its residual is the repair owner's (the truth's index
   in the first held family, pinned and re-run), decoded and checked to reopen every passage.

### 0.4 The measures [definition]

The fibre outcome at the read set's end (one gauge class, plural, empty) and whether it is the
generator's; the survivors per observation (survivors and lifts); `n*_machine`, the least
observation count from which the survivors' transports are one gauge class with every class's
advance set, held to the read set's end; the terrain's unicity count `n_U`, the least `n` with
`|A|^(n−1) ≥ D^|A| · |A|! / 10` (the classes of transports and labels under the dihedral gauge of
order 10 must take distinct emission words after the gauge-fixed first one), `n_U = 16` since
`5^14 = 6,103,515,625 < 9,331,200,000 ≤ 5^15`; the relabelling law (located transport and code
length under all 120 permutations, and the residue chart's code length under them); the founded
dimension, reached span and the squares; the code lengths against the literal `960·⌈log₂ 5⌉ = 2,880`
bits; the repair's released, held and correct cells, its residual bits against the literal
`368·3 = 1,104` bits a draw, and every passage reopened.

### 0.5 The claim [derived from §0.1; agent-inferred]

On every read draw:
- **Location.** The fibre at the read set's end is one gauge class and it is the generator's (`A`
  or its reflection `−A`, with the labels to match); `n_U = 16 ≤ n*_machine ≤ 240` (located within
  the first four passages).
- **Relabelling.** For all 120 permutations the located transport on `π∘x` is `A∘π⁻¹` (exactly, on
  the label-free representative), the outcome is the same and the code length is equal; the residue
  chart's code length changes under at least one permutation.
- **Founding.** The squares `D E = ρ`, `E T_u = U_u E` hold exactly on every reached state; the
  founded dimension equals the reached span, `60` on a draw whose advances generate `ℤ/60`.
- **Code.** The located navigators regenerate the read set with no patch: `30 + 7 + 16·6 + 10 = 143`
  bits against the literal `2,880`; the residue chart's code is longer than the located one.
- **Repair.** Every released cell equals its truth; at least 332 of the 368 erased cells are released
  (nine tenths); every passage reopens from its residual, whose bits are below the literal `1,104`.

A located class other than the generator's, a fibre without the truth, a relabelling that changes
the located transport or the code length, a square that fails, a released cell that differs from
its truth, or a code at or above the literal falsifies the claim.

The computational object is the helical pair interaction. Of the
[winding guide](../../docs/WINDING_CARRY_AND_PLACEMENT.md)'s six objects this loop touches **the
helix** (circle + carry: the odometer's carries are the hidden rings' winding read by the receiving
ring), **the tower thread** (each ring's carry is the next ring's step: the carry tower over the
lift, and its CRT chart), **the cell holonomy** (a recurrence closes the loop of the steps between
two visits of one receiving cell), **faces and placement** (the receiving chart's labels, the
encoding's `D`) and **the tube** (the repair carries the lift family across the damage). The pair
stays attached: two visits of one cell are the pair contact between two crossings of the receiving
ring's section, here read through the lift rather than through a located pair `(δ, f)`.

## 1. The recorded failures this loop could repeat, and how each is held

From the [lessons](2026-09-29_LESSONS_THE_FAILURES_THAT_REPEATED_AFTER_THEY_WERE_RECORDED.md) and
the [prototypes' lessons](2026-09-24_LESSONS_FROM_THE_WORKBENCH_AND_ATHENA_PROTOTYPES.md):
- **1, an authored routine standing in for learning.** The terrain generates its truth; the machine
  is handed the declared periods only and branches every advance over `ℤ/D`. No advance, label or
  key is read from the terrain or from a class's code.
- **2, recitation or an index of contexts.** The retained object is a transport of `|A|` advances,
  the labels and one key a passage, never a context or a count; the code regenerates the passage
  from them.
- **3, text as the exception.** A class is a reading of the receiving ring's digit at its grain; a
  pixel's, a sample's or a motor step's class enters alike. The location reads only the equality of
  occurrences, so no codec's grain enters it, which the relabelling law tests.
- **Lesson 3, a located cause carried unrepaired.** The bank's release (its nearest-lock and
  class-preference causes) is not this loop's consumer: the encoding owner and the repair read the
  located transport directly.
- **6, seen graded as unseen.** The repair passages are fresh keys from their own seeds, damaged
  before the machine reads them; the truth is read only to score.
- **7, bits read as progress.** The code lengths are reported beside the fibre, the relabelling law
  and the repair's fidelity.
- **9, a refusal answered with a larger limit.** Each run has its deadline from a development
  measurement; none is relaunched past it.
- **11, the programming language.** The design is stated as a lift on a helix, its charts (digits
  with carry, CRT residues), loop closure at a grain, a dihedral gauge and a fibre.
