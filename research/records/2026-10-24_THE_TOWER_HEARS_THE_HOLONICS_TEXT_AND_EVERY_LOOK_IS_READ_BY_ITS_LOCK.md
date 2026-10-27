# The tower hears the Holonics text, and every look is read by its lock

Refs #405 #404. Follows [the digit terrain](2026-10-23_ON_A_TERRAIN_OF_INTERACTING_DIGITS_THE_TOWER_COMPUTES_WHAT_IT_NEVER_MET_WHERE_IT_KNOWS_THE_LEVEL.md#every-look-read-by-its-lock-and-the-turn-to-the-holonics-text)
and the mathematics thread's [one face law](2026-10-24_ONE_FACE_LAW_A_FACE_IS_A_CONGRUENCE_SO_LANGUAGE_ARITHMETIC_AND_ANY_OPERATION_ARE_READ_BY_ONE_CONTACT.md)
and its record on cycles (PR #426). Status: [measurement; agent-inferred, October 24], on the host.
October 25: the units step's fixed acceptance is met, the tower's own guess right at 475 of 495
held-out sums' units at 0.623 bits a digit against the foil's 40 and 3.397, with the carriage key
located by loop closure ([the section](#the-machine-locates-the-carriage-key-by-loop-closure)).
October 25, later: the tens step's fixed acceptance is met, the tower's own guess right at 463 of
495 held-out sums' tens and 473 of their units, the held-out text 2.334 bits a byte against the
foil's 2.458 ([the tens](#the-tens-under-the-closures-whole-torsion)). The tower then writes 445 of the 495 held-out
sums itself, whole and right, 219 of the 248 it never met ([the writing](#the-tower-writes-the-sums-itself)).
The differences by a ring of their own: 129 of 268 written right, the acceptance (201) not met; the
tens are what no key carries, and the move the closure lacks is the reflection
([the differences](#the-differences-by-a-ring-of-their-own-and-the-reflection-they-lack)).

## The failure this step works on

Since October 23 every tower heard digit lines alone and every reading asked about digits. Brandon,
October 24: arithmetic is one section of what the machine hears, and the conservation of faces
carries between language, arithmetic and any operation. This step lets the tower hear the public
Holonics text with the digits as one section of four, and reads every section by the same lock.

## The claim fixed first

No completion is claimed. The step measures two things: what each tower writes in each medium from
a held-out opening, shown whole; and whether looking again holds the lock in each medium (the
micro-control's §7: `λ` grows or holds and `F*` falls or holds, `λ` the longest order-consistent
coupling of a look with the true rest and `F* = |H| + |T| − 2λ`). The acceptance the line is held to
from here: looking again holds the lock in every medium, at moments the tower locates itself and not
at a declared byte.

## The terrain

`tools/holonics_text_terrain.py . .local/run/arith100 54016 12000 4000 .local/run/htext1` cuts four
media from the tracked tree: the dated records' prose (`research/records/*.md`, top level), the
Framework's Lean (`lean/Holonics/`), the main library's Rust (`crates/holonics/src/`) and the digit
terrain's lines. Each text medium is its files in path order read at a stride, so the cut spans the
tree. Training takes the files at `k · stride`, the held-out text the files at
`k · stride + stride/2`, so no file is in both. From each file it takes whole lines from the start to
4,000 bytes.

| medium | training | held out |
|---|---|---|
| prose | 54,087 bytes from 16 records | 12,080 from 5 |
| Lean | 54,067 from 18 files | 12,047 from 5 |
| Rust | 54,070 from 15 files | 12,093 from 5 |
| digits | 54,016 (the digit terrain's training lines) | 11,998 (its held-out lines) |

216,240 training bytes and 48,218 held out (`MANIFEST.tsv` pins every piece by its SHA-256). The
training text holds the four media one after another, so each of the eight streams reads mostly one
medium and every section deposits all four together.

## The towers and their runs

Both are the pumped tower (width 64, 64 modes, 256 rectifying contacts, two levels), eight streams of
128 cells, rate `2^(−7)`, the keys `keys_tower.bin`, 12 passes:

- **plain**: `train-pumped-tower`, every byte compared on the plain stream;
- **taught to look again**: `train-looking-pumped-tower` with the moment at `=` and the line end at
  `\n` (four agreeing draws), the [looking tower](2026-10-23_ON_A_TERRAIN_OF_INTERACTING_DIGITS_THE_TOWER_COMPUTES_WHAT_IT_NEVER_MET_WHERE_IT_KNOWS_THE_LEVEL.md#looking-inside-training)
  with the fork comparing the true rest only at the lock's slips.

Projections came from one development pass each: 32.6 s for plain, 59.6 s for the taught tower. The
taught tower ran 12 passes in 682.6 s against 715 s projected (ratio 0.95). Its passes took 53.7 to
58.8 s and its peak resident set was 419 MB. The plain run's first pass took 33,215 ms against its bound of
32,626 ms (1.8% over the single development measurement) and was stopped there, incomplete. It was
continued from the state that pass left, with the bound raised to the largest measured pass. That is
the projection rule's update of its own measurement before the new launch, not a raised limit. The
streams open at rest each pass and a plain run draws no keys, so the continuation is the
uninterrupted run's. Its 11 passes took 29.5 to 33.1 s, 340.6 s in all against 365 s projected (ratio
0.93), with a peak of 158 MB.

Two more towers, the same declaration with the pair contact below in place of the rectifier, trained
on the plain stream like the plain tower:

- **pair**: `train-pair-pumped-tower`, 12 passes in 452.8 s against 483 s projected (12 × 40.3 s,
  the larger of the two development passes, 40,276 ms; ratio 0.94), passes 36.2 to 39.7 s, peak
  173 MB;
- **its linear foil**: `train-pair-linear-pumped-tower`, the same material and opening with the
  bilinear block held at zero. Its ninth pass took 41,080 ms against the 40,276 ms bound and the
  run stopped there, incomplete. It is read at the state that pass left (`STATE.8`), beside the pair
  tower at the same pass (`pair, 9 passes`), and not relaunched.

## What they write

Each tower got a line end and the opening of the first held-out file of each text medium (for Lean,
the module comment after the imports), or the first held-out digit line up to `=`. It wrote 400 bytes
with four agreeing draws a byte (`sample-tower`, keys `keys16k.bin`). Shown whole as written; a run of
trailing spaces is cut and counted.

**Taught to look again.** Prose, after `# THE PENDING DEED CROSSES THE REGISTER APERTURE`:

```text
The comparisonCurrent word constitution and a commation the and the and a conservation cometricalation the and the and and the and and at a constitution and the and the the and the and the and and and a station and the constitution a commatchare and the native and the and the constitution and the constitution and the the the the and the the and constitution and a constitution the and the and the a
```

Lean, after `/-!` and `# Clocks and their readings: elapsed time is a pairing`:

```text
import Holonics.Position: V →ₗ[𝕜] Q) (stransilt : V →ₗ[𝕜] Q) (the carry: &'a make::hnn::{Q (native : V)
```

(then a line end and 282 spaces)

Rust, after `//! **Two clocks: the Farey lock and the convergent near-returns.**` and `//!`:

```text
//! The and the constitution and the and a constitution and the are a comention and the and the the and constitution and the constitution and the and and the and the and the the the and the is the and a steper the constith the and an an the the and the and the constitution and the and the and the constitution and the the the the and the the and the the and the constitution and the and the and the 
```

Digits, after `74-72=`:

```text
2 Q) (Eamparate::{V : V →ₗ[𝕜] Q;
    pub(complex) : V : V →ₗ[𝕜] Q) (the structionCurvatariented_conservation: V : V : V : V (LinearMap<usive_conservation: V →ₗ[𝕜] Q) (strains: &'a chec<Rat>,
    pub(complex>,
```

(then 170 spaces)

**Plain.** Prose:

```text
@[orience) 𝕜] V) : V →ₗ[𝕜] Q) : V →ₗ[𝕜] V) : V Q) : V →ₗ[𝕜] Q) : V →ₗ[𝕜] Q) : V →ₗ[𝕜] Q) : V →ₗ[𝕜] Q) : V →ₗ[𝕜] V) (Q) :=
    }
}

theorem : V →ₗ[𝕜] Q) : V →ₗ[𝕜] Q) : Q →ₗ[𝕜] Q) : V Q) : V →ₗ[𝕜] Q) ∈ invariant: &self, &self, &str) = receivingReceivingReceivingLaw_one_exact Receiving::hnn::hnn::hnn::hnn::hnn::hnn::hnn
```

Lean:

```text
## The complete constition receiving constition and the complete the comparison and the chart only the interned constition constition conservation and constition and the conchandented contact and and and the complete and and the compains and the construction and the complete construction only the complete and are and the the the complete commation and the and the conciance and the complete constit
```

Rust:

```text
# The and are and the the conchandentity and the complete complete complete the changes and the the constition the complete receiver the can and constition and and the constition the the complete and and the compains and the construction and the complete construction only the complete and are and the the the complete commation and the and the conciance and the complete constit
```

Digits:

```text
ort5un V →ₗ[𝕜] V) →ₗ[𝕜] Q) : V Q) : V Q) : V →ₗ[𝕜] Q) : V →ₗ[𝕜] Q) : V →ₗ[𝕜] Q) : V Q) : V Q) : V →ₗ[𝕜] Q) : V →ₗ[𝕜] Q) : V →ₗ[𝕜] Q) : V →ₗ[𝕜] Q) : V →ₗ[𝕜] Q) : V Q) : V Q) :=
    (&trainned_exact Fibre_test →ₗ[𝕜] V) = rel {
        (&transport {
```

(then 76 spaces)

Both babble. Each holds the commonest words of the prose (`the`, `and`, `constitution`,
`conservation`, `complete`) and the commonest Lean signature (`V →ₗ[𝕜] Q)`) and loops on them. The
taught tower stays in the medium it was given, except after `74-72=`, where it writes the true
difference `2` and then Lean. The plain tower leaves the medium: it writes Lean signatures after the
prose heading, and prose after the Lean and Rust module comments (whose own text is markdown). The
two Lean and Rust prose writings share their last 200 bytes word for word: one loop the plain tower
falls into from either opening.

**Pair, 12 passes.** Prose:

```text
\]
variable constitutive scorence orientedArcurrence orientedArcuration.

## The complete and consenty open is the comparison and construction and construction and the complete and construction comparisational construction and consense and construction constitutive constitutive is constitutive is the complete and complete constitutive constitutive constitutive is the comparison and the comparisati
```

Lean:

```text
active complete constitutive and the comparisational construction, the comparison the comparison construction and the complete and conses and the comparison construction and the construction and the complete constitutive and complete and construction constitutive or the construction oriented construction constitutive is the complete instruction and the commutes and consect and construction and com
```

Rust: 400 spaces and nothing else.

Digits, after `74-72=`:

```text
0
    (quotient Fibre) :
    (quotient commutes (LinearMap.ker quotient)

/-- Option<Option<EpochReceivingLawSiteLawStr(),
```

(then 277 spaces)

**Its linear foil, 9 passes.** Prose:

```text
The
import PartialLochRetained chart commandmarks and and conserve receiver the conservation and change classical consed change change conchere the commanding ally the conserval the conservation the change consely conservation and
    partitionReceiving::RestitTich groblar::hnn::ReceivingRetionRetionReading::{Exact : V →ₗ[𝕜] Q) (left (x => &stration,
```

(then 40 spaces)

Lean:

```text
/-- The complete conserver not carry and change and commonic and the clared consely conserfice and
/// is the conservation consely conses and close conserval changes and consely conservation addressere and consely conservation and
    partitionReceiving::RestitSelved::Receiving_conserved_is_constr_consel_index>::Reshen_consed::Rest(),
```

(then 63 spaces)

Rust:

```text
/// The chart and constrous and arior change conserved consely conservation the close is a conservation and
//! and change conservation the conservation and change with noring and change classesse and change conserved commonic and commonic and
import interval chantic change consely distition chantic is changes the classice invary change conservection change consection and



[desserthine = chanded
```

Digits, after `74-72=`:

```text
 [Q.code_admitted::ReloringLockQ.withmodeR2)
        (channervedVec<Comparis::{Ve::Fibre_cending_certive_appored_conseln>,
```

(then 277 spaces)

The pair tower babbles as the others do and loops on one family of words (`construction`,
`constitutive`, `comparison`). After the Rust module comment it writes only spaces, a whitespace
loop, and after `74-72=` it writes `0`, not `2`. The foil switches media within a line (prose into
Rust paths, Lean comments into Rust doc comments) and writes no answer after `74-72=`. The pair
tower at 9 passes writes in the same families (`WRITE_pair8_*`).

Held-out code after the last pass, beside the writing and not its reading (bits a byte): taught
tower prose 3.080, Lean 3.089, Rust 2.755, digits 2.276; plain prose 2.971, Lean 2.975, Rust 2.662,
digits 2.308; pair tower (all four media together) 2.748 after 12 passes and 2.783 after 9, its foil
2.809 after 9.

## The lock where the tower looks again

`read-lines-again` opens each held-out line that holds `=` on the state the true text before it
left. It writes the rest of the line, then looks again up to eight times (the fork carries its look,
the line end and the head again). Each look is read by its lock with the true rest
(`tools/text_looks.py`). Sums over the lines, first look to last, and the lines whose lock held or
grew:

| medium (lines with `=`) | true rest bytes | taught to look again | plain |
|---|---|---|---|
| prose (7) | 242 | λ 55 → 52, F* 328 → 408, held on 2 | λ 33 → 38, F* 342 → 359, held on 4 |
| Lean (24) | 1,469 | λ 275 → 297, F* 1,870 → 2,012, held on 6 | λ 357 → 362, F* 2,032 → 2,010, held on 10 |
| Rust (12) | 491 | λ 143 → 131, F* 729 → 768, held on 6 | λ 136 → 127, F* 737 → 727, held on 6 |
| digits, line met in training (159) | 622 | λ 346 → 346, F* 552 → 553, held on 125 | λ 337 → 342, F* 580 → 572, held on 130 |
| digits, line not met (1,041) | 3,909 | λ 2,162 → 2,190, F* 3,453 → 3,432, held on 846 | λ 2,175 → 2,160, F* 3,539 → 3,561, held on 813 |

The pair towers at `=`, the same lines:

| medium | pair, 12 passes | pair, 9 passes | linear foil, 9 passes |
|---|---|---|---|
| prose | λ 54 → 42, F* 322 → 278, held on 4 | λ 46 → 20, F* 311 → 253, held on 5 | λ 40 → 53, F* 320 → 347, held on 3 |
| Lean | λ 135 → 92, F* 1,540 → 1,550, held on 14 | λ 214 → 124, F* 1,631 → 1,630, held on 8 | λ 315 → 248, F* 1,806 → 1,754, held on 5 |
| Rust | λ 112 → 113, F* 684 → 662, held on 7 | λ 86 → 100, F* 596 → 564, held on 6 | λ 102 → 108, F* 685 → 617, held on 6 |
| digits, met | λ 358 → 369, F* 533 → 506, held on 138 | λ 327 → 330, F* 596 → 588, held on 135 | λ 327 → 323, F* 601 → 613, held on 123 |
| digits, not met | λ 2,198 → 2,249, F* 3,393 → 3,297, held on 889 | λ 2,072 → 2,094, F* 3,713 → 3,658, held on 860 | λ 2,086 → 2,100, F* 3,758 → 3,747, held on 842 |

The pair tower was never taught to look, and at `=` its looking again holds on digits, met and
unmet, by more than the taught tower's (unmet: λ +51 and F* −96 against +28 and −21), and on Rust's
twelve lines. Its foil at the same pass holds on unmet digits by less (λ +14, F* −11) and falls on
met ones.

No held-out text line is met verbatim in training, since the files differ.

- **Digits.** On unmet lines the taught tower's looking again holds the lock in sum (`λ` +28, `F*`
  −21) where the plain tower's falls (`λ` −15, `F*` +22). The taught tower learned to look at `=`, on
  the lines where `=` asks.
- **Prose, Lean and Rust.** Looking again at `=` does not hold. The taught tower's `λ` falls on prose
  and Rust and grows on Lean while its slip grows more. The plain tower holds in sum on Lean only. At
  its first look the taught tower holds 55% of the unmet digit rests in order (2,162 of 3,909 bytes),
  29% of the Rust rests, 23% of the prose and 19% of the Lean.
- **Why.** `=` asks a question on 1,253 held-out digit lines and on 7 prose, 24 Lean and 12 Rust lines
  in about 12 KB of each. A declared moment byte is an arithmetic moment: the tower was taught to look
  where digits ask, and it carried the arithmetic tilt into a terrain where digits are a quarter. By
  the face law, the moment is where a located key fires: a recurrence the passage tree or a copy
  contact locates, a seam the tower locates itself, or a written relation (`=`, `:=`, `:`, `->`, "is").
  The look reads the partner's located face. That moment is medium-neutral, and the next loop places
  the looks there.

## The lock where a located key fires

**Withdrawn, October 26.** The moments in this section were placed by the passage tree's node
lock, an index of exact contexts with a longest-match copier, and `read-lines-located` and the
passage tree were retired in commit `0934a25ff`
([the retirement](2026-10-26_THE_STORES_AND_COPIERS_ARE_RETIRED_AND_THE_PLAIN_TOWER_CODES_THE_SAME_BITS_WITHOUT_THEM.md)).
The measurements stand as reads at those moments only; a moment the tower locates itself is still
owed, and the lookups are not a design to resume.

`read-lines-located` (depth 4) places the moment with no declared byte. The passage tree
(`hnn::passage`) hears the read stream, and a line's moment is its first cell whose four classes up to
it lie in the line and form a context the tree's lock locates at full depth: the same four classes
met earlier in the passage. At least one class of the line must follow. The key is the line's own
expression, in any medium. Depth four is the deepest at which every medium's held-out lines hold
such keys (agent-inferred, counted before the reads): at depth 5 the digit lines fall to 480 of
1,253 and at depth 6 to 76, since a two-digit operand makes longer contexts unique, while prose,
Lean and Rust keep about 90% of their lines through depth 6. A key fires in 163 of 174 prose lines,
145 of 153 Lean, 161 of 180 Rust and 1,007 of 1,253 digit lines. The reads write the first 1,200
digit lines, which hold 957 of those moments: 535 fall on `=`, 333 before it and 89 after it. A text
line's rest from the moment averages 65 to 76 bytes, a digit line's 3.3.

Sums over the lines not met in training, first look to last (`READ_LOCATED.txt`):

| tower | prose (158 lines, 10,771 bytes) | Lean (140, 10,948) | Rust (147, 11,141) | digits (831, 3,555) |
|---|---|---|---|---|
| taught to look again | λ 4,109 → 4,221, F* 13,285 → 13,491 | λ 3,840 → 3,835, F* 13,931 → 13,999 | λ 4,100 → 4,150, F* 14,494 → 14,387 | λ 2,032 → 1,997, F* 2,940 → 3,015 |
| plain | λ 4,098 → 4,166, F* 13,471 → 13,736 | λ 3,705 → 3,709, F* 13,696 → 13,828 | λ 4,177 → 4,154, F* 14,335 → 14,476 | λ 1,999 → 1,992, F* 3,124 → 3,144 |
| pair, 12 passes | λ 4,047 → 3,815, F* 13,456 → 13,295 | λ 3,559 → 3,279, F* 13,759 → 13,765 | λ 4,002 → 3,959, F* 14,664 → 14,848 | λ 2,047 → 2,075, F* 3,002 → 2,939 |
| pair, 9 passes | λ 4,131 → 4,130, F* 13,090 → 13,267 | λ 3,633 → 3,372, F* 13,218 → 13,099 | λ 4,117 → 4,176, F* 14,279 → 14,233 | λ 1,964 → 1,968, F* 3,214 → 3,199 |
| linear foil, 9 passes | λ 3,972 → 3,982, F* 13,596 → 13,453 | λ 3,744 → 3,494, F* 14,218 → 13,740 | λ 3,277 → 2,820, F* 14,922 → 14,677 | λ 1,970 → 1,949, F* 3,257 → 3,300 |

- **The text media.** Looking again holds in sum in three of fifteen cells: the taught tower on
  Rust, the pair tower at 9 passes on Rust, the foil on prose. Line by line it holds or grows on 31
  to 63% of the lines in a cell (prose 80 to 93 of 158, Lean 55 to 73 of 140, Rust 45 to 93 of
  147). Two looks in a row agree on 11 to 39 lines of 145 to 163. Each look of a long rest is
  another babble, and its order agreement with the truth wanders from look to look.
- **Digits.** The pair tower holds in sum at both passes, and per line it holds or grows on 691 of
  831 lines at 12 passes (the plain tower 645, the taught 623, the foil 656). The taught tower,
  which holds at `=`, falls here: its looking was learned at `=`, and 422 of the 957 digit moments
  fall before or after it.
- **What the first look holds.** At a located moment the first look holds 29 to 38% of a text
  line's rest in order (λ over the rest's bytes), and 55 to 58% of a digit line's.

The acceptance fixed above is not met: looking again does not hold in every medium. The pair
contact is the first law under which it holds on digits at both kinds of moment without being
taught to look. The next loop's subject, by its measurement: on prose, Lean and Rust, two looks in a
row agree on about one line in ten, so a look does not yet settle. The moment here is the passage
tree's, an exterior receiver hearing the read; a moment the tower locates itself is still owed.

## A reading bug, found and repaired

`read-lines` wrote each look as characters, one per byte. Each byte at or above `0x80` became two
UTF-8 bytes, and the lock was read on those bytes. A look holding `𝕜` or `→` was therefore compared
garbled, and so was every Lean and Rust look. The looks are now bytes. Every text field of
`LINES.tsv` and `LOOKS.tsv` is written escaped (`escape_ascii`, with `|` as `\x7c`), so a field holds
no tab or `|` and reads back to its exact bytes (`codecs.escape_decode`). The two towers' looks were
read again with the repaired binary: the same looks, the corrected locks above. None of the digit
terrain's 30 `LOOKS` receipts holds a byte at or above `0x80`, so its readings stand. Of these runs,
only the plain tower's digit looks held such bytes, on three lines, and its digit sums above are the
corrected ones.

## The pair contact, built

The face law reads every section through one pair contact `W(x̄ ⊗ ȳ)`, `x̄ = (x, 1)`, and the
mathematics thread approved its mode form for the tower. `hnn::tower` now carries it as a contact
law ([`ContactLaw`](../../crates/holonics/src/hnn/tower.rs)):

```text
Pair         v = (W_a r̂ + b_a) ⊙ (W_b r̂ + b_b)
             δ(W_a r̂ + b_a) = δv ⊙ (W_b r̂ + b_b),   δ(W_b r̂ + b_b) = δv ⊙ (W_a r̂ + b_a)
PairLinear   v = (W_a r̂ + b_a) b_b + b_a (W_b r̂)          the bilinear block held at zero
Rectifying   v = max(W₁ r̂ + b₁, 0)
```

The second drive opens at `W_b = 0`, `b_b = 1`, so the contact opens one-sided, with no kink, and its
bilinear block is learned from there. The first drive is founded as the rectifier's. The product is
taken on `2^(−32)` and released to the face's `2^(−16)`. The second drive's material and bias follow
every other family in the layout, so a rectifying tower's layout and text are unchanged. The text
head gains `pair` or `pair-linear`. Tested (`cargo test -p holonics --lib hnn::tower::`, 27 passed):

- both laws restore exactly from their text;
- the pair contact and its foil code every passage alike at founding and differ once `W_b` moves;
- each law's covector matches the code difference (the pair ungated and gated, the foil ungated,
  with the second drive's families among those read).

`train-pair-pumped-tower` and `train-pair-linear-pumped-tower` train it; its runs, writing and
locks are above, beside the two rectifying towers as their foil. Tested with the rungs below, 28
passed.

From the mathematics thread's cycles record (PR #426), the reading the pair contact owes:

- **Where the bilinear weight sits** (read in the next section). Report held×fast against
  fast×fast, by the founded `|λ|` of the modes each drive reads. This is the slip's Hodge split read per section:
  - exact: absorbed by rereading the faces, the one-sided blocks;
  - coexact: a local curl, fast×fast;
  - harmonic: a cycle no local cell bounds, held×fast.

  The harmonic part is what retention keeps, and it is never collapsed to a score.
- **The lap beside the phase.** A mode keeps its phase and modulus and counts no laps, so a sum's
  carry (the crossing of the summed phase) is not yet carried as a winding.
- **Two reports apart.** When the contact's material is deposited, a face changing with no new
  input (`Ċm`) is reported apart from one changing under new input (`Cṁ`).

## Where the pair tower's bilinear weight sits

`read-tower-pair` reads [`Tower::bilinear_rungs`](../../crates/holonics/src/hnn/tower.rs): each
level's two drives read back onto the modes' faces, `A = W_a [C_re, −C_im]` and `B = W_b [C_re,
−C_im]`, and the bilinear block's weight on the founded memory rungs of the two modes,
`E_(s,s′) = Σ_o (Σ_(k on s) |A_(o,k)|²)(Σ_(k′ on s′) |B_(o,k′)|²)`. The ladder has eight rungs,
founded at `|λ| = 1 − 2^(−s−1)`, a memory of 2 to 256 cells. Held is the upper four rungs and fast
the lower four (the ladder's halves, agent-inferred). In thousandths of each level's whole:

| tower | level 1: held×fast, fast×fast, held×held | level 2 |
|---|---|---|
| pair, 12 passes | 483, 168, 350 | 498, 257, 245 |
| pair, 9 passes | 479, 159, 363 | 499, 249, 252 |
| linear foil, 9 passes | 463, 132, 405 | 488, 177, 336 |
| equal weight on every rung pair | 500, 250, 250 | 500, 250, 250 |

At founding `W_b = 0`, so every entry is zero: all of this weight was learned. The foil never takes
the product, so its row is the placement the two drives' material reaches without it. On the first
level both lean toward the held rungs, the foil more. The product, taken, moves weight from
held×held toward the fast rungs at both levels (second level fast×fast 249 against the foil's 177 at
the same pass). The held×fast part, the harmonic part of the cycles record's split, stays near its
equal-weight share (463 to 499 of 500) in every tower. So the product's weight does not concentrate
on the harmonic part. Where it moves, it moves toward the coexact (fast×fast) block. Full matrices
in `PAIR_RUNGS_*.txt`.

Still owed from that record: the lap count beside the phase, and the report of `Ċm` apart from `Cṁ`
when the contact's material is deposited.

## The writing law, audited

The writing above reads as more repetitive than the GSM8K towers' of October 23, and it writes almost
no integers. The audit (`AUDIT_WRITE_*`) found three things.

- **The release law changed, not the machine.** Every October 23 writing was released at one draw
  or at two agreeing draws. The writing above used four agreeing draws, the face raised to the fourth
  power, which piles the weight on the commonest next byte. The same states, prompts and keys,
  counted over written words (distinct words; the commonest word's share):

  | tower, prompt | one draw | two agreeing | four agreeing |
  |---|---|---|---|
  | taught to look, prose | 84%; "the" 7% | 58%; "the" 20% | 18%; "and" 35% |
  | taught to look, Rust | 83%; "the" 13% | 49%; "the" 22% | 12%; "the" 45% |
  | pair, prose | 92%; "quotient" 11% | 57%; "the" 19% | 35%; "and" 20% |
  | pair, Lean | 93%; "is" 5% | 60%; "the" 15% | 31%; "and" 23% |

- **The integers are hidden by the bare prompt.** After `74-72=` from rest the tower cannot tell
  it is in the arithmetic section, since `=` also opens Rust and Lean lines. With the twelve held-out
  digit lines that fit the 128-byte prompt budget before it (`PROMPT_arithmetic_ctx.txt`), all three
  towers write whole lines of arithmetic at one, two and four agreeing draws. The taught tower writes
  digit lines at two agreeing draws even from the bare prompt.
- **No code break.** arith24 (with the pair contact) writes byte for byte what arith22 wrote from the
  taught tower's state on all four prompts.

What stays wrong: at one draw the text varies but crosses media inside a line, so the tower does not
hold which medium it is in. It heard 54 KB of each medium, against 3.5 MB for the GSM8K towers.
(Eight times the text did not change this; see the next section.)

Free writing is released at one draw (the face itself) and at two agreeing draws, both shown, and not
at four (agent-inferred: the fourth power reads the single likeliest answer, which suits a look at
one question and the lock that reads it, not writing).

## Eight times the text

The audit's reading was that the tower crosses media because it heard little of each. To test it,
the terrain is cut again with only its size changed:
`tools/holonics_text_terrain.py . .local/run/arith100 524288 12000 4000 .local/run/htext2`. That
gives 524,288 bytes of each text medium (prose from 135 records, Lean from 146 files, Rust from 135
files) and the digit terrain's 216,131 training bytes, so 1,789,116 training bytes against htext1's
216,240. The held-out text is 48,031 bytes from files that neither cut trains on. The new Lean
prompt is `BIG_PROMPT_lean.txt`, because the old one's file is now in training. The pair tower is
trained from rest with its declaration unchanged: width 64, 64 modes, 256 contacts, 2 levels,
8 streams, sections of 128, 4 passes, rate `2^(−7)`.

Training (`BIG_TRAIN.txt`):
- Held-out bits a byte by pass: 2.791, 2.645, 2.585, 2.543. Training: 2.767, 2.396, 2.299, 2.220.
- The gap at the last pass is 0.32 bits a byte, against 0.49 for the htext1 pair tower (2.255 and
  2.748).
- Held out by medium at the end: prose 3.159, Lean 2.490, Rust 2.208, digits 2.315.

**The writing still leaves its medium.** At one draw the Lean prompt opens with prose, passes a Lean
doc comment (`/--`) and reaches a Rust one (`//!`) by its ninth line (`BIG_WRITE_big_lean_a1.txt`):

```text
Rating is by an patherting population, come.

[mean traces them))inu (Hamal stric/target)  -> heure)).prepares
index-boostingPairied togen

/-- behing is side.

An |Be is other grounds its colcatime bankrithlies locked read residual  
//! `knqul ::them, sime: Retained; 0 wracheve returned-loethout, by every twithing by onuse them strred tin //!= then eresaanance /// Twise bits. Decise. Population 
```

At two agreeing draws the Rust prompt writes code shaped like Rust with Lean's `:=` inside it
(`BIG_WRITE_big_rust_a2.txt`):

```text
//! [emitted + companion.speented_trace = ObservedFace = verserietent (hamiltonian.closes)
    }

    residual :=
  residual > 0 + boundid (Selection, not law : Oncgenceless) -> the preserver (here : A) :
    residual :=
              (E) :
        residual()
    pub navigator: Result<Self)) :
    determinants {
        current {
        decides[reson] (searched (held.clone());
        &self) -> &
```

The prose prompt, a record's heading and a blank line, is answered by `#[determily)` at two draws:
after the blank line the tower writes Rust's attribute opener. With twelve held-out digit lines
before it, the two-draw writing stays in digits for all 400 bytes: it answers the prompt's `74-72=`
with `1`, then writes 40 whole equation lines (`BIG_WRITE_big_arithmetic_ctx_a2.txt`). Their answers
have the right number of digits, and none is right (`85*90=6115`, `94+31=117`, `13+97=109`).

**The lock on the same unseen text.** Both pair towers look at the located moment on htext2's
held-out lines, which neither heard (`BIG_LOCATED_LOOKS_<tower>_<medium>.tsv`,
`BIG_READ_LOCATED.txt`). Met and unmet lines are summed; `ΣT` is the true rests' bytes.

| medium, lines, `ΣT` | tower | `Σλ` first → last | `ΣF*` first → last | held or grew / fell | last `λ / ΣT` |
|---|---|---|---|---|---|
| digits, 957, 4,103 | eight times the text | 2,289 → 2,298 | 3,630 → 3,578 | 766 / 191 | 56.0% |
| | htext1 pair | 2,367 → 2,400 | 3,460 → 3,389 | 795 / 162 | 58.5% |
| prose, 164, 10,696 | eight times the text | 3,700 → 3,732 | 13,532 → 13,588 | 79 / 85 | 34.9% |
| | htext1 pair | 3,693 → 3,692 | 14,099 → 13,937 | 89 / 75 | 34.5% |
| Lean, 152, 10,998 | eight times the text | 3,866 → 3,894 | 13,334 → 13,176 | 65 / 87 | 35.4% |
| | htext1 pair | 3,647 → 3,436 | 13,447 → 13,470 | 65 / 87 | 31.2% |
| Rust, 204, 11,034 | eight times the text | 3,441 → 2,938 | 14,016 → 14,069 | 68 / 136 | 26.6% |
| | htext1 pair | 3,759 → 3,759 | 15,182 → 15,047 | 151 / 53 | 34.1% |

The larger text raises the first look on prose and Lean, where `λ` is higher and `F*` lower. On
Lean the larger tower's looks hold or grow over the whole text, where the smaller one's fall. On
digits the two are close and the smaller is ahead. On Rust the larger tower's looking again falls:
`Σλ` drops by 503, the looks shorten from 9,864 to 8,911 bytes, and 136 of 204 lines fall. The
looks there move out of comment text into code: line 2's later looks write `&self.res…` after a
`//!` head.

So the medium crossing does not come from how little the tower heard. Eight times the text closes
some of the gap between training and held-out bits, and lifts the lock on two media. The writing
still leaves its medium within a line or two, and on Rust looking again leaves it too. The next loop
asks whether the crossing follows the fit (agent-inferred: held-out bits still fall 0.04 a pass, so
four more passes from this state is the one change that tells fit from law).

### One more pass

The four more passes are projected from the largest measured pass, 317,155 ms, so 1,268.6 s, with a
deadline of 1,270 s. The first launch was stopped by hand: a workspace check run beside it on the
four cores slowed it past its bound (`RUNS.tsv`). Relaunched unchanged with nothing beside it, pass 0
ran 332,250 ms, 1.048 of its bound, and the run stopped there on evidence (`CONT_TRAIN.txt`). It is
read at the state it reached, five passes in all, and is incomplete as a test of four more passes.

- Held-out bits a byte are 2.511, and training bits 2.171. By medium: prose 3.117, Lean 2.431,
  Rust 2.172, digits 2.324.
- The writing still crosses media (`CONT_WRITE_<prompt>_a<draws>.txt`). At one draw, the prose
  prompt writes a Rust signature (`pub fn determinantTrace(&self) -> Source`) and then a Lean
  `def` by its seventh line. With digit context, two draws write 41 whole equations, none right.
- The lock on the same held-out lines (`CONT_LOCATED_LOOKS_<medium>.tsv`, `CONT_READ_LOCATED.txt`):

  | medium | `Σλ` first → last | `ΣF*` first → last | held or grew / fell | last `λ / ΣT` |
  |---|---|---|---|---|
  | digits | 2,281 → 2,291 | 3,663 → 3,613 | 786 / 171 | 55.8% |
  | prose | 4,028 → 3,921 | 13,597 → 13,390 | 86 / 78 | 36.7% |
  | Lean | 3,935 → 3,888 | 14,077 → 13,518 | 73 / 79 | 35.4% |
  | Rust | 2,808 → 1,926 | 15,771 → 16,194 | 99 / 105 | 17.5% |

The fifth pass lowers the held-out code and raises prose's first look. It does not hold the writing
in its medium. On Rust the lock falls further: the first look holds 633 fewer bytes in order than
after four passes, and looking again then loses 882, with looks that settle early on rests that do
not fit (136 of 204 lines agree twice). Fitting the text more closely is not what holds a medium,
so the next loop changes the learning step itself, not the amount of training: the difference the
tower can bridge from where it stands deposits, and the remainder it cannot bridge is kept as tension
that founds a new contact (being derived with the mathematics thread).

## The tension the text leaves

The mathematics thread's law for the learning step
([the effective-tension record](2026-10-24_WHAT_A_CONTACT_CANNOT_BRIDGE_IS_ITS_EFFECTIVE_TENSION_AND_THE_TENSION_FOUNDS_THE_FACE_THAT_CARRIES_IT.md),
PR #427) splits what the readout misses into the part a move of its material can still close and
the part no material reading its face closes. This section reads that split on the tower of the last
section (`hbig2_pair/STATE.0`, SHA-256 `56c6cb4a…`), before the step is changed.

**What is read** [agent-inferred, October 24]. `Tower::read_tension` steps the frozen tower and hands
each cell's `TensionCell` to the receiver: the face the readout reads (`top`), the covector
`dz = p̂ − [· = u]` (one function, `covector`, now shared with the reverse scan), the top level's
quadrature `Im(C h)` on the read's own ratio, and the face the top level read from below. The unit
test `the_tension_readings_bridge_is_the_readouts_covector` checks that `B = Σ dz (top, 1)ᵀ` is
exactly the readout's covector the reverse scan forms. `read-tower-tension` sums the joint Gram of
`(top, 1, quadrature, below, foil, region, dz)` exactly in `i128`, 517 coordinates, per medium, at
line starts (the cell read just after a line feed, pooled over the media) and over the whole. It
then eliminates the face block by fraction-free elimination in `BigInt`, so every reading is a ratio
of exact integers:
- `tr T` per cell is the Brier score of the faces;
- the tension is `tr S`, the readout's remaining bridge `tr T − tr S`;
- each candidate face's drop is the part of `tr S` its own unread part carries.

Two references sit beside the tower's own faces. The **foil** is the quadrature read half a stream
away in the same stream: the same medium's face, not aligned with the cell's comparison, so its
drop is what a face of that width removes by chance. The **region** is the exterior reader's medium
label, read only here: it measures how much tension a face that carried the medium perfectly would
bridge. Nothing in the tower reads it.

The training text is read at one constitution, as the law asks (the frozen tower, 1,789,108 cells,
eight streams). Its region file is cut from the terrain's manifest, each piece checked against its
SHA-256 (`train.roles`, `2dd6ef8c…`).

| text | part | cells | Brier `tr T` | tension share | readout bridge | quadrature | below | foil | region |
|---|---|---|---|---|---|---|---|---|---|
| training | prose | 524,313 | 0.614 | 98.8% | 11.7‰ | 3.7‰ | 3.9‰ | 0.14‰ | – |
| training | Lean | 524,309 | 0.579 | 98.9% | 11.2‰ | 4.1‰ | 4.7‰ | 0.15‰ | – |
| training | Rust | 524,355 | 0.521 | 98.5% | 14.5‰ | 5.7‰ | 6.6‰ | 0.14‰ | – |
| training | digits | 216,131 | 0.653 | 98.5% | 14.8‰ | 2.8‰ | 4.0‰ | 0.31‰ | – |
| training | line starts | 54,143 | 0.765 | 96.4% | 36.5‰ | 10.4‰ | 11.1‰ | 5.0‰ | 32.3‰ |
| training | all | 1,789,108 | 0.581 | 99.2% | 8.3‰ | 2.7‰ | 3.0‰ | 0.11‰ | 0.24‰ |
| held out | prose | 12,009 | 0.708 | 97.3% | 27.1‰ | 13.3‰ | 13.1‰ | 5.4‰ | – |
| held out | Lean | 12,009 | 0.591 | 96.7% | 32.9‰ | 21.3‰ | 22.2‰ | 5.7‰ | – |
| held out | Rust | 12,008 | 0.530 | 97.7% | 23.4‰ | 14.7‰ | 14.3‰ | 5.6‰ | – |
| held out | digits | 11,997 | 0.655 | 98.3% | 17.2‰ | 8.3‰ | 8.6‰ | 4.8‰ | – |
| held out | line starts | 1,870 | 0.843 | 93.1% | 69.1‰ | 40.6‰ | 41.1‰ | 36.9‰ | 39.8‰ |
| held out | all | 48,023 | 0.621 | 98.9% | 10.7‰ | 5.4‰ | 5.7‰ | 1.5‰ | 0.46‰ |

The readout bridge is in thousandths of `tr T`; each candidate's drop is in thousandths of the
tension `tr S`. Inside one medium the region is constant and carries nothing. Reading the quadrature
and the face below together removes 4.8‰ of the tension on the whole training text and 10.0‰ on the
held-out text. The four-pass tower (`hbig_pair/STATE`) reads close to these on the held-out text: Brier 0.628 over
the whole against 0.621, and every bridge and drop within 6‰ of the table's
(`TENSION_DEV_big.txt`).

**The classes in tension** (`TENSION_OPPOSED` lines, the most negative `S_ab` with its correlation).
Every medium's strongest pair is a line feed against a space (−0.28 to −0.30 on the training text):
whether the line ends. Then come the vowels against each other (`e|i`, `a|e`, `a|o`, `e|o`, −0.14 to
−0.20): the face knows a vowel comes and not which. In the digits the operators oppose (`*|+` −0.57,
`*|-` and `+|-` −0.38), and so do neighbouring digits (`1|2`, `4|5`, `2|3`, −0.13 to −0.17): read as
the face holding a digit's size and not the digit [agent-inferred]. At line starts the strongest pair is a space against `/`
(−0.24 on the training text, −0.44 held out): an indented line against a comment line.

**What it says.**
- The readout is close to the best any material reading its face can do: at most 1.5% of the
  training text's error is still bridgeable by moving it. The other 98.5 to 99.2% is tension.
- The tower's own unread faces carry little of the tension. The quadrature and the face below each
  carry 3 to 7 thousandths of it on the training text, twenty to forty times the foil, and 8 to 22
  thousandths held out, two to four times the foil. A contact founded on them, as the law states
  it, would close under 1% of what the readout misses.
- On true text the face already carries the medium. The medium label adds 0.24‰ over the whole. At
  line starts it adds 32‰, three times what each of the tower's own faces adds there, with 3
  coordinates against their 64. There the strongest fork is a space against `/`, an indented line of
  code against a comment line.
- The training text's tension is nearly the held-out text's (Brier 0.581 against 0.621). The tower
  fits the text it heard barely better than text it never heard in this reading, which agrees with
  eight times the text changing nothing [agent-inferred].

So the founding step cannot draw on the faces the tower has now: the tension is in differences none
of them holds (which vowel, which digit, whether the line ends). And since the face holds the medium
while it reads true text, the medium jumps in its writing arise where it reads its own releases,
which this reading of true text cannot see [agent-inferred]. The next loop founds a face the tension
itself chooses and checks it by code length on the held-out text.

## The floor under the tension

`tr S` mixes two things: what no face could ever bridge (the text's own floor, which a predictor
holding the true conditional still pays) and what a face the tower does not have yet could bridge.
The mathematics thread split them with two exterior references, never faces of the machine
([its record](2026-10-24_WHAT_A_CONTACT_CANNOT_BRIDGE_IS_ITS_EFFECTIVE_TENSION_AND_THE_TENSION_FOUNDS_THE_FACE_THAT_CARRIES_IT.md),
§7): a count model of the last bytes, and the linear face of the last bytes' encodings. If the two
agree, a new mode suffices; if the count model knows much more, the missing difference is a
conjunction, which only a pair contact carries.

**What is read** (`read-tower-floor`, [agent-inferred, October 24]).
- The count model is Witten–Bell interpolation of the bytes that followed each context of up to six
  bytes in the training text, down to the byte counts, exact on `2^(−48)` and read on `2^(−24)`. On
  the held-out text it counts the training text. On the training text it counts it with the cell's
  own arrival deleted, so both of its readings are out of sample.
- The linear reference is `E(u_t), E(u_(t−1)), E(u_(t−2))`, the tower's own encodings of the last
  three bytes (`Tower::encoding`, the face the bottom level reads), eliminated after the face one
  block at a time. Beside them: the order-3 count model's prediction as a candidate face, and the
  foil, the encoding of a byte half a stream away.
- The drops are read on the training text. Its 1.8 million cells keep 64 coordinates from removing
  more than a ten-thousandth of the tension by chance; the held-out text's twelve thousand cells a
  medium would let a few hundred coordinates remove about 2% by chance, the size of the signal.
- The covector and the count model are read on the 171 classes that arrive in the training text.
  The others carry under a thousandth of the Brier score.

**The first split: the tower against the count model, held out.** Brier per cell, the count model
at orders 3 to 6 (orders 0 to 2 are in the receipt):

| part | tower | order 3 | order 4 | order 5 | order 6 |
|---|---|---|---|---|---|
| prose | 0.708 | 0.696 | 0.647 | 0.636 | 0.646 |
| Lean | 0.591 | 0.591 | 0.511 | 0.475 | 0.460 |
| Rust | 0.530 | 0.565 | 0.491 | 0.467 | 0.459 |
| digits | 0.655 | 0.735 | 0.734 | 0.748 | 0.743 |
| line starts | 0.843 | 0.836 | 0.844 | 0.876 | 0.951 |
| all | 0.621 | 0.647 | 0.596 | 0.581 | 0.577 |

On the training text with deleted counts the same pattern holds: 0.581 for the tower over all
against 0.496 at order 6; prose 0.614 against 0.498, Lean 0.579 against 0.430, Rust 0.521 against
0.408; digits 0.653 against at best 0.735 (order 3); line starts 0.765 against at best 0.753
(order 4).

**The second split: the linear face against the conjunction, on the training text.** Drops in
thousandths of the tension (`tr S` = 0.576 per cell, 991.7‰ of the Brier score):

| face read after the tower's face | drop (‰ of the tension) |
|---|---|
| foil, the encoding of a byte half a stream away | 0.07 |
| `E(u_t)` | 3.99 |
| then `E(u_(t−1))` | 2.15 |
| then `E(u_(t−2))` | 1.04 |
| the three encodings together | 7.18 |
| the order-3 count model's prediction alone | 29.93 |
| the count model after the three encodings | stopped at the deadline; at least 22.75 |

The last step did not finish inside its deadline (below). Reading a face after others removes at
least what it removes alone, less what the others removed, so the conjunction past the linear face
removes at least `29.93 − 7.18 = 22.75`.

**What it says.**
- In prose, Lean and Rust the tower's error is not the text's floor. A count of the last five or
  six bytes leaves 0.07 to 0.13 less Brier per cell on text neither has seen: 10% of the tower's
  error in prose, 22% in Lean, 13% in Rust.
- That missing part is a conjunction of recent bytes. The count model of the last three bytes
  carries four times what the linear face of the same three bytes' encodings carries. A new mode
  driven by the encodings, which is linear in them, would close little of it. A pair face over
  recent encodings is what the founding should build.
- In the digits and at line starts the tension is not in the last bytes. The tower already beats
  every count order on the digits (0.655 against 0.734 at best), and at line starts the two are
  level. What decides a digit lies further back (the operands), and what decides how a line starts
  lies in the lines before it. This is what the mathematics thread predicted: the operands'
  cheap-ring faces for digits, the newline's clock for line ends [agent-inferred; the founding test
  decides each].

The next loop founds a pair face on the last bytes' encodings, chosen by the tension (the leading
directions of the pool of their products, the mathematics thread's reduced-rank rule), and checks
it by code length on the held-out text.

**The run.** The projection came from a 4,792-cell slice, whose text has 106 classes. The full
training text has 171, so the count block was 1.6 times as wide as projected and its eliminations
ran past the projection, while the read was faster (224 s against 336). The run stopped at its
600-second deadline in the last step and was not run again with a larger one; that step's reading
is the bound above.

## Founding pair faces on the tension

The floor says the missing part is a conjunction of the last bytes. The mathematics thread's
founding at scale builds faces of that kind from one pass: a face that is a function of the pair
of bytes `p = (u_(t−1), u_t)` is read from a table of the pairs alone, each pair keeping its cells
`n_p`, `τ_p = Σ t` and `φ_p = Σ f̄`.

**What is read** (`found-tower-pair`, [agent-inferred with the mathematics thread, October 24]).
- The ceiling is the table itself, every pair its own coordinate: the most any face of the last two
  bytes could carry, against its chance level `(P − 1)/N`. Each pair's mean is subtracted rounded to
  nearest, so each entry is within half the number of pairs of its exact value (6,330 halves in
  entries of about `2^53`).
- Each rank founds one coordinate `c_p = (aᵀx̂)(bᵀŷ)`, the product of a read of the current byte's
  encoding and a read of the byte before's, each with the unit, so either byte's linear face is
  among the candidates. With one factor held, the other is the leading direction of the pool
  (`w = Q⁻¹Mᵀv`, `v ← Mw` on released copies of the reduced moments, only directions being read).
  The factors alternate; each step's coordinate is read exactly from the table, and the rank stops
  when a step gains less than `2^(−15)` of its drop. The coordinate then joins the face and the next
  rank is founded on what remains.
- The readout fitted on the training text, with the founded coordinates and without, is read on
  the held-out text.

**What it reads.** On the training text (1,789,108 cells, 6,330 pairs, 171 arriving classes) the
tension is 0.576 per cell, 991.7‰ of the Brier score, the floor reading's value.

| face read after the tower's face | drop (‰ of the tension) |
|---|---|
| the pair table, every pair a coordinate (the ceiling) | 40.72 |
| its chance level, `(P − 1)/N` | 3.54 |
| founded rank 1 | 1.18 |
| rank 2 | 0.72 |
| rank 3 | 0.83 |
| rank 4 | 0.74 |
| the four ranks | 3.46 |

On the held-out text the four ranks carry what they carry on the training text: they remove 2.4‰
of the residual the face's own readout leaves (3.8‰ in prose, 2.8‰ in Lean, 2.9‰ in Rust, none in
the digits). The face's own readout, refitted, moves the held-out Brier score by at most 0.006 per
cell in any medium (0.621 to 0.619 over all).

Each rank is a conjunction a reader can name (its pairs with the most weight, the classes whose
tension it removes most):
- rank 1: after ` p`, `ch`, ` m`, ` h`, `mp`, whether `a` or `e` follows (13.5‰ of `a`'s tension,
  7.3‰ of `e`'s);
- rank 2: after `}`+newline, `)`+newline, `ce`, `co`, `re`, `on`, whether a space or a newline
  follows (8.1‰ of the space's tension);
- rank 3: after `iv`, `in`, ` d`, `th`, whether `e` or `o` follows;
- rank 4: after `ha`, `ra`, ` a`, `ea`, whether `n`, `d` or `t` follows (12.9‰ of `n`'s).

**What it says.**
- The last two bytes carry 37‰ of the tension above chance; the deleted count model of up to six
  bytes carried 29.93‰ as one face. The pair table is fitted in sample (its chance level
  subtracted) and the count model is read out of sample, so neither is exact; both say the last
  bytes hold a few hundredths of the tension that the tower's face does not.
- A single product of two encoding reads is a thin face: four of them carry 3.5‰, a tenth of what
  the pairs could carry. What they carry is real (it holds on the held-out text), and each is a
  readable next-byte contrast.

**How many coordinates the pairs need.** The pair table's class matrix `S − S_w` (its trace is the
ceiling) says it. Its leading eigenvalue is the most one coordinate of the pair could carry, and
the sum of its leading `k` the most `k` could. The directions are located by power steps on a
released copy, each found direction projected out of the later ones, and the sum over the span of
the first `k` is read exactly, `tr((VᵀV)⁻¹VᵀEV)`, so each sum is at least what the leading `k`
carry. In thousandths of the tension, fitted in sample (the chance level, 3.54‰, is spread over
all 171 directions):

| leading coordinates | 1 | 2 | 4 | 8 | 16 | 32 | all 171 |
|---|---|---|---|---|---|---|---|
| the most the pair could carry | 3.70 | 6.94 | 11.91 | 18.48 | 25.63 | 31.93 | 40.72 |
| founded products of two reads | 1.18 | 1.90 | 3.46 | | | | |

The leading directions are contrasts among the next byte's letters: `e` against a space, `a` and
`o`; a space against a newline and the vowels; `a` against `o`; then `o` against `r` and `t`,
`r` against `i` and `s`, `n` against `t` and `s`.

So both limits hold at once. One product of two reads carries about a third of what the best single
coordinate of the pair carries (1.18 against 3.70; four against four, 3.46 against 11.91). And the
conjunction is spread over many next-byte directions: the eigenvalues fall slowly (3.70, 3.24,
2.81, 2.16, 1.91, 1.74, 1.57, 1.35, …), eight coordinates carry under half the ceiling and
thirty-two carry four fifths. A pair face for text is a block of some tens of coordinates, each a
bilinear form of the two encodings richer than one product of reads: the pair contact
`W(x̄⊗ȳ)` of the [one face law](2026-10-24_ONE_FACE_LAW_A_FACE_IS_A_CONGRUENCE_SO_LANGUAGE_ARITHMETIC_AND_ANY_OPERATION_ARE_READ_BY_ONE_CONTACT.md), founded with its rank read from this spectrum
[agent-inferred; the next loop founds it and reads it held out].

**The run.** The slice (4,800 bytes as the training text, the held-out text whole, two ranks) ran
in 57.9 s; its readout overfits, which the slice was not meant to test (the held-out residual rises
33‰ and 82‰). The projection for the full text, from the slice's largest units, was 440 s (the pass
98 s, the ceiling 5 s, at most 80 half-steps of 1.05 s a rank); the deadline was 540 s. The run took
170.5 s at a peak of 132 MB: the pass took 91.7 s as projected, and a half-step about 0.5 s. The
spectrum was added after it and checked on the slice (5.8 s); the whole run again, projected at
186 s from the run before with a 240 s deadline, took 178.5 s at a peak of 236 MB, with every
founding and held-out reading identical to the first run's.

## A block of full pair forms

The spectrum says a pair face for text is a block of some tens of coordinates, each a full
bilinear form of the two encodings. This step founds that block and reads it held out
(`found-tower-pair-block`, [agent-inferred with the mathematics thread, October 24]).

**What is read.**
- The pool is every product of a coordinate of the current byte's encoding with one of the byte
  before's, `z_p = x̂_cur ⊗ ŷ_prev`, each with its unit (`x̂ = (E(u), 2^16)`; the start of a stream
  has `ŷ = (0, 2^16)`): 65 × 65 = 4,225 coordinates. A full pair form `W(x̄⊗ȳ)` is one read of the
  pool, `c_p = Σ_ij W_ij x̂_i ŷ_j`. The table of pairs is its ceiling, and one product of two reads
  (the founded ranks above) is its rank-one case.
- The block is founded as a reduced-rank read of the tension on the pool after the face. With `M`
  the pool's cross moment with the covector and `Q` its Gram, both after the face, the class matrix
  `N = M Q⁻¹ Mᵀ` (171 × 171) holds what the whole pool could carry. Its leading `k` eigen-directions
  `v` hold the most `k` coordinates could, and each direction's form is `W_v = Q⁻¹Mᵀv`. The face and
  the pool are eliminated together, so each form is read after the face.
- The elimination runs at a declared grain. Each coordinate is scaled by a power of two so its
  diagonal is below `2^50`, and the covector by one power of two so its total is below `2^50`. The
  factorization is `LDLᵀ`: the face's coordinates first, then the pool's, each step pivoting on the
  largest remaining diagonal. A set stops when that diagonal falls below `2^20`, so a coordinate
  within `2^−30` of its predecessors' span is passed over. `L` carries 46 fractional bits, each term
  is rounded on its own and the sums are exact, so the factorization is the same however the cores
  share the sums. The forms are back-substituted exactly, in integers of any width, and released to
  62 bits.
- Each form is then a table over every pair of the alphabet: the form's resident face, released by
  its largest value on the training pairs to `2^16`. The readout is fitted exactly (Bareiss, as for
  every face) with the first `k` forms beside the face, `k = 1, 2, 4, …, 32`, and read on the
  held-out text.

**The search's grain, measured.** The first search eliminated the coordinates in their given
order. On the slice, whose 926 pairs leave the pool's 4,225 products far from independent, it left
its 64-bit grain four times:
- with the floor at `2^10` and 30 fractional bits in `L` (7.4 s);
- with the floor at `2^20` (6.8 s);
- instrumented: an entry of the eliminated column reached `2^51.8` at pivot 1,275, outside the cone a
  semidefinite matrix keeps. `L`'s rounding (`2^−31` of entries near `2^50`, about `2^19` a term)
  had reached the floor;
- with 46 fractional bits: the carried covector row outgrew its grain at pivot 1,152.

The cause was the order, not the width: elimination in a given order on near-dependent products
pivots on rounding, and its multipliers grow (`|l|` reached `2^10` in the instrumented run). Taking
the largest remaining diagonal first is the rank-revealing order. It bounds every multiplier by 1
within a set (by `2^15` for pool rows read on the face's steps), and the slice then ran clean at the
same grain. The exact readout agrees with the search wherever both are read.

**What it reads.** On the training text (1,789,108 cells, 6,330 pairs, 171 arriving classes) the
face's own readout takes 8.263‰ of the Brier score, at the search's grain and exactly alike. The
whole pool after the face carries 36.52‰ of the tension (one of its coordinates is passed over;
its chance level, 4,224 coordinates over the cells, is 2.36‰), against 40.72‰ for the table of
pairs. In thousandths of the tension:

| leading coordinates | 1 | 2 | 4 | 8 | 16 | 32 |
|---|---|---|---|---|---|---|
| the most the pair could carry (the table's spectrum) | 3.70 | 6.94 | 11.91 | 18.48 | 25.63 | 31.93 |
| the pool's spectrum, at the search's grain | 3.455 | 6.319 | 10.980 | 17.186 | 23.757 | 29.217 |
| the founded block, read exactly | 3.455 | 6.319 | 10.980 | 17.186 | 23.758 | 29.217 |
| founded products of two reads | 1.18 | 1.90 | 3.46 | | | |

Held out (48,023 cells), in thousandths of the residual the face's own readout leaves:

| forms | prose | Lean | Rust | digits | all |
|---|---|---|---|---|---|
| 1 | 3.106 | 3.592 | 4.048 | 0.059 | 2.622 |
| 2 | 4.774 | 4.966 | 6.304 | 0.172 | 3.937 |
| 4 | 6.624 | 7.934 | 9.284 | 0.242 | 5.828 |
| 8 | 9.886 | 14.115 | 12.764 | 0.519 | 9.047 |
| 16 | 12.340 | 19.337 | 18.075 | 0.822 | 12.209 |
| 32 | 15.050 | 23.379 | 20.221 | 2.312 | 14.794 |

The held-out residual falls from 0.619 to 0.610 per cell over all (prose 0.702 to 0.692, Lean
0.590 to 0.577, Rust 0.532 to 0.521, digits 0.652 to 0.651). Four forms remove 5.8‰ where the four
products removed 2.4‰, and thirty-two remove about six times what the products did. Only 57 held-out
cells fall on pairs the training text never met, yet they carry 24‰ to 80‰ of each leading form's
held-out square: off the pairs it was fitted on, a form is free and takes large values.

The leading forms read as contrasts among the next byte, each weighing most on a few pairs:
- form 1: `e` against `a`, a space and `o`, weighing most on `iv`, ` d`, `rn`, `ch`, ` p`, `ar`;
- form 2: a space (with `e`) against `a`, a newline, `i` and `n`, on two spaces, `on`, `ce`,
  `}`+newline, `)`+newline, `ge`;
- form 3: `a` against `o` and `r`, on ` p`, ` m`, `pr`, two spaces, `at`, `mp`;
- form 4: `o` against `r`, `t` and `i`, on `pa`, ` p`, `s `, `ha`, `ac`, `wh`.

On the slice the forms memorize, as a slice must: with 926 pairs the pool carries exactly the
table's 263.43‰, 3,300 of its coordinates are passed over, 4,466 held-out cells fall on unmet pairs
and carry 966‰ to 994‰ of each form's square, and the held-out residual grows to 176 per cell. The
slice was the timing read.

**What it says.**
- The pair contact `W(x̄⊗ȳ)` of the one face law is a real face of text. One full form carries 93%
  of what the best single coordinate of the pair could (3.455 against 3.70), where one product of
  two reads carried a third; thirty-two carry 92% of the best thirty-two. On held-out text they keep
  about half of what they carry on the training text, and they hold in prose, Lean and Rust alike.
- The digits take almost none of it (2.3‰): the byte before says little about the next digit.
- The face is small, 1.5% of the held-out residual, as the table's ceiling said it would be: even in
  sample the last two bytes hold about 4% of the tension. What a longer context holds is the next
  founding's question, read the same way on its own pool [agent-inferred].

**The run.** The slice ran in 13.7 s at a peak of 229 MiB. The projection for the whole text, from
the slice's units and the founding's pass (92.7 s), was 190 s and at most 250 s: the elimination
grows with the coordinates taken squared (at most 4,225, about 21 times the slice's), the forms
alike, and the readouts with the moments' width. The deadline was 300 s. The run took 121.1 s at a
peak of 319 MiB, 0.64 of the projection.

## The block joined to the tower

The block was read beside the tower. This step joins it to the tower's face, so the tower codes and
writes with it (`install-tower-pair-block`, `sample-tower-block`, [agent-inferred, October 24]).

**The join.**
- At each byte the frozen tower gives its face `p̂` (on `2^−24`) and the top face its readout reads
  (`Tower::advance_top`, and `Tower::read_faces` over a passage). The block's forms are read at the
  pair of the byte before and the current byte. With `f̂ = (top, 1, c_1, …, c_k)`, the readout fitted
  exactly on the training text gives the fitted covector `ĝ = R f̂`. The covector is `p̂ − q`, so
  `q̂ = p̂ − ĝ` is the least-squares read of the next byte from the face, its top and the block.
- `q̂` is not a distribution: it can be negative. It is moved to the nearest one under the Brier
  score. Over the arriving classes `Q_c = max(K q̂_c − (S_K − 2^24), 0)`, where `K` is the largest
  count whose `K`th largest value lies above the shared shift `(S_K − 2^24)/K` and `S_K` is the sum
  of those `K`. `Q` sums to `K·2^24` and is zero off the arriving classes.
- The joined face mixes the two, `p′ = (1 − η) p̂ + η q̃` with `η = j/32`. Its masses are exact
  integers, `m′_c = (32 − j) m_c K 2^24 + j Q_c T` over the total `32 T K 2^24`, below `2^108`. A
  class the block reads as zero keeps the tower's share `(1 − η) p̂`, so no byte is coded at
  unbounded length.
- The code is the cross-entropy at each `η` of the partition, and it is convex in `η`. The installed
  `η` has the least training code. The held-out text is read at every `η`.
- At `η = 0` the joined masses are the tower's times one constant, so the code and the writing are
  the tower's own. Checked: the code at `j = 0` reads as the tower's to the thousandth on the slice,
  the training text and the held-out text (the code is read on `2^−20` bits, so a scaled mass can
  move its last grain), and the block with `η` set to 0 wrote the tower's prose at one draw byte
  for byte (`INSTALL_WRITE_eta0_prose_a1.txt` against `CONT_WRITE_prose_a1.txt`).
- `R` is released to 64-bit words, `round(X 2^b / D)` with `b` set so the largest is below `2^62`
  (`b = 42` here). The forms' tables are as above.

**What it codes.** In bits a byte: the tower alone, the face's own readout joined with no forms (its
least training code at `η = 11/32`), and the block of 32 forms joined (`η = 21/32`):

| text | tower | the face's readout, no forms | 32 forms |
|---|---|---|---|
| training | 2.316 | 2.302 | 2.220 |
| held out, prose | 3.117 | 3.095 | 3.026 |
| held out, Lean | 2.431 | 2.398 | 2.316 |
| held out, Rust | 2.172 | 2.157 | 2.085 |
| held out, digits | 2.324 | 2.317 | 2.310 |
| held out, all | 2.511 | 2.492 | 2.434 |

- Joined, the block takes 0.077 bits a byte off the held-out code, 3.1%. Of that, 0.058 is the forms'
  and 0.019 the face's refitted readout. On the training text it takes 0.096, and the held-out text
  keeps 80% of it.
- The `η` chosen on the training text is within a thousandth of a bit of the held-out least (2.433,
  at `η` from 17/32 to 20/32): the mixture does not overfit.
- The digits take almost nothing, as the block's held-out reading said.

**What it writes.** The joined tower wrote 400 bytes from each of the four prompts at one and two
agreeing draws (`INSTALL_WRITE_<prompt>_a<draws>.txt`, each with the prompt's code under the tower
and under the join). The prompts' code falls for prose (4.097 to 3.750 bits a byte), Lean (2.335 to
2.210) and Rust (2.333 to 2.237), and rises for the digits with their context (2.779 to 2.850).
- The writing keeps the tower's kind. At one draw it is Rust doc comments, Lean comment heads and
  prose with broken words. At two draws it runs the text's own phrases ("The completed residual: the
  residual receiving the conserved from the commuted receiving carried residual is …").
- From the digit prompt at one draw the join and the tower alone open alike (`5`, then `87*90=820`)
  and then part: the join leaves the equations on that line for prose and Lean, and the tower alone
  stays in them through its 400 bytes (34 well-formed equations, 1 right). At two draws the join
  writes 40 equations in the prompt's form, 2 of them right (`74*0=0`, `55-16=39`); the tower
  alone wrote 41, none right.

**What it says.**
- Joined to the face, the pair contact `W(x̄⊗ȳ)` shortens held-out text by 3%, three quarters of it
  the forms' own. It is a real face of text, and small, as the tension said: the last two bytes hold
  about 4% of the tension.
- It moves bytes within words and does not change what the writing is. What the rest of the tension
  holds lies past the last two bytes [agent-inferred]; the next founding reads a longer pool the same
  way.

**The run.** The slice ran in 12.1 s at a peak of 203 MiB. The projection for the whole text was
255 s: the founding through its fit measured 121 s whole, and the training join 130 s at the
slice's 72.6 µs a cell over 1,789,108 cells. The deadline was 300 s. The run took 226.7 s at a peak
of 314 MiB, 0.89 of the projection; with no forms it took 206.2 s. Each write took under 0.6 s.

## The pair forms inside the learner

The block was joined beside the tower's face through a closed-form fit and a mixture. This step
joins its forms inside the learner, so the learning step itself moves what reads them
(`PairFace`, `Tower::join_pair_face`, `TowerLearner::join_pair_face`; the commands
`join-tower-pair-face`, `read-tower-pair-cells` and `read-tower-pair-leverage`; [agent-inferred,
October 24], decided with GPT-6's review of the block).

**The law.**
- At each cell the face reads the pair of the class before and the class arriving,
  `c_v(p) = x̂_curᵀ W_v ŷ_prev` with `x̂ = (E₀(cur), 2^16)` and `ŷ = (E₀(prev), 2^16)` (the start's
  `ŷ = (0, 2^16)`), released by each form's founding shift, rounded half up, to `2^−16`.
- Its values enter twice through learned material on `2^−24`: the readout, `z += V c(p)`, and the
  input, `x⁰ = E(u) + P c(p)`. `V` and `P` open at zero, so a joined tower reads every passage
  exactly as the tower alone (checked on the fixture), and they take the section's covector under
  the certified deposit with the rest of the material: `V` gets `δz ⊗ c`, `P` gets `δx⁰ ⊗ c`.
- The class before is carried in the state (`TowerState::previous`, the start at rest), so a
  passage read in two parts codes as the whole: the pair at the seam is read whole (checked).
- `W` is fixed at the founding and the face is held as the forms' values at every pair, read at
  the founding encoding `E₀`. Reading `W` at every cell would cost `32 · 65² = 135,200`
  multiply-adds a cell, more than the tower's own cell; the values are the forms' resident face,
  generated from them and never authored. The encoding moves after the founding, and the face
  keeps its founding chart; a refounding rereads it at the encoding it meets.
- The face is carried at every pair, met or not: an index of which contexts the training text met
  would be the recorded failure of an index of contexts. The held-out cells at pairs the training
  text never meets are read apart.
- The duplex refuses a pair-faced tower: it reads its towers' faces off their tops, which a pair
  face does not read alone.

**The checks.** The tower's 34 tests pass, four of them new: a joined tower opens on itself, it and
its learner restore exactly from their text, the face's covector matches the code's difference,
and the seam's pair is read from the carried class. `V`'s covector is read on every fixture tower.
`P` moves the input at every cell, so on a tower with a kink (rectifying contacts or a gate) every
step of it crosses one somewhere: on the rectifying fixture five of its parameters crossed a kink
within steps of `2^−7` units and the sixth fell below the reading's grain. It is read on the
kinkless pair-contact tower, where it matches.

**The reach of the free values.** Joined to the five-pass pair tower (`hbig2_pair` `STATE.0`), the
face agrees with the block's tables at all 65,792 pairs. The training text meets 6,331 of them. On
the 59,461 it never meets, each form's largest value is 1.13 to 3.49 times its largest on met
pairs, and 4 to 1,065 unmet pairs per form sit past that largest met value (`FACE_JOIN.txt`).

**What it codes.** One more pass from the same five-pass tower, joined and plain (the foil), in bits
a byte:

| text | five passes | one more, plain | one more, forms in the learner |
|---|---|---|---|
| training, during the pass | – | 2.134 | 2.122 |
| held out, prose | 3.117 | 3.115 | 3.118 |
| held out, Lean | 2.431 | 2.417 | 2.409 |
| held out, Rust | 2.172 | 2.151 | 2.149 |
| held out, digits | 2.324 | 2.306 | 2.283 |
| held out, all | 2.511 | 2.497 | 2.490 |
| held out, cells at met pairs (47,965) | 2.507 | 2.492 | 2.484 |
| held out, cells at unmet pairs (58) | 6.137 | 6.619 | 7.606 |

- The forms in the learner take 0.007 bits a byte off the held-out code beside the foil, 0.3%:
  0.008 on met pairs, none on prose, 0.023 on the digits. The closed-form join took 0.058 for the
  forms on the frozen tower.
- On the 58 cells at unmet pairs the learned readout reads the forms' free values and loses a bit a
  cell beside the foil (6.62 to 7.61). Over the held-out text that costs 0.001 bits a byte.
- During the pass the joined code ran below the foil's in 47 of 55 reads, and the gap widened: by
  quarters of the pass, 0.009, 0.006, 0.016 and 0.017 bits a byte. `V` is still learning at the
  pass's end (its entries' root mean square is 1.88 units against the readout's 0.55).

**The leverage of the unmet pairs** (the mathematics thread's reading, its effective-tension record
§9; `read-tower-pair-leverage`). The training text gives the exact Gram of what the joined
readout reads, `x = (top, 1, c(pair))`, over its 1,789,104 cells: dimension 97, full rank, no pivot
passed over. Every held-out cell at an unmet pair and every 64th at a met pair is read by one
forward pass over the elimination's stored rows, `h = −corner/Δ_r`, split at the bias into the top
face's part and the pair face's part. In units of the average training cell's leverage, `rank/N`:

| one-pass state | cells | h mean | median | largest | top face's part | pair face's part |
|---|---|---|---|---|---|---|
| forms in the learner, met pairs | 747 | 0.99 | 0.64 | 47 | 0.70 | 0.29 |
| forms in the learner, unmet pairs | 58 | 51.3 | 19.0 | 1,172 | 27.7 | 23.6 |
| foil (its face alone, unit 65/N), met pairs | 747 | 1.17 | 0.66 | 138 | 1.17 | – |
| foil, unmet pairs | 58 | 94.6 | 1.15 | 4,700 | 94.6 | – |

- No reading has an open part: every held-out reading lies in the span the training cells fixed.
- At unmet pairs the leverage is 51 training cells' on average, against one at met pairs, and both
  parts grow: the pair face's (0.29 to 23.6) and the top face's (0.70 to 27.7). The tower's own
  state at a pair it never met sits far from its training states too.
- In absolute terms `h` stays small. The largest is `1,172 · 97/1,789,104 = 0.064`, so in the
  Gaussian chart the released face's error at that reading grows by at most 6.4%, a charge of at
  most 0.044 bits.
- [agent-inferred] The bit a cell the learned readout loses at unmet pairs is therefore not an open
  direction. The bound `|wᵀv_s|² ≤ (wᵀGw)·h` lets a form's value at a reading of 1,172 training
  means reach `√(97 · 1,172) ≈ 337` times its root mean square over the training cells; the reach
  above found values up to 3.5 times the largest met value, and the softmax reads them through `V`
  as a confident logit.

**What it writes.** Both states wrote 400 bytes from each of the four prompts at one and two
agreeing draws (`FACE_WRITE_<state>_<prompt>_a<draws>.txt`; whole in
`outputs/2026-10-24_TOWER_WITH_PAIR_FORMS_IN_THE_LEARNER_WRITES.md`, outside the repository).
- Prose, Lean and Rust keep the tower's kind: comment heads and doc lines with broken words, and at
  two draws the text's own phrases.
- From the digit prompt at one draw the joined tower stays in equations through its 400 bytes, 39
  well-formed, 2 right (`99-67=32`, `72-43=29`); the foil leaves them after two lines. At two
  draws both write 42, the joined 2 right and the foil 3. Right answers stay at chance, and many
  miss by a little (`72+79=152`).

**What it says.**
- The learning step reads the founded forms and gains slowly: one pass carries an eighth of what
  the closed form read on the frozen tower, and the gain is still widening. The next loop is the
  second pass of both, read the same way.
- The unmet pairs sit inside what the training text fixed, at fifty times a training cell's leverage,
  and the learned readout pays a bit a cell there. Over the held-out text that is a thousandth of
  a bit a byte, so the next loop leaves the unmet pairs as they are and reads them again.

**The run.** The release binary built in 377 s. The 60 s development reads gave 0.33 to 0.37 s a
section. The first launch projected the pass from the largest measured block alone (642.5 s joined,
596.6 s plain) and stopped on evidence at its first block, 11,782 ms against a bound of 11,768
(1.001). The relaunch took every block measured before it, their largest plus their largest
spread: 698.8 s joined (deadline 739 s) and 660.8 s plain (deadline 701 s). The passes took 615.0 s
(0.88 of the projection, peak 193 MiB) and 585.5 s (0.89, peak 176 MiB). The met and unmet reads
took 4.0 to 4.5 s each, and each write 0.6 to 3.4 s. The gate took 690 s against a projection of
1,334 s (the previous host's 460 s times this host's measured 2.9 on the library's test build;
deadline 1,500 s). The leverage read's timing slice (a sixteenth of the training text) took 88.5 s:
the Gram 9.6 s and 5,943 held-out readings at 13.3 ms each. The whole text was projected at 167 s
(deadline 240 s) and took 150.5 s joined (0.90) and 145.8 s for the foil.

### The second pass

Both towers ran one more pass over the same text from the first pass's states, and were read the
same way. In bits a byte:

| text | one pass, plain | one pass, forms in the learner | two passes, plain | two passes, forms in the learner |
|---|---|---|---|---|
| training, during the pass | 2.134 | 2.122 | 2.114 | 2.084 |
| held out, prose | 3.115 | 3.118 | 3.087 | 3.102 |
| held out, Lean | 2.417 | 2.409 | 2.394 | 2.366 |
| held out, Rust | 2.151 | 2.149 | 2.091 | 2.085 |
| held out, digits | 2.306 | 2.283 | 2.304 | 2.302 |
| held out, all | 2.497 | 2.490 | 2.469 | 2.464 |
| held out, cells at met pairs (47,965) | 2.492 | 2.484 | 2.463 | 2.457 |
| held out, cells at unmet pairs (58) | 6.619 | 7.606 | 7.016 | 8.105 |

- On the training text the forms' gain grew two and a half times: 0.012 bits a byte over the first
  pass, 0.030 over the second (by quarters 0.007, 0.038, 0.044 and 0.032; the joined code ran below
  the foil's in 52 of 55 reads).
- Held out it did not grow: 0.007 after one pass, 0.005 after two. Lean's gain grew (0.008 to
  0.028) and Rust's held (0.002 to 0.006). Prose turned further against the forms (−0.003 to
  −0.015), and the digits' gain is gone (0.023 to 0.002): the joined tower's digits went from 2.283
  to 2.302 while the foil's held at 2.304.
- At the 58 cells at unmet pairs both towers lose with every pass (6.137 at the five-pass start; the
  foil 6.619, then 7.016; the joined 7.606, then 8.105). The forms' extra loss there is 1.09 bits a
  cell (0.99 after one pass).
- The second pass opened above the first. Over its first 32 sections the joined tower coded 2.588
  bits a byte and the foil 2.473, against 2.346 and 2.327 at the first pass's opening, and one of the
  joined tower's first 32 sections deposited nothing after 31 halvings of its step (the foil halved
  once). By section 128 the two were level (2.223 and 2.225), and from there the joined ran below.

The leverage, read as before (`read-tower-pair-leverage`, the exact Gram of 97 or 65 coordinates,
full rank, no pivot passed over), in units of `rank/N`:

| two-pass state | cells | h mean | median | largest | top face's part | pair face's part |
|---|---|---|---|---|---|---|
| forms in the learner, met pairs | 747 | 1.24 | 0.63 | 257 | 0.95 | 0.29 |
| forms in the learner, unmet pairs | 58 | 69.8 | 18.9 | 2,134 | 45.8 | 24.0 |
| foil (its face alone, unit 65/N), met pairs | 747 | 0.95 | 0.66 | 17 | 0.95 | – |
| foil, unmet pairs | 58 | 171 | 1.06 | 8,880 | 171 | – |

- Still no reading has an open part.
- At unmet pairs the pair face's part held (23.6 to 24.0) and the top face's grew (27.7 to 45.8).
  The forms are fixed, so what moves away from the training cells at the pairs the text never met is
  the tower's own state. The largest absolute leverage is now `2,134 · 97/1,789,104 = 0.116`.
- The foil's face alone reads most unmet cells as ordinary (median 1.06) and a few far out (one at
  8,880 means, `0.32` absolute). With the forms joined the median unmet cell sits at 19 means: the
  forms' free values carry the distance, as after one pass.

**What it writes** (`FACE2_WRITE_<state>_<prompt>_a<draws>.txt`; whole in
`outputs/2026-10-24_TOWER_WITH_PAIR_FORMS_SECOND_PASS_WRITES.md`, outside the repository).
- Prose, Lean and Rust keep the tower's kind: comment heads and doc lines with broken words, and at
  two draws runs of the text's own phrases (`/-- The companion composition is the next composition
  endpoint`).
- From the digit prompt at one draw the joined tower writes 6 well-formed equations, none right,
  then leaves for words; after the first pass it had stayed for 39. The foil leaves within its first
  equation. At two draws the joined writes 40, 1 right (`49*0=0`), and the foil 41, 1 right
  (`74-37=37`). Many miss by a little (`95-63=31`, `62-38=25`).

**What the second pass says.**
- The forms inside the learner are fitting the training text: their training gain grew two and a
  half times while their held-out gain fell from 0.007 to 0.005. The closed-form join read 0.058 on
  the frozen five-pass tower, and its 2.434 still codes the held-out text below either tower after
  two more passes (2.464, 2.469). [agent-inferred] The certified step deposits what lowers each
  section's own code; the closed form solves the same readout over every training cell at once, and
  what it fixes generalizes where the per-section path does not.
- The pair face is spent at this grain. Its ceiling is 4% of the tension (40.7‰ of `S`), the closed
  form read 0.058 of it held out, and the learner's path an eighth of that after one pass and a
  twelfth after two. The rest of the tension lies past the last two bytes. The next loop founds the
  situated pool `top ⊗ x̂`, the conjunction of the tower's own state with the arriving class, which
  reaches back through the whole passage the state carries, and reads it by the exact Gram first, as
  the block was read, before any of it enters the learner.

**The run.** Each pass was projected from every block measured before its launch (61 each: the
development reads, the stopped launch and the first passes), their largest plus their largest
spread: 785.2 s joined (deadline 825 s) and 812.1 s plain (deadline 852 s). The passes took 576.4 s
(0.73, peak 200 MiB) and 556.2 s (0.68, peak 177 MiB). The met and unmet reads took 4.2 and 3.7 s,
each write 0.6 to 3.1 s, and the leverage reads 156.8 s and 140.7 s (projected 167 s, deadline
240 s).

## The circuit at the result

Brandon, October 24: read the circuit's own signals, its power, loudness and loss, and the
expansion and contraction of the written results he pointed out on October 23 (the
[near-miss record](2026-10-23_A_NEAR_MISS_IS_A_DRAW_FROM_THE_FACES_IT_KEPT_AND_THE_BASES_CHEAP_RINGS_CLOSE_THE_REST.md)'s
occasion), not the code alone. This step reads both.

**The written results** (`tools/answer_digits.py '74-72=' <writes>`, an exterior count). The
digit-prompt writings in these receipts, 37 writes from this record's towers on the mixed Holonics
terrain (29 of them write equations), hold 804 whole equations with a result that is not negative.
The towers of the arithmetic terrain are not among them: there the pumped tower wrote a sum's units
right in 191 of 240, keeping the parity in 36 of the 49 misses
([its record](2026-10-23_ON_A_TERRAIN_OF_INTERACTING_DIGITS_THE_TOWER_COMPUTES_WHAT_IT_NEVER_MET_WHERE_IT_KNOWS_THE_LEVEL.md)).
On this terrain:

| result | equations | length right | leading digit right | units right | whole right |
|---|---|---|---|---|---|
| sum that expands (carries into the hundreds) | 218 | 210 | 210 | 17 | 10 |
| sum that holds its length | 182 | 170 | 71 | 27 | 8 |
| difference that holds | 101 | 96 | 45 | 10 | 5 |
| difference that contracts to one digit | 34 | 30 | 6 | 6 | 5 |
| product, full length | 203 | 198 | 108 | 46 | 0 |
| product, one digit short | 66 | 40 | 12 | 11 | 5 |

- The length is right in 744 of 804. A sum that carries into the hundreds is written at its length
  210 times of 218, with its leading 1 right in 209 of them. A difference written too short, as
  `99-56=5` was, is 4 of 135.
- The units of sums and differences are right in 60 of 535, chance among ten digits. Where a sum
  is written at its length, its units miss by every step of the ring of ten about equally (27 to 50
  times each, against 41 right).
- A sum's tens is right in 190 of 380 and off by one in 168 of the rest: the carry from the units.
  Where the operands' units carry, the written tens takes the carry in 52 of 108 and omits it in 23;
  where they do not, it adds one anyway in 38 of 208.
- The near-miss record's §2 read the sums' units as right from the lines it quoted. Counted over
  these writings, the sums' units are at chance (44 of 400) and what the towers place is the size:
  the length, the leading digit and, more often than not, the carry. So the law that held the ring
  2 of the ten on arithmetic alone does not hold it on the mixed terrain.

**The reading** (`Tower::read_circuit`, `read-tower-circuit`; [agent-inferred, October 24]). At each
cell and level the frozen tower gives the modes' stored energy before the class arrives
(`before = Σ_k |h_k|²`), what the moves carry of it by the step's own released law
(`carried = Σ_k |α_t h_k + β_t h̄_k|²`) and the energy after the push (`after`), exact on `2^(−48)`,
beside the read's scale, the contacts' reach and the cell's code. `lost = before − carried` is what
the level dissipates at the tick (nonnegative: `|α_t| + |β_t| = ρ_t < 1`, the pumped mode's norm
identity, formal-checked in `HNN/PassiveMode`: `pumped_norm_le`, `pumped_carried_le`), `push = after − carried` the power the arriving class brings, and
`dE = after − before = push − lost`. The test `the_circuit_readings_energies_are_the_forwards`
checks the energies and the code against the forward on the pumped pair-contact fixture and the
ungated one.

It read the held-out equations (`htext2` `dev_arithmetic.txt`, 11,998 bytes, 1,253 lines) as one
passage from rest, at every plain pass of the pair tower (passes 1 to 4 `hbig_pair` `STATE.0`–`.3`,
pass 5 `hbig2_pair`, passes 6 and 7 `hcont1` and `hcont2`) and at the two joined passes (`hface1`,
`hface2`). `tools/tower_circuit.py` sorts the cells by the role of the class each predicts and divides
each level's energies by that level's mean stored energy over the reading. Over the seven passes the
mean stored energy grew from 1,430 to 28,255 in the lower level and from 38,348 to 144,968 in the
upper (in the state's unit squared), and the reading's code fell from 2.499 to 2.300 bits a byte.

At `=` (the cell that has just heard `=` and predicts the result's first digit), the upper level's
change `dE` by the result's shape, and the first digit's code in bits:

| result | pass 1 | 2 | 3 | 4 | 5 | 6 | 7 | first digit, pass 1 → 7 |
|---|---|---|---|---|---|---|---|---|
| sum that expands | +0.040 | +0.078 | +0.350 | +0.463 | +0.422 | +0.511 | +0.287 | 0.46 → 0.12 |
| sum that holds | +0.022 | +0.002 | +0.036 | −0.014 | −0.080 | −0.017 | −0.053 | 3.13 → 1.39 |
| difference that holds | +0.025 | +0.005 | +0.012 | −0.065 | −0.106 | −0.125 | −0.130 | 3.06 → 1.68 |
| difference that contracts | +0.011 | +0.011 | −0.014 | −0.052 | −0.082 | −0.121 | −0.169 | 3.73 → 4.63 |
| product, full | −0.048 | +0.013 | −0.035 | −0.062 | −0.080 | −0.083 | −0.086 | 2.86 → 1.70 |
| product, short | −0.052 | −0.004 | −0.053 | −0.141 | −0.152 | −0.139 | −0.129 | 3.56 → 4.25 |

Through the rest of the result, per pass:

| cell | pass 1 | 2 | 3 | 4 | 5 | 6 | 7 |
|---|---|---|---|---|---|---|---|
| a sum's middle digit (three-digit sums): code | 3.21 | 2.89 | 1.88 | 1.36 | 1.29 | 1.23 | 1.03 |
| its upper level's stored energy | 0.95 | 1.07 | 1.40 | 1.44 | 1.55 | 1.59 | 1.44 |
| its upper level's `dE` | −0.060 | −0.102 | −0.251 | −0.263 | −0.328 | −0.316 | −0.224 |
| a sum's units: code | 3.52 | 3.55 | 3.51 | 3.46 | 3.50 | 3.54 | 3.49 |
| its upper level's `lost` | 0.178 | 0.178 | 0.345 | 0.399 | 0.455 | 0.441 | 0.431 |
| a difference's units: code | 3.52 | 3.85 | 3.73 | 3.66 | 3.76 | 3.72 | 3.61 |
| its upper level's `lost` | 0.179 | 0.183 | 0.255 | 0.298 | 0.341 | 0.323 | 0.349 |
| a product's units: code | 3.17 | 3.05 | 2.86 | 2.81 | 2.75 | 2.89 | 2.71 |
| a sum's line end: code | 0.05 | 0.01 | 0.00 | 0.00 | 0.00 | 0.01 | 0.00 |
| its upper level's `dE` | +0.268 | +0.184 | +0.215 | +0.110 | +0.083 | +0.072 | +0.123 |

The joined passes read the same: the pair face moves a sum's units by 0.08 bits (3.41 at its second
pass against the foil's 3.49), and the split at `=` keeps its signs (`CIRCUIT_j6.txt`,
`CIRCUIT_j7.txt`).

**What the circuit says.**
- The upper level's energy at `=` learned the result's length. At pass 1 every shape moved it by at
  most 0.052 of its mean. From pass 3 a carry into the hundreds expands it (0.29 to 0.51 of its
  mean), and from pass 4 every result that keeps or loses length contracts it, a difference that
  shrinks to one digit the most. The first digit's code fell with the split. [agent-inferred] The
  same `=` lands on states that differ only by the operands, so the push's power at `=` is the
  operands' size read ahead: this is the expansion and contraction of October 23, in the circuit.
- Through the result the upper level contracts: it is loudest at a sum's middle digit (1.4 to 1.6
  times its mean from pass 3) and sheds the most there and at the units. At the line end, whose code
  is 0.00 bits from pass 3, it expands again.
- The units are the one place the passes did not move. Their code stayed at chance (log₂ 10 = 3.32
  bits) at every pass, while the upper level's loss at that cell grew from 0.18 to 0.43 of its mean:
  each pass taught it to dissipate there, not to place the digit.
- [agent-inferred] That loss is the measurable tension of the near-miss record and the effective
  tension record, located on the residue face `ℤ/10 = ℤ/2 × ℤ/5`. A sum's units are one crossing on
  that cycle, but between the two operands' units, three bytes apart; their phases must be composed,
  and no read of summed magnitudes reaches a residue. The pair face joins only neighbouring classes.
- The lower level grows quieter during the result at every pass (its loss at a sum's units from
  0.197 to 0.056 of its mean): it is loud while it hears the operands and coasts while the result is
  written.
- Read cell by cell, the upper level dissipates 0.25 to 0.47 of its mean energy a tick at the result.
  The swell line's `1 − max|λ|`, which fell toward the margin over these passes, is its slowest mode
  alone; the fast modes of the ladder and the gates carry the loss.
- `cancel` stayed 0.00 at every role and pass: summed over a level, the push never lowered the
  energy the moves carried. Any cancellation is between modes, below the level's grain.

**Decided next** [agent-inferred]: whether the operands' units are still in the state when the units
are predicted. On the training text's equation block, fit the units of each operand and of the
result from the top face at the units cell by the exact Gram, and read the fit on the held-out
cells. If the operands' units read and the result's do not, the missing term is the composition (a
contact between the state at the units and the state at the operands' units); if they do not read,
the dissipation erased them and the missing term is retention.

**The run.** The release binary `circuit1` built in 341.6 s (projected 377 s from `face1`'s build,
0.91; deadline 450 s). The nine reads were unmeasured, planned at one to three minutes with a 180 s
deadline each, and ran together at one thread each: 6.2 to 7.4 s, peak 22 to 68 MiB. The tower's
tests, with the new one, passed (35) in 218.8 s with their build, against 115.7 s projected from
the last measured run (1.89; deadline 240 s, peak 4.6 GiB), and the gate passed every step in
618.3 s (projected 690 s, 0.90; deadline 800 s, peak 3.1 GiB).

## The flux at the units

Brandon, October 24: the energy's transport is diffusion in the abstract. The observer can witness
the flux and the parametric orientation of where it goes: a knot that has not been crossed can still
slip, because the crossing is what changes the friction's distribution, and one feels where the
nodes and antinodes cross. This step reads the circuit mode by mode at a sum's units, the one place
the passes did not move.

**The per-mode read** (`CircuitMode`, `read-tower-modes`; [agent-inferred, October 24]). Each
level of `Tower::read_circuit` now carries every mode at the cell: its state before the class
arrives, what the moves carry of it (`α_t h + β_t h̄`, released on the step's own law) and its state
after the push, on `2^(−24)`, beside the move `λ_t` and the pump `β_t` on `2^(−30)`. The test
`the_circuit_readings_energies_are_the_forwards` now also checks that the modes' before and after
are the forward's states and that their carried energies sum to the level's. `read-tower-modes`
prints them at named cells, all ten integers a mode (`full`) or the state after (`after`).
`tools/tower_modes.py` reads them outside the machine: `flux` splits each mode's push
`d = after − carried` against its carried phase `c` into `R = 2 Re(c̄ d)` along the phase (a
boost), `Q = 2 Im(c̄ d)` across it (a turn) and `N = |d|²` (power `R + N`), with the share of its own
energy the moves keep; `probe` fits the operands' and the result's units digits from one level's
state; `turns` reads how each mode's move depends on the digit that arrives.

**Where the loud modes release.** On the held-out equations, at a sum's middle digit and at its units,
the upper level of the mixed pair tower at passes 1 and 7 and of the arithmetic tower
(`MODES_FLUX_*.txt`; shares of the level, `kept` of the mode's own energy):

| | pass 1, middle | pass 1, units | pass 7, middle | pass 7, units | arithmetic, middle | arithmetic, units |
|---|---|---|---|---|---|---|
| the level keeps | 0.79 | 0.81 | 0.76 | 0.63 | 0.54 | 0.47 |
| the loudest mode: energy, kept | 50: 0.55, 0.95 | 50: 0.57, 0.95 | 50: 0.37, 0.90 | 50: 0.45, 0.90 | 5: 0.15, 0.34 | 12: 0.14, 0.28 |
| the next: energy, kept | 32: 0.23, 0.78 | 32: 0.22, 0.76 | 9: 0.22, 0.85 | 9: 0.21, 0.58 | 12: 0.14, 0.66 | 5: 0.08, 0.22 |
| of the push's power, along the carried phase (`R`) | 0.40 | 0.52 | 0.67 | 0.66 | 0.21 | 0.21 |

- At pass 1 the loud modes keep the same at the middle digit and the units. By pass 7 they hold
  through the middle digit and let go at the units: mode 9 keeps 0.85 then 0.58, mode 32 0.94 then
  0.22, mode 16 0.98 then 0.19. Mode 50, a pump mode (`|β|` 0.79 to 0.88 against `|λ|` below 0.17,
  so its phase is held on one of the pump's two sheets), keeps 0.90 at both and holds 37 to 45% of
  the level's energy.
- The arithmetic tower's upper level holds its energy over many modes (the loudest 0.14 to 0.15),
  releases more than half of it at the units, and takes the push there mostly as fresh amplitude
  (`N`, 0.79 of the power) rather than as a drive along the phase it carried: the units cell is
  written anew. The mixed tower at pass 7 drives two thirds of the push along the phase it carries.
- Per mode, the push lowers what a mode carries (`cancel`) in every loud mode of the arithmetic
  tower's upper level (each with at least 1% of the energy: 25 modes at the units, in 4 to 46% of
  the cells; 18 at the middle digit, in 2 to 56%). In the mixed tower at pass 7 it does so in 3 of
  the 7 loud modes at the units (mode 16 in 28% of the cells, the others under 10%) and in 6 of 11 at
  the middle digit (mode 16 in 42%). The circuit read's level sums never cancelled: the
  cancellations are between modes, as that read inferred.

**Whether the strands reach the units.** The probe takes the training text's equation block (its
22,551 lines are the arithmetic terrain's training text, byte for byte), read in eight parts each
from rest, and fits each class's indicator by least squares from one level's state after the cell:
every coordinate released to `2^(−10)` of the state's unit, one unit of ridge on the diagonal, the
exact Gram solved by Bareiss elimination in integers. On the held-out equations the read is the
share of cells whose largest fitted class is the true one. The cells: `A` has just heard the first
operand's units digit, `B` the second's, `E` the `=`, and `U` codes the result's units. A linear read
of a state in which the two digits are superposed can give either digit and not their sum: on the
ring `ℤ/10` the sum's character is the product of the operands', `χ(c₀) = χ(a₀)χ(b₀)`, a crossing of
the two strands, which a sum of what each left behind does not contain.

The pair tower of the mixed terrain at pass 7 (`hcont2`) against the pumped tower of the arithmetic
terrain after its 12 passes (`ap_t1`), on the same 495 held-out sums (the commonest class: 62 of
495 for `a₀`, 57 for `b₀`, 63 for `c₀`):

| cell, level | mixed `a₀` | `b₀` | `c₀` | arithmetic `a₀` | `b₀` | `c₀` |
|---|---|---|---|---|---|---|
| `A`, lower | 495 | 49 | 40 | 495 | 27 | 54 |
| `B`, lower | 476 | 495 | 134 | 482 | 495 | 370 |
| `B`, upper | 347 | 479 | 76 | 192 | 246 | 67 |
| `E`, lower | 476 | 495 | 129 | 482 | 495 | 368 |
| `U`, lower | 375 | 492 | 84 | 424 | 476 | 301 |
| `U`, upper | 215 | 369 | 79 | 136 | 174 | 459 |

Differences (268; `c₀`'s commonest 35) read `c₀` at `B` lower in 68 (mixed) and 176 (arithmetic),
and at `U` upper in 45 and 208. Products (490; commonest 132, mostly 0) read 281 and 326 at `B`
lower, 195 and 345 at `U` upper.

**Where the crossing lives.** At `B` the second operand's units digit arrives, and the
lower level's move is that digit's alone (its spread over the digit's cells is zero). A pumped
mode's move is real-linear, `h ↦ λ h + β h̄`, a real `2×2` matrix `M(b₀)` acting on the carried state
that holds `a₀`, so the step itself carries a bilinear contact between the two strands, as large as
`M` depends on the digit. `turns` reads that dependence, `mean_d ‖M(d) − M̄‖² / mean_d ‖M(d)‖²`
weighted by each mode's share of the stored energy at `B`, and how many modes hold the energy in
effect (`1 / Σ share²`):

| lower level at `B` | share of the move that depends on the digit | modes holding the energy | the loudest mode's share |
|---|---|---|---|
| mixed pair tower, pass 1 | 0.057 | 5.7 | 0.364 (mode 16) |
| mixed pair tower, pass 7 | 0.036 | 1.6 | 0.786 (mode 16, its move 0.027 the digit's) |
| arithmetic pumped tower, pass 12 | 0.172 | 23.2 | 0.122 (mode 2) |

No mode in either tower turns as a character of the ring of ten: across both levels of both towers,
no turn `arg λ(d)` and no pump axis `arg β(d)` fits `d ↦ 2π m d/10` at 0.9 or better (the turns fit
`m = 0`, the same turn for every digit, at 0.91 to 1.00 in the loud modes). The crossing the
arithmetic tower reads is spread over its modes, not placed in one.

**The contact or the terrain.** Two towers of the first mixed terrain (`htext1`: the four media,
the digits 54,016 of 216,240 training bytes, the first quarter of the arithmetic training text), 12
passes each, read and probed the same way on sums: the plain pumped tower, which has the arithmetic
tower's own declaration (rectifying contacts), and the pair tower (`MODES_PROBE_plain12_sums.txt`,
`MODES_PROBE_pair12_sums.txt`, `MODES_TURNS_plain12.txt`, `MODES_TURNS_pair12.txt`):

| tower | terrain | contact | passes | `c₀` at `B`, lower | `c₀` at `U`, upper | move's digit share | modes holding the energy |
|---|---|---|---|---|---|---|---|
| arithmetic | digits alone, 216,131 bytes | rectifier | 12 | 370 | 459 | 0.172 | 23.2 |
| plain | first mixed | rectifier | 12 | 124 | 66 | 0.080 | 5.0 |
| pair | first mixed | pair | 12 | 127 | 89 | 0.035 | 2.4 |
| pair | eight times the text, digits 216,131 of 1,789,116 bytes | pair | 7 | 134 | 79 | 0.036 | 1.6 |

Both first-terrain towers hold the operands at `B` (475 and 495 of 495 each) and leave them
uncrossed.

**What it says** [agent-inferred]:
- The knot is the crossing of the two operands' units, and it is made at the tick where the second
  arrives, by the move that digit makes on the strand the state carries. The tower trained on the
  digits alone makes it, holds the sum in its upper level at the units and writes a sum's units right
  (191 of 240). Every tower trained beside the Holonics text holds both strands at that tick and
  leaves them uncrossed, and its writings put the units at chance (44 of 400).
- The terrain, not the contact, removes it: the plain tower with the arithmetic tower's declaration
  fails on the mixed terrain as the pair towers do. Nor is it the amount of digit text alone: the
  eight-times tower met 7 × 216,131 bytes of equations, 58% of the arithmetic tower's 12 × 216,131,
  and crosses no better than the first-terrain towers, which met 12 × 54,016.
- On the mixed terrains the lower level gathers its energy into few modes whose moves every digit
  makes alike, and the gathering grew with the passes (5.7 modes at pass 1, 1.6 at pass 7, mode 16
  holding 0.79 with a move 0.027 the digit's). The energy that would carry the crossing sits where
  the arriving digit cannot act on it: the friction is all on a strand the digit does not turn, so
  the knot slips. On the digits alone the energy spreads over 23 modes the digits move differently.
- No single mode turns as a character of the ring of ten in any tower. The crossing the arithmetic
  tower reads is distributed over its modes; a read of one mode's phase would not find it.
- [derived] The strands are there to be crossed. At `B` the lower state reads `a₀` in 476 of 495 and
  `b₀` is the class arriving, so a bilinear form of the state against the arriving class reads the
  sum at the rate `a₀` reads: for each arriving digit `d` the sum's units are the permutation
  `a₀ ↦ a₀ + d` of `a₀`. The missing term is that form, the situated pool `top ⊗ x̂`.

**Decided next** [agent-inferred]: the loop already decided after the pair forms' second pass, the
situated pool `top ⊗ x̂` founded by the
[effective tension's](2026-10-24_WHAT_A_CONTACT_CANNOT_BRIDGE_IS_ITS_EFFECTIVE_TENSION_AND_THE_TENSION_FOUNDS_THE_FACE_THAT_CARRIES_IT.md)
law and read by the exact Gram before any of it enters the learner, now has a located consumer and
a fixed acceptance: on the mixed terrain its founded forms read a sum's units at `B` in at least 370
of the 495 held-out sums, the arithmetic tower's own crossing. It is the crossing of a carried strand
with an arriving class in every medium, not a digit routine: the pair forms in the learner join only
the last two classes, which at `B` are `b₀` and the class before it.

**The run.** The release binary `modes1` (`25db693e…`) built in 346.6 s (projected 377 s from the
larger of the last two builds, 0.92; deadline 450 s, peak 2.5 GiB). Every mode read ran at one
thread, four at a time: 3.8 to 11.0 s a text against deadlines of 60 to 120 s (the first planned at
one to three minutes), peak 18 to 22 MiB; `MODES_READS.tsv` lists each reading's state, text, cells
and SHA-256 (the readings themselves, 12 to 146 MB, stay outside the repository). The equation
block was read in eight consecutive parts of 2,819 lines (the last 2,818), each from rest. The
mixed tower's probes took 122.7 to 142.0 s against 272 s projected (0.45 to 0.52; deadline 450 s);
the arithmetic tower's 133.6 to 157.6 s against 142.0 s, the largest measured (0.94 to 1.11, the
sums over the projection and inside the 160 s deadline); the first-terrain towers' 135.2 and
139.3 s against 157.6 s (deadline 200 s); peak 310 to 335 MiB each. The flux reads with each
mode's kept share took 9.2 to 10.5 s (planned at one to three minutes; deadline 180 s; peak 680 to 690 MiB), the turns reads 4.2 to 7.2 s. The tower's tests (35) passed in 215.5 s with their build
against 300 s projected (0.72; deadline 360 s, peak 4.5 GiB). The gate's first run filled the disk
at its fourth step (the linker died with a bus error); with the 5.3 GB incremental cache it wrote
removed and none written, it passed every step in 681.9 s against 618.3 s projected (1.10;
deadline 800 s, peak 4.5 GiB).

## The situated pool

The step decided above founds forms `c = (aᵀŝ)(bᵀx̂)` (the state a class meets, level 0's carried
modes before the move, crossed with the arriving class's encoding and its unit) on the covector the
tower's own reverse sends to each cell's input, `y = δx⁰` (`Tower::read_input_covectors`): the
tension of every later face in the cell's section carried back to where the class arrived.
Summed by class, it is the encoding's covector (the test
`the_input_covectors_sum_to_the_encodings_covector`). The moments `Σŝ`, `Σy`, `Σŝŝᵀ`, `Σŝyᵀ` per
arriving class and `Y = Σyyᵀ` are written once (`read-tower-situated-moments`), so a founding never
reads the text again; the forms are read centred within each arriving class, because the class
alone already bridges its own mean (the encoding's covector).

**Does a sum's units error reach `B` at all?** (`read-tower-input-covectors`, the covector printed at
the probe cells, read by the same exact probe as the modes). From the input covector, held out:

| role | `a₀` | `b₀` | `c₀` |
|---|---|---|---|
| `A` (the first operand's units arrive) | 343 | 213 | 125 |
| `B` (the second operand's units arrive) | 117 | 174 | 208 |
| `E` (`=` arrives) | 96 | 118 | 294 |
| `U` (codes the result's units) | 76 | 73 | 494 |

(of 495; commonest 62, 57, 63; `COVECTOR_PROBE.txt`, coordinates released by `2^10`). The state at `B` reads `c₀` in 134 (the section above). The error at the units, read
in 494 of 495 where it is made, still reads in 208 at `B` after its transport back through `E`: the
tension that would cross the operands reaches the tick where they can be crossed. A lookup of the
covector at `B` by `(operation, a₀, b₀)` removes 10% of its within-class energy there (`UNITS_LOOKUP.txt`).

**Three criteria, and what they founded first.**

| criterion | text | train | held out | serves |
|---|---|---|---|---|
| energy (least squares of `−y`, the identity metric) | slice | 30‰ | −16‰ | `g`, `t`, `u` |
| energy | whole text | 1‰ | 0‰ | `o`, `i`, `r`, `l` |
| per-class code weights `ω_u ∝ n_u/t_u` | slice | 2‰ | −12‰ | `y`, `.` |
| code saved to second order in the tension's own metric (`Y⁻¹`) | slice | 200‰ | −8,273‰ | `g` alone |

None served a digit, and the last two lost code held out.

**The located cause: the reading started in silence.** Each criterion's moments were read in eight
streams, each from rest. Each level's read is the face's ratio to its power (`ratio_to_power`),
whose adjoint divides by that power (`ratio_adjoint`). Just after rest the modes hold one or two
pushes and the power is near zero, so the covector a cell's input receives carries the inverse of a
near-silent loudness. Read from rest at the slice's second cut (`ENERGY_FROM_REST.txt`), the stream's first two cells carry
`1.41·10⁸` and `1.66·10⁸` (in the covector's unit squared) against a median cell's 15.4; its first
ten cells hold
998‰ of the stream's whole tension energy, `g` and `a` (the first two classes after the cut) 908‰
of it. Read as one passage, where only the text's own first cell opens from rest (`ENERGY_ONE_PASSAGE.txt`),
the same slice's energy is 26.7 a cell, the mean 1.9 times the median, the largest cell 0.7‰ of the whole, and no
place in the section holds more than its share. Every founding above fitted the few cells after
each cut: the energy criterion their letters, the code-weighted one the same cells reweighed, and
the canonical one the directions those cells alone fill, which the held-out text's cuts (other
letters) do not share.

**The repair** [agent-inferred, October 24]. Each stream after the first now opens one section
before its cut, from rest, and counts none of that section's cells (`read_moments`): the section
brings the stream to the loudness the text keeps, as the learner's own streams are after their
first section. The text's own start stays at rest. With the repair, on the slice the canonical
criterion's first form saves 63‰ and loses 47‰ held out, serving `n` (the slice's 111,811 cells
are too few for a form over 128 state coordinates against 64 tension coordinates
[agent-inferred]). On the whole training text (1,789,108 cells, 171 classes) it saves 96‰ and 106‰ held out, and serves the
digits: `3` 304‰, `4` 239‰, `2` 149‰, `5` 131‰, `1` 74‰, `6` 56‰ of its saving. The tension's own
metric is well conditioned (the training eigenvalues of `Y/N` span 0.049 to 2.18, and the held-out
text's energy along each is 0.90 to 1.06 of the training's).

**Sixteen forms on the whole text.** Founded one rank at a time (`found-tower-situated`, 16 ranks),
the canonical share grows on both texts. The held-out text keeps pace with the training text to
rank 13 and falls behind after it:

| forms | 1 | 2 | 4 | 8 | 12 | 16 |
|---|---|---|---|---|---|---|
| train | 96‰ | 147‰ | 221‰ | 334‰ | 423‰ | 510‰ |
| held out | 106‰ | 194‰ | 261‰ | 338‰ | 427‰ | 469‰ |

The first two forms serve the digits (`3`, `4`, `2`, `5`). From the third they serve `s` and `=`,
from the sixth `g`, then the letters `a`, `r`, `d` and `n`. At sixteen forms the six classes
carrying most of the training share are `s` 85‰, `=` 81‰, `a` 77‰, `g` 71‰, `3` 68‰ and `n` 60‰ of
it. A founding resumed from the first four forms (`FROM`) reproduces the fifth form's line and both
shares exactly (248‰ and 276‰).

Read at the probe cells (`read-tower-situated`, the sixteen forms' values, probed as the modes are;
held out, of 495):

| role | `a₀` | `b₀` | `c₀` |
|---|---|---|---|
| `A` | 481 | 39 | 37 |
| `B` | 113 | 481 | 75 |
| `E` | 163 | 400 | 68 |
| `U` | 110 | 134 | 53 |

(commonest 62, 57, 63). The forms tie each operand where it arrives, `a₀` at `A` and `b₀` at `B`,
each in 481. The sum's units at `B` grow with the forms, 49 at four, 52 at eight, 62 at twelve and
75 at sixteen (`SITUATED_PROBE_r{4,8,12,16}.txt`), against the acceptance's 370. The step's claim is not met.

**What a crossing at `B` could carry.** Under the founding's own criterion, a lookup of the
covector at `B` (the eight parts of the training text's equation block, read from rest, first
sections left out) by `(operation, a₀, b₀)`, centred on the arriving class, carries at most 84.3‰
of the text's canonical tension, and by `(operation, c₀)` 78.5‰ (an exterior reading,
`CROSSING_CEILING.py`). Its directions carry 26.2, 15.7, 8.6, 5.3, 4.6 and 3.6‰, then less; by
`(operation, c₀)` 24.8, 15.4 and 8.0‰. The first is the size of a founded rank (16 to 30‰ at ranks
10 to 16). These lookups take sums, differences and products together; for the sums alone the
crossing is smaller than any founded form (the correction below).

**The crossing is phase.** For the 8,986 sums among those cells, the covector at `B` (whitened by
`Y`, its arriving class's mean removed) is averaged per `c₀` and read in the plane of the means' top
two directions. Its angle increases with the units: `0` 165°, `1` 175°, `2` 196°, `3` 204°, `4` 249°,
`5` 335°, `6` 353°, `7` 361°, `8` 365°, `9` 366°, about half a turn from `0` to `9`, with `4` and `5`
near the centre. Against the characters `d ↦ e^(2πikd/10)` of the ring of ten, the means align
0.743 with `k = 1` (0.477 with the reversed turn, 0.435 with `k = 2`; the alignment is
`|Σ z_d e^(−2πikd/10)| / Σ|z_d|`). The sum's units are a character product,
`e^(2πik c₀/10) = e^(2πik a₀/10) · e^(2πik b₀/10)`: a complex rank-one form of the state that
carries `a₀` and the class arriving as `b₀`. A real form is `f(a₀) g(b₀)`, and the real part of a
character product is `cos·cos − sin·sin`, two real products: one real form holds at most half of
the character's square, about 13‰ of the 26‰ offered [agent-inferred], below the letters' 16 to
30‰. Code length founds the letters first.

**What it says** [agent-inferred]:
- A loudness normalization makes the circuit's sensitivity inverse to its loudness. Near silence a
  push moves the read by far more than it does at the text's loudness, and the covector, read
  back through the same normalization, is that expansion seen from the output side. A tension read
  from rest measures the circuit's waking, not the text.
- The knot at the units is a phase. Each strand is tied where it arrives, and the crossing slips:
  a real form grips one face of the turn while the other face slides past it. A real form ties
  two strands; a complex form ties their phases.

**Decided next** [agent-inferred]: complex situated forms. A form keeps its factors complex,
`c = (aᵀŝ)(bᵀx̂)` with `a`, `b` over the Gaussian integers, and both its faces are read as channels,
`Re c` and `Im c`. The search maximizes the canonical share of the form's two faces together, the
circular criterion `‖𝕄w‖²_(Y⁻¹) / wᴴQw`. Each rank starts from the unit and from a ring, the top
two directions of the class-crossed tension against its class-weighted Gram, `a = e₁ + i e₂`, and
founds the start with the larger exact training share. A form whose two faces are one reading
(their squared correlation within `2^(−15)` of one) keeps the larger, so a complex form costs a
second channel only where its second face reads something the first does not. The acceptance
stays: the founded forms read a sum's units at `B` in at least 370 of the 495 held-out sums.

**The runs.** The binaries `situated1` to `situated6` were built in release; `situated6`
(`fa381fdc…`, the warm start and the resume) in 238.1 s against 230 s (1.04; deadline 400 s, peak
1.7 GiB). On the training slice, from rest: the energy founding's two forms took 91.2 s (planned at
one to three minutes; deadline 240 s; peak 371 MiB); the code-weighted founding's moments 18.0 and
8.5 s (deadline 120 s each) and its two forms 203.8 s, against a projection of two ranks at 31.6 s
(3.2 times; inside the 240 s deadline, but its first rank took 126.8 s, four times the 31.6 s a
rank, and the run was not stopped, against the early-stop standard); the canonical founding's two forms 74.1 s
(deadline 240 s). The energy founding on the whole text (24 forms, projected 1,260 s, deadline
1,300 s) read its moments in 305.5 s and was stopped by hand after its first rank, at 366.2 s: that
form's 1‰ located the criterion's defect, not the run's limit. The tension read from rest over the
slice took 62.0 s (deadline 120 s). The input covector at the probe cells took 15.0 to 15.9 s a block
and 6.8 s held out, four at a time (projected about 40 s and 9 s; deadline 90 s; peak 23 MiB); its
probe 8.8 s (deadline 180 s). With the warm start: the slice's moments 19.0 s (projected 20.2 s;
deadline 60 s), the held-out moments 8.6 s (9.1 s; deadline 40 s); the slice founding stopped at its
240 s deadline after its first rank took 167.7 s at 27 steps, 4.8 times the 34.8 s a rank measured
before, and is reported here as stopped, not relaunched. The whole text's moments took 288.1 s
against 301 s projected (0.96; deadline 400 s; peak 553 MiB), its first rank 70.3 s (deadline
240 s). The sixteen ranks took 1,826.4 s against 2,688 s projected (0.68; deadline 2,700 s; peak
299 MiB); the fourteenth rank took 212.5 s at 30 steps, past the 168 s a rank its own stop rule
named, and the run was not stopped: a lapse of the declared rule, recorded here. The resumed
fifth rank took 144.1 s against 152.5 s (0.94; deadline 400 s). The forms' reads at the probe
cells took 4.4 to 10.4 s each (deadline 60 s; peak 22 MiB), their probe 1.9 s (deadline 180 s), and
the three exterior crossing reads under a minute together (deadline 180 s each). The moments
(45 MB training, 32 MB held out), the covector reads and the forms' reads stay outside the
repository;
`SITUATED_RUNS.txt` keeps every run's log line, and `SITUATED_FORMS16.txt` the sixteen forms. The gate
passed every step in 659.3 s against 701 s projected (0.94; deadline 800 s, peak 4.5 GiB).

## Complex forms, and where the crossing's share goes

**Complex forms** [agent-inferred, October 24]. `found-tower-situated` now founds complex forms.
- `a` and `b` are over the Gaussian integers, and both faces of `c` are read as channels.
- The search uses the circular criterion `‖𝕄w‖²_(Y⁻¹) / wᴴQw`.
- Each rank is searched from two starts and founded from the one with the larger exact training share:
  - the unit;
  - a ring: the top two directions of the class-crossed tension against its class-weighted Gram, `a = e₁ + i e₂`.
- A form whose two faces are one reading keeps the larger.

`read-tower-situated` prints a form's kept faces, `Re c` before `Im c`. On the whole training text (`COMPLEX_RUNS.txt`):

| forms | start | channels | train | held out | the classes carrying most of the training share |
|---|---|---|---|---|---|
| 1 | ring | 2 | 97‰ | 108‰ | `3` 303‰, `4` 237‰, `2` 149‰, `5` 132‰ |
| 2 | ring | 4 | 153‰ | 195‰ | `=` 306‰, `3` 195‰, `4` 153‰, `2` 97‰ |
| 3 | ring | 6 | 200‰ | 266‰ | `=` 236‰, `3` 170‰, `4` 138‰, `2` 103‰ |
| 4 | unit | 7 | 242‰ | 288‰ | `=` 195‰, `s` 170‰, `3` 140‰, `4` 114‰ |

Four real forms saved 221‰ and 261‰. Read at the probe cells, the four complex forms tie each operand where it arrives: `a₀` at `A` in 247 and `b₀` at `B` in 223. They read a sum's units at `B` in 50 of the 495 held-out sums (`SITUATED_PROBE_c4.txt`); four real forms read 49.

The founding was launched for eight forms. It was stopped by hand during its fifth rank on this reading. The stop was declared while the run was going, once its 75-minute projection had been questioned: if three or four complex forms did not clearly read more than four real ones, the run would stop there.

**The state carries the phase.** This is an outside reading (`CHARACTER_AT_B.py`) of level 0's modes before the second operand's units arrive. It covers the 9,018 true sums of the training equation block and the 495 held out. Each coordinate is released to `2^(−10)`, with one unit of ridge.
- A straight-line read of that state holds 966‰ of the variance of the first operand's units character `e^(2πi a₀/10)`, held out.
- The root nearest the read is `a₀` in 484 of 495.
- Ten indicator fits read `a₀` in 494.
- The character `k = 3` is held at 897‰.

**One form reads the units.** Take the complex form whose `a` is that read and whose `b` gives each digit its character. Off the digits, `b` is drawn towards zero on every other class, weighted by its count. This is an exterior construction (`IDEAL_FORM.py`; the form is in `IDEAL_FORM_quiet.txt`), not a founded form. The machine's own `read-tower-situated`, probed as the founded forms are, reads a sum's units at `B` in 475 of 495 (`IDEAL_PROBE.txt`). With a second such form at `k = 3`, the exterior read gives 492. So the shape the step decided can carry the acceptance with one form.

**The founding's own measure gives it 3 to 4‰** (`IDEAL_SHARE.txt`).
- Alone, it saves 3‰ on the training text and 5‰ held out; with `b` left free off the digits, 4‰ and 4‰.
- After the four founded forms it adds 3 to 4‰: 242‰ becomes 245‰ or 246‰.
- Each founded form saved 16‰ to 100‰.

**Where the share goes** (`FORM_DILUTION.py`, `CROSSING_AT_U.py`). The covector is taken at the probe cells, read from rest in the eight parts with their first sections left out, against the whole text's `Y`. Shares are in the founding's unit, in which the text's whole tension is 64.

| sums' cell | tension per cell, against the text's mean cell | the cells' tension within their class | the exact crossing `χ(c₀)` | its part of the cells' own | any function of `c₀` |
|---|---|---|---|---|---|
| `A` | 0.49 | 130‰ | 3.0‰ | 23‰ | 5.2‰ |
| `B` | 0.67 | 209‰ | 6.7‰ | 32‰ | 11.9‰ |
| `E` | 0.56 | 178‰ | 7.5‰ | 42‰ | 12.9‰ |
| `U` | 0.18 | 54‰ | 9.7‰ | 180‰ | 22.3‰ |

- **The crossing is a small part of the tension, even where it lives.** At `B` it is 32‰ of what the cell receives, and the sums' `B` cells are quieter than the text's average cell. At `U`, the cell that codes the units, it is 180‰ of the cell's tension, but that cell is a near node: 0.18 of the mean.
- **The form fires wherever a digit arrives.** Its `B` cells hold 0.2‰ of its within-class energy over the whole text, and its ten digit classes 171‰. The rest lies on the other classes, where `b` is drawn towards zero but does not reach it. The canonical share divides what the form reads at `B` by everything it carries. Were it to read only the crossing, its share would be about `6.7‰ · 0.0002`, near 0.001‰. The 3 to 4‰ it shows is what it happens to read elsewhere [agent-inferred].
- **At `U`, the two strands are read separately.** Before the class arriving at `U`, the state carries `b₀`'s character at 973‰ and `a₀`'s at 778‰. The product of the two reads gives the units in 304 of 495. A form of the state with itself reads less at `U` than the state crossed with the arriving class reads at `B`.

**A correction.** "What a crossing at `B` could carry" above read its lookups over sums, differences and products together. For the sums alone, a lookup by `c₀` at `B` carries 11.9‰ and the exact character 6.7‰. That is below every founded form, not the size of one. Its sentence "the crossing is large enough to be founded" is withdrawn. So is the estimate in "The
crossing is phase" that a real form holds about 13‰ of the 26‰ offered: that figure, too, rests on
all three operations. The complex forms hold the whole character, and they did not read the units
either.

**What it says** [agent-inferred]:
- **The knot is present, and one form ties it, but the founding does not choose it.** Its criterion is one global share: what a form saves of the whole text's tension. The crossing is a few thousandths of that, placed at cells quieter than the text's mean, and a form of the state and the arriving class spreads over every digit. Code length founds the letters, `=` and the digits' arrivals first; the crossing would come after all of them, if at all. This makes the earlier reading quantitative: the terrain, not the contact, removes the crossing.
- **Read as the circuit.** The units' error is made at a node of the tension (`U`, 0.18 of the mean). Carried back to `B`, it is a thirtieth of what `B` receives. A criterion that weighs every cell by the whole text's tension hears the antinodes, and averages away the node where this knot sits.

**Decided next** [agent-inferred]: the selection law, not more ranks.
- The receipt law reads a receiver's readings per region, each in its own frame and over its own ticks, never as one global scalar. The founding's criterion is one global share.
- The next loop reads the tension per region, each region at its own loudness, with the regions taken from the tower's own state rather than from a label.
- Its first step is an outside reading: does level 0's state separate the cells where a sum's crossing lives from the text's other digit arrivals?
- The acceptance stays.

**The state marks the place** (`LOCK_AT_B.py`, the first reading of that loop). It covers the 8,239
cells of the held-out equations where a digit arrives: 1,253 are second operands' units, 495 of them
sums'. Each is read in level 0's state before the digit arrives (the full mode read of every cell).
- The loud mode 16 holds 76% of the energy at those cells and carries little of the place.
- The place is in the relative phases of quiet modes. The relative phase of modes 57 and 35, in 16
  sectors, carries 0.71 of the information of "a second operand's units arrive here" (0.438 of
  0.615 bits). One of its sectors holds 35% of those cells and no other digit arrival.
- For the sums alone, modes 42 and 35 carry 0.64 of it. One sector holds 91% of the sums' `B`
  cells, at precision 0.62.
- For scale, a straight-line separator fitted on the even lines and read on the odd ranks them at
  0.92 (all three operations) and 0.91 (sums).
- [agent-inferred] The address the crossing needs is carried by the tower, as a pair of modes'
  relative phase: a lock in the elementary objects' sense (a pair contact's address), not a label.

**The runs.**
- The binary `situated7` (`25f4309f…`, the complex forms) built in 238.1 s against 238 s (1.00; deadline 400 s; peak 1.7 GiB).
- The first complex rank, a timing read, took 97.3 s. It was planned at up to 640 s (a real rank's 213 s and a ring search at up to twice a real step), with a deadline of 700 s; peak 265 MiB.
- The eight-form founding resumed from that rank. Its projection was 4,463 s (seven ranks at 637.5 s), with a deadline of 4,500 s, and a rank past 640 s would have stopped it. Ranks two to four took 314.0, 98.6 and 123.5 s. It was stopped by hand during the fifth at 713.3 s (peak 282 MiB), on the reading above.
- The forms' reads at the probe cells took 7.1 to 15.7 s beside the founding (deadline 60 s), and their probe 1.4 s.
- The modes at the sums' `B` and `U` cells took 3.8 to 8.8 s per text (deadline 60 s).
- The four outside readings took 3.5 to 11.1 s (deadlines 180 to 300 s).
- The one form's share took 2.3 to 3.8 s (deadline 60 s), its reads 3.5 to 8.4 s and its probe 1.0 s.
- The lock reading took 5.0 s (deadline 300 s).
- The gate passed every step in 690.4 s against 659 s projected (1.05; deadline 900 s, peak 4.4 GiB).

The mode reads stay outside the repository. The forms and every log line are in the receipts, and each run's row is in `RUNS.tsv`.

## The crossing at its own loudness

**The readings** (`REGION_SHARE.py`, `REGION_FOUNDING.py`, `TURN_FORMS.py`, `CLASS_MODES.py`,
`MODE_PARTNER.py`; all exterior). They cover the 147,775 digit arrivals of the training equation
block, read from rest in its eight parts with cells from 128.
- At each arrival they take level 0's state before the digit arrives and the covector at the input.
- Each region is read against its own `Y_r` (uncentred), so its whole tension is 64, as the text's
  is in the founding's unit.
- Forms are centred within each digit inside the region.
- Held out, a form is read as the machine reads it: its channels uncentred, a ridge indicator fit at
  the training sums' `B` cells of the region, and 0 at held-out cells outside the region.

**The region raises the crossing about forty-fold and still does not put it first.** Over the whole
text the exact crossing `χ(c₀)` at `B` held 6.7‰ (above). Read at each region's own loudness:

| region | cells | the exact crossing | the outside form | best form | its `β` on `k = 0` | best form held out | outside form held out |
|---|---|---|---|---|---|---|---|
| every digit arrival | 147,775 | 0.095 | 0.083 | 0.541 | 0.99 | 48 | 475 |
| the sums' `B` cells (a label) | 8,986 | 0.386 | 0.378 | 1.379 | 0.95 | 42 | 475 |
| lock 42-35, sector 0 | 13,138 | 0.279 | 0.087 | 0.906 | 0.96 | 34 | 440 |
| lock 57-35, sector 6 | 7,817 | 0.264 | 0.278 | 0.941 | 0.93 | 45 | 268 |

- Lock 42-35's sector 0 holds 8,088 of the 8,986 training sums' `B` cells (0.62 of the region) and
  449 of the 495 held out.
- The best form is the same from the unit, ring and outside starts in every region. Its class factor
  is constant: a read of the state alone.

**Twenty-four forms founded in the lock region** (each rank residualized on the forms before it).
- The joint share reaches 6.98, and the crossing left falls from 0.279 to 0.140.
- Held out, the units at `B`: 35 (one form), 77 (four), 97 (sixteen), 122 (twenty-four).
- No form's class factor is a character: its largest non-zero character holds at most 0.46.
- Founded after the state's own read (128 channels common to the digits, share 5.14), four forms
  read 76; in the label region the same founding failed on a singular Gram.

**The turn alone is not the separation.** With the class factor held to unit modulus, the search
converges to a constant phase (share 0.41 to 0.83, held out 36 to 51). The leading form's two
channels hold at most 0.022 of the result's size (`log₁₀`) and of `χ(a₀)`; in the label region,
0.156 of the size.

**After the state's own read, the digits' coupling is the ring of ten.** Take the tension left at
each digit's arrivals once the state's common read is removed. The digits couple through it as
`K_de = tr(Y_r⁻¹ M̃_dᵀ S̄⁻¹ M̃_e)/√(n_d n_e)`. No label enters `K`. Over every digit arrival:

| mode | eigenvalue | its power on the characters |
|---|---|---|
| 1 | 1.016 | `k = 1` 0.84 |
| 2 | 0.636 | `k = 1` 0.78 |
| 3 | 0.499 | `k = 2` 0.54 |
| 4 | 0.394 | `k = 2` 0.41 |
| 5 | 0.236 | `k = 2` 0.46, `k = 5` 0.40 |
| 6 | 0.223 | `k = 3` 0.76 |
| 7 | 0.169 | `k = 3` 0.64 |
| 8 | 0.132 | `k = 4` 0.79 |
| 9 | 0.117 | `k = 4` 0.55 |
| 10 | 0 | `k = 0` 0.99 |

- The modes come in the characters' order of frequency, the first character first.
- The first pair leads in every region read: the lock region (0.69, 0.57), the sums' `B` cells
  (0.80, 0.93) and the `B` cells of all three operations (0.81, 0.64).
- The state's own read leaves the crossing whole: 0.279 of 0.279 in the lock region.

**The state's side is not located.** The form whose class factor is modes 1 and 2, with its top 1,
2, 4 and 8 state reads together, reads the units at `B` held out in:

| region | 1 | 2 | 4 | 8 |
|---|---|---|---|---|
| every digit arrival | 79 | 65 | 83 | 104 |
| lock 42-35, sector 0 | 51 | 78 | 103 | 127 |
| the sums' `B` cells (a label) | 40 | 67 | 109 | 232 |

- With each digit's own offset read beside the channels, the counts move by up to 14 over every
  digit arrival, 16 in the lock region and 36 in the label region (109 to 145 at four reads; 238 at
  eight). The arriving digit alone reads 32; the outside form with offsets read away, 477.
- The four state reads paired with the first-character mode, in the label region, hold at most 0.21
  of `χ(a₀)` and at most 0.14 of `χ(a₁)`, `χ(b₁)`, `χ(c₁)` or the carry, fitted on even lines and
  read on odd (`MODE_PARTNER.txt`). The outside form's read holds 0.966 of `χ(a₀)`.

**What it says** [agent-inferred]:
- **The loudest relation at `B` is the state with itself.** At every region's own loudness it is
  larger than the crossing, so any criterion of tension founds it first. The region raises the
  crossing but does not reorder the antinodes.
- **The arriving side of the knot is located by the tension**: the digits' ring of ten, its first
  character first, found without a label.
- **The carried side is not.** The read the crossing needs, the first operand's units, is
  privileged by what the state carries (966‰), not by the tension it leaves. The tension's own
  partner reads are mixtures, so the knot still slips there.

**Decided next** [agent-inferred]:
- The class factor comes from the coupling's modes, as located here.
- The state factor comes from what the state carries of the ring's modes along the passage: each
  earlier arrival's ring character transported to the cell through the state's own modes (a
  phase-carried moment `Σ_k Ĝ(τ_k)⁻¹ β(u_k)`), never an offset or a window.
- Candidates are scored by code length in the lock region. An exterior reading comes first, and the
  acceptance stays.

**The runs.**
- The region shares took 54.5 s and, rerun, 54.8 s (unmeasured, planned at one to two minutes;
  deadline 300 s; peak 1.2 GB). The first run read held-out forms centred within each class by the
  region's means, which distorted the outside form in mixed regions (its output was not kept); the reads above are
  uncentred, as the machine reads them.
- The founding in three regions was projected at about 250 s (deadline 400 s). Its first launch was
  stopped before output on that centring, and its second at rank five on its rate: 1.5 to 9.6 s a
  rank against about 3 s projected. It was relaunched with the partition changed to the lock region
  alone (`REGION_FOUNDING_stopped.txt` keeps the stopped ranks).
- The lock-region founding of 24 ranks was projected at 260 s (30 s and 24 ranks at 9.6 s; deadline
  300 s) and took 143.6 s (0.55; peak 805 MiB).
- The turn forms failed at 38.8 s on a singular Gram (a real form's two channels are one reading)
  and, with a pseudo-inverse share, took 47.9 s (projected about 70 s; deadline 300 s; peak 1.2 GB).
- The state-first founding (projected at most 150 s; deadline 300 s) failed at 42.8 s in the label
  region after the lock region's four ranks (peak 805 MiB).
- The class modes took 37.5, 40.1 and 39.0 s, and the label regions 36.4 s (under a minute
  projected; deadline 180 s; peak 1.2 GB). The mode partner took 33.2 s (deadline 180 s; peak
  806 MiB).

## The carried turns

A digit's character `χ(d) = e^(2πi d/10)` has modulus one: a pure turn. A read of the state that
carries one earlier arrival's character turns without boosting, so its modulus is the same at every
cell. `CARRIED_TURN.py` and `CARRIED_SELECT.py` (exterior) ask only that, with no label and no
arrival index: over a region's cells, minimize `E(|aᵀŝ|² − 1)²` over complex reads `a`, with the
state whitened in the region (Godard's constant-modulus criterion). Components are found one after
another, each decorrelated from the reads before it, each from a fixed start. Labels enter only to
read what each component turned out to carry.

**The state carries its earlier arrivals as turns, and a blind criterion finds them.** In the lock
region (16 components; the fraction of each character's variance a component holds at the sums' `B`
cells, where that digit is present, fitted on even lines and read on odd):

| component | modulus spread | carries | tension `J` with the coupling mode | held out, with the coupling mode / with `χ₁` |
|---|---|---|---|---|
| 1 | 0.028 | `b₁` 0.43 | 0.067 | 36 / 45 |
| 2 | 0.077 | `b₁` 0.23 | 0.043 | 47 / 47 |
| 3 | 0.085 | `b₁` 0.27 | 0.039 | 33 / 38 |
| 5 | 0.178 | `a₁` 0.48 | 0.041 | 47 / 41 |
| 6 | 0.237 | `a₀` 0.36 | 0.054 | 47 / 32 |
| 10 | 0.261 | `a₁` 0.42 | 0.038 | 42 / 41 |
| 11 | 0.256 | `a₀` 0.37 | 0.039 | 51 / 44 |
| the outside read | 0.943 | `a₀` 0.97 | 0.063 | 231 / 440 |

- Each component carries mostly one arrival. The second operand's tens, the most recent arrival
  when present, is the cleanest turn; the first operand's tens and units follow.
- In the label region the first component carries `b₁` at 0.71 with modulus spread 0.016, and the
  fourth carries `a₀` at 0.32 (that run stopped at its deadline after four components).

**The first operand's units are carried as an ellipse, not a circle.** The read that holds 0.97 of
`χ(a₀)` has modulus spread 0.94, and the circular criterion splits `a₀` across components 6, 8 and
11. The tension does not pick it among the turns: the `b₁` turn carries the most (`J` 0.067; the
outside read 0.063; the best `a₀` turn 0.054).

**The lock region's class factor halves the read.** Its coupling mode is 0.79 on the first
character. With it the outside read gives 231 held out; with `χ₁` exactly, 440.

**What it says** [agent-inferred]:
- The carried side of the knot is made of turns the machine can find blindly, one arrival each. A
  turn is cleanest when its arrival is most recent. An older arrival comes back as an ellipse: its
  character has been carried through modes that turn and decay at different rates, a turn composed
  with a boost (the swing's factoring).
- So the read the crossing needs is a turn only after the transport since its arrival is undone.
  This is the phase-carried moment `Ĝ(τ)⁻¹E(u)` read literally: the receiver un-transports by the
  navigators' own clock.

**Decided next** [agent-inferred]: the transported turn. Locate each arrival's turn where it is
cleanest, one tick after it arrives. Carry that read to the later cell through level 0's own mode
transport, and measure its modulus and what it reads there. An exterior reading comes first, and
the acceptance stays.

**The runs.**
- The turn reading was planned at under a minute (deadline 180 s; peak 805 MiB). The lock region
  took 112.2 s for eight components, and the run stopped at its deadline in the label region after
  four. It is reported as incomplete (`CARRIED_TURN.txt`), and the next reading changed the
  partition (the lock region alone) and capped each component's search at 120 steps.
- The selection reading was projected at 121 s (25 s to load and up to 6 s for each of 16
  components; deadline 180 s). It took 107.2 s (0.89; components at 4.5 to 4.9 s each; peak
  806 MiB).

## The ring's sense, and the end of the search at `B`

**Read in its own complex modes, the coupling still has no sense of turn** (`HANDED_RING.py`,
exterior). Here the state is read as level 0's 64 complex modes `h`, and a state read is
holomorphic, `r = bᴴh`, so it turns with the modes. The coupling `K` is then Hermitian. Its top two
modes still split the first character and its conjugate about equally:

| region | mode 1 on `k = 1` / `k = 9` | mode 2 on `k = 1` / `k = 9` |
|---|---|---|
| every digit arrival | 0.42 / 0.43 | 0.38 / 0.37 |
| lock 42-35, sector 0 | 0.31 / 0.37 | 0.27 / 0.26 |
| the sums' `B` cells | 0.39 / 0.42 | 0.47 / 0.45 |
| the differences' `B` cells | 0.45 / 0.49 | 0.48 / 0.45 |

**The state carries each arrival in both senses.** At the sums' `B` cells, a holomorphic read holds
0.84 of `χ₁(a₀)` and 0.85 of `χ₉(a₀)`, its conjugate (0.92 and 0.91 in the lock region). Each
mode's move is real-linear, `h ↦ λh + βh̄`: the pump's conjugate term carries the arrival in both
senses at once. Each read crossed with its own character reads the units held out: `χ₁(a₀)` with
`χ₁` in 355 (383 in the lock region), and `χ₉(a₀)` with `χ₉` in 340 (370). A read crossed with the
other sense reads 35 to 43. So the sense of turn is fixed only in the pairing of a read with a
class factor.

**Held to the ring's pair, the joint search still finds mixtures** (`RING_SPAN.py`). The class
factor is held in the span of `K`'s top two modes, which has no constant, so a read of the state
alone is excluded. The holomorphic read is searched jointly with it, and four ranks are founded one
after another:
- Each class factor balances `k = 1` and `k = 9` (0.20 to 0.44 on each, one rank 0.27 / 0.48), a
  real factor rather than a turn.
- No read holds more than 0.14 of `χ₁(a₀)`.
- Held out, the four ranks together read 74 in the lock region and 61 in the label region.
- The leading rank's `J` is 0.27 in the lock region. The outside `a₀` form's was 0.063.

**What it says** [agent-inferred]:
- At `B`, the units crossing is not the leading relation of the ring in any refinement read: whole
  text, per region at its own loudness, with the class factor taken from the coupling, as a turn,
  in the state's complex modes, or held to the ring's pair. The search at `B` is closed.
- The tension at `B` is the downstream error carried back to the input. The crossing becomes the
  error at `U`, the cell that codes the units. There it is the largest part of a cell's own tension
  (180‰), but `U` is a near node (0.18 of the mean), and the two operands' units are both carried
  strands (`b₀` at 973‰, `a₀` at 778‰). The knot sits at the node, as a crossing of two carried
  strands, not of the state with the arriving class.

**Decided next** [agent-inferred]: read the crossing at `U` at its own loudness, as a form of the
state with itself, `c = (aᵀŝ)(a′ᵀŝ)`, with the region taken first from the label and then from the
tower's own lock. This is an exterior reading first. The acceptance's cell `B` stays; a form found
at `U` would be read there too, and the acceptance is not moved.

**The runs.**
- The handed ring was unmeasured and planned at about 40 s (deadline 180 s). It took 114.3 s (2.9;
  four regions at 17.7 to 23.6 s each; peak 1.3 GiB) and finished inside its deadline.
- The ring-span search was projected at about 45 s (deadline 180 s). It took 73.0 s (1.6; peak
  809 MiB).

## The knot at the node `U`

**The readings** (`U_FORMS.py`, `U_SHARE.py`; exterior). They take the 8,986 training sums' `U`
cells (the cell that codes the result's units; eight parts, each from rest, cells from 128). At
each they read level 0's state before the class arriving at `U`, released as at `B`, and the input
covector there, read for this loop. The region is these cells (a label region, a ceiling), read
against its own `Y_r`. A form of the state with itself is `c = (aᵀŝ)(a′ᵀŝ)`. Held out, forms are
read at the 495 sums' `U` cells.

**At `U` the crossing is the loudest turn.** At its own loudness, the exact crossing `χ₁(c₀)`
holds a share of 1.86 of the 2 its two channels can hold. That is louder than the state's own
leading read (`J` 0.67 against the crossing's 0.93). At `B` the crossing held 0.39 in the label
region, under a read of the state alone at 1.38.

| form at `U` | `J` | two-channel share | holds `χ₁(c₀)` | held out, units at `U` |
|---|---|---|---|---|
| the exact crossing (a label) | 0.931 | 1.863 | 1 | — |
| the outside product, `a₀`'s read × `b₀`'s read | 0.712 | 1.424 | 0.757 | 285 |
| searched by `J`, three starts | 0.932 to 0.938 | 0.95 to 0.97 | 0.00 | 46 to 57 |
| searched by the share, from the outside reads | 0.715 | 1.429 | 0.756 | 282 |
| searched by the share, three blind starts | 0.24 to 0.55 | 0.74 to 0.94 | 0.00 | 42 to 65 |

- The outside product's two reads hold 0.78 of `χ₁(a₀)` and 0.97 of `χ₁(b₀)`.
- Searched by the circular `J`, every start ends on a form just above the crossing's `J` that reads
  nothing: one real channel (a boost) scores under `J` as high as a full turn.
- The two-channel share ranks the crossing first. Searched by it, the outside product stays where it
  is (1.43), and the blind starts stop well below it (299 steps each, not converged).

**What it says** [agent-inferred]:
- The knot is heard where it sits. At the node that codes the units, the crossing of the two
  carried strands is the tension's leading turn, in a measure that counts a turn's two channels.
- Two repairs follow for the founding's selection. Score a complex form by its two-channel share,
  not by the circular `J`. Start the search from the carried turns, not from the state's principal
  directions.

**Decided next** [agent-inferred]: the blind pipeline at `U`, read from outside first.
1. Find the carried turns at `U` by constant modulus.
2. Form their pair products in both senses, `zᵢzⱼ` and `zᵢz̄ⱼ`.
3. Rank the products by two-channel share at the region's own loudness, with the region first from
   the label and then from the tower's lock.

The acceptance stays at `B`: a form of the state with itself is read there on the state after the
second operand's units arrive, when both strands are carried.

**The runs.**
- The covector reads at the `U` cells took 14.7 to 15.5 s a part (deadline 90 s each, four at a
  time). The `B` cells' reads, 15.0 to 15.9 s, were the projection (about 1.0).
- The forms by `J` were projected at about 60 s (deadline 180 s) and took 71.6 s (1.19; peak
  110 MiB).
- The forms by share were projected at about 40 s (deadline 180 s) and took 77.8 s (1.9; peak
  104 MiB).

## The blind reads at `U`, and the distance the demand travels

**The readings** (`U_TURNS.py`, `U_TENSOR.py`, `LAG_AT_B.py`; exterior). The first two take the
8,986 training sums' `U` cells as `U_FORMS.py` does and look for the crossing with no label and no
chosen start. The third splits the sums' `B` cells by the result's length.

**Constant modulus at `U` finds a clock first.** Of 24 blind turns of the state (Godard's criterion,
whitened in the region, each decorrelated from those before it):
- The first turns with a modulus spread of 0.006 and holds nothing of either operand (at most 0.089
  of `χ₁(b₀)`): a clock.
- The rest are mixtures. None holds more than 0.23 of any character `χ_k` (`k` = 1 to 5) of `a₀` or
  `b₀`, where straight-line reads of the state hold 0.78 of `χ₁(a₀)` and 0.97 of `χ₁(b₀)`.
- Their 576 crossings in both senses, ranked by two-channel share, reach 0.13. The first, a `b₀`
  mixture crossed with an `a₀` mixture, reads 85 of 495 held out, and the top 8 together read 103.

**The third moment finds loudness.** The tension's third moment against the state,
`T_ijk = Σ y_k x_i x_j` (state and covector whitened in the region), unfolded as a
`(128·128) × 64` matrix, names the quadratic forms the tension asks for most, in order, with no
start.
- Its leading singular values are 2,960, 2,126 and 1,758, against 514, 435 and 377 for its foil
  (the covectors permuted among the cells): a clear gap.
- Its leading forms hold nothing of `c₀` (0.000). Forms 1 and 2 as one complex form have share 1.15
  and read 38 of 495 held out. The leading 16 together read 55.
- Form 1 is one-signed: its leading eigenvalues are all negative, and two of them hold 0.62 of its
  square, an energy of a few directions. Its variance per cell at unit size is about 1,470 (from
  its singular value and share), where a Gaussian state's would be 2. The raw numerator ranks forms
  by their loudness: the circular `J`'s fault in another dress.

**The demand reaches `B` turned by the distance it travels.** The covector at `B` is the downstream
error carried back to `B`'s input. `U`'s error crosses the `=` and the result's digits before its
units to get there, so the result's length sets how far it travels. Split by that length (a label
of the passage after `B`), each part read in its own `Y_r`:

| the sums' `B` cells | cells | `χ₁(c₀)` share | its foil | `χ₁(b₀)` share |
|---|---|---|---|---|
| pooled | 8,986 | 0.386 | 0.014 | 0.315 |
| result of two digits | 4,503 | 0.679 | 0.023 | 0.477 |
| result of three digits | 4,431 | 0.726 | 0.034 | 0.377 |

The 52 sums with a one-digit result are too few for a 64-dimensional tension. The foil permutes the
characters among each part's cells.

**What it says** [agent-inferred]:
- Every blind criterion over the state alone at `U` is held by the state's own loud geometry: clocks
  under constant modulus, energies under the raw third moment, boosts under the circular `J`. The
  two strands the crossing needs are quiet and spread across many directions.
- Within one distance the covector at `B` holds the crossing at 0.68 to 0.73; pooled over the two
  distances it holds 0.39. The transport turns `U`'s demand by an amount that depends on how many
  cells it crosses, and the two turns cancel about half of it.
- This is the gradient as it is, not a fault of the reading. A form placed at `B` reaches `U`'s
  reader turned by the same distance, so with the present transport a form at `B` serves `U` only
  as far as its turn is the same for both distances.

**Decided next** [agent-inferred]: read how each mode carries from `B` to `U`, with its move and
pump at every cell between them (`read-tower-modes` at the `=` and the result's digits). Find the
modes whose carry is the same for both distances. A crossing placed in those modes reaches `U`
whole, and the crossing's share at `B` is then read through them alone. The acceptance stays at
`B`.

**The runs.**
- The blind turns were projected at about 90 s (deadline 120 s) and took 61.4 s (0.68; peak
  183 MiB). Their rerun, reading every character, was projected at about 65 s (deadline 90 s) and
  took 64.3 s (0.99; peak 183 MiB); its output is the receipt. A first launch copied the script into
  the wrong directory and stopped before reading anything.
- The third moment was projected at about 25 s (deadline 60 s) and took 7.2 s (0.29; peak 222 MiB).
- The split at `B` was projected at about 30 s (deadline 60 s) and took 31.8 s (1.06; peak 807 MiB).

## The crossing placed where it carries, founded against the demand at `U`

**The readings** (`CARRY_B_TO_U.py`, `FOUND_AT_B_BY_U.py`, `FOUND_POOL_AT_B.py`,
`FOUND_PLACE_AT_B.py`; exterior).
- Level 0's modes were read in full at every cell between each sum's `B` and `U` (the `=` and the
  result's digits before its units; 22,351 cells, `MK_PATHS.py`). There each mode moves by its own
  move and pump, `h ↦ λh + βh̄`. The carried value equals the move applied to the state before at
  every cell read (largest departure 3·10⁻¹⁰, relative).
- A form placed at `B` reaches `U` as the product of its mode's moves over those cells: two moves
  for a two-digit result, three for a three-digit one.

**One mode carries the crossing alike for both lengths.** The exact crossing `χ₁(c₀)` placed at `B`
in each mode in turn, carried to `U` through that sum's own moves:
- In mode 41 it reaches `U` holding 0.90 of itself pooled (0.91 and 0.94 within the two lengths),
  with share 1.74 of `U`'s tension; the mean carries of the two lengths differ by 0.21 of their
  size. Modes 56 and 48 hold 0.95 to 0.98 within each length but 0.86 and 0.84 pooled.
- In modes 47, 38, 55 and 7 the third result digit turns the carry about half a turn (the two
  lengths' mean carries differ by 1.8 to 2.0): within each length mode 47 holds 0.97 and 0.89, and
  pooled 0.05. These are the antinodes the extra cell crosses; mode 41 is a node.
- One mode holds at least 0.9 pooled, 25 hold at least 0.5, and the median holds 0.46.
- The strands themselves are spread: the mode holding most of `χ₁(b₀)` at `U` (48) holds 0.18 of
  it.

**Scored by the demand that reaches it, the crossing leads at `B`.** A situated form at `B`,
`c_B = (aᵀs_B)β_d` (the state before the arrival, the arriving digit's class factor), is placed in a
mode, carried to `U` through that mode's moves, and scored by its share of `U`'s tension:
- Placed in mode 41, the outside form (`χ₁(a₀)`'s read times `χ₁(b₀)`) takes 1.68 of the 2 its two
  channels can hold. The state at `B` alone, read in straight lines, takes 0.71 in two channels.
- Climbs from blind starts (the principal pair, with the ring's first character or the unit) stop
  at 0.66 after 300 steps and read 39 and 36 of 495 held out. From the outside form the climb stays
  there (1.69, 475 held out).
- Founded as the pool law founds, with no start (the leading generalized eigenvector of a pool's
  demand against its own loudness, one pool for each class factor; the pools are the ring's
  characters, which the coupling found without labels):

| pool at `B`, placed in mode 41 | leading single-channel share | its form holds `χ₁(a₀)` | held out, units at `B` |
|---|---|---|---|
| the unit (the state alone) | 0.706 | 0.008 | 50 |
| `χ₁` | 0.870 | 0.936 | 444 |
| `χ₂` | 0.675 | — | 220 |
| `χ₃` | 0.604 | — | 350 |
| `χ₄` | 0.638 | — | 197 |
| `χ₅` | 0.776 | — | 83 |
| the ten characters as one pool | 0.958 in the sample | — | 140 |

  `χ₃` is a faithful character like `χ₁`, so its form reads the units through `χ₃(a₀)`; `χ₂` and
  `χ₄` read them modulo 5 and `χ₅` their parity. The ten characters as one pool fit the sample
  better and read less held out: their leading vector mixes the characters (weights 0.05 to 0.15).

**The founding chooses the placement and the character itself.** Every pair of a placement mode (64)
and a pool (the unit, `χ₁` to `χ₅`), 384 pairs, ranked by the leading share alone:
- The ten leading pairs are all `χ₁`, in modes 16, 57, 42, 58, 56, 25, 48, 40, 51 and 27 (0.915 to
  0.886). Each other pool's best is lower: the unit 0.835 (mode 15), `χ₅` 0.791, `χ₂` 0.727, `χ₄`
  0.689, `χ₃` 0.649.
- The leading pair's form, `χ₁` placed in mode 16, has a state read holding 0.960 of `χ₁(a₀)` and
  reads the units at `B` in **471 of 495** held-out sums. The acceptance's bar is 370.

**What it says** [agent-inferred]:
- Within the label region and with the ring's characters as its pools, the founding finds the
  units crossing at `B` with no label on the form and no start, once each candidate form is scored
  by the demand that reaches it through its own placement (the `U` cells come from the true sums). Placement belongs to the
  form: a value placed in a node mode reaches `U` alike for every distance, and `U`'s demand reaches
  it whole.
- The pool law's eigenproblem finds what every climb missed. The climbs failed on the landscape,
  not on the criterion.

**What it does not say.** This is an exterior founding, computed outside the machine with its laws.
It used `U`'s demand alone, not every downstream cell's error carried back through the placement;
the region is the sums' `B` cells (a label region); the class factors are the ring's characters.
The acceptance is a claim about the machine's founded forms, and it is not claimed here.

**Decided next** [agent-inferred]: build this into the machine's situated pool founding.
1. Each candidate form carries its placement mode.
2. Its demand is the reverse's covector at that mode at the cell, carried back through the mode's
   own moves from every downstream cell.
3. The pools are the ring's characters, from the coupling's modes.
4. The region comes from the tower's lock.

Then the acceptance is read on the machine's founded forms.

**The runs.**
- The mode reads at the cells between `B` and `U` were projected at 10 to 30 s a part (deadline
  90 s each, four at a time) and took 8.0 to 8.5 s a part (peak 22 MiB).
- The carry was projected at about 40 s (deadline 90 s) and took 16.3 s (0.41; peak 121 MiB).
- The scoring at `B` with its climbs was projected at about 75 s (deadline 120 s) and took 79.1 s
  (1.05; peak 805 MiB).
- The pool founding in mode 41 was projected at about 70 s (deadline 120 s) and took 47.1 s (0.67;
  peak 1.36 GiB).
- The founding over every placement was projected at about 90 s (deadline 150 s) and took 66.8 s
  (0.74; peak 805 MiB).

## The demand at the modes, and the reader the crossing lacks

The decided build needed the machine's own demand at a placement mode. The reverse already has it.

**The reading** (code). `Tower::reverse_joined` carries every later face's demand back through each
mode's own moves. On the way it holds `G_h`, the covector of each level's modes after a cell's
push. A value placed in a mode at the cell changes the code by `Re(conj(G_h) δh)` to first order.
- The reverse now keeps `G_h` when asked.
- `read_input_covectors` hands it beside the input covector (`InputCovector::modes`, level by
  level and mode by mode, on the covector's grain `2^(−24)`).
- `read-tower-input-covectors` prints one level's when given a level.

Nothing else changes: the duplex's reverses ask for none.

**Founded against the modes' own demand, the crossing is not found at `B`**
(`FOUND_BY_MODES_AT_B.py`; exterior, with the machine's moments). The pool law founds each pool's
leading form with `G` (level 0's 128 mode coordinates) in place of the input covector `y`.

| region | demand | pool | leading share | its form holds `χ₁(c₀)` at `B` | held out, units at `B` |
|---|---|---|---|---|---|
| the sums' `B` cells | `G` | the unit | 0.862 | 0.000 | 46 |
| the sums' `B` cells | `G` | `χ₁` | 0.673 (two channels 1.014) | 0.000 | 46 |
| the sums' `B` cells | `y` | `χ₁` | 0.583 | 0.000 | 40 |
| every digit arrival | `G` | `χ₁` | 0.204 | 0.005 | 41 |
| every digit arrival | `y` | `χ₁` | 0.194 | 0.010 | 41 |

The other pools read 29 to 80 in every region. The modes' demand at `B` is large, but it is not the
units'.

**Where the units' demand goes** (`CROSSING_DEMAND.py`, `MODE_MEMORY.py`). The exact crossing
`χ₁(c₀)` is scored by its two channels' share (at most 2):
- At `U` it takes 1.77 of every mode's covector and 1.86 of the input covector. One mode alone
  takes at most 0.52, and the modes that take most are 4, 15, 2, 6 and 14 (0.52 to 0.42). Mode 41
  takes 0.08 and mode 16 0.16; the median mode takes 0.15.
- At `B` it takes 1.10 of every mode's covector but only 0.39 of the input covector. One mode alone
  takes at most 0.14 (median 0.05). The demand reaches `B` through the modes, spread over all of
  them.
- The modes that read the units at `U` are mostly short and turning. Modes 4, 15 and 6 keep 0.11 to
  0.27 of their value per cell and turn 1.8 to 2.8 rad; 2 and 14 keep about half.
- The modes that carry a value from `B` to `U` alike for both result lengths keep more and turn
  less: 41, 56 and 48 keep 0.58 to 0.80 and turn 0.31 to 0.67 rad. Mode 16, where the founding by
  `U`'s demand placed the crossing, keeps 0.57 and turns 0.02 rad.
- The antinodes the third result digit crosses (47, 38, 55, 7) turn 2.5 to 2.9 rad a cell, nearly a
  half-turn. One more digit flips them.

So the nodes that carry the crossing and the modes that read it at `U` are different modes. A value
placed in a node reaches `U` alike for both result lengths and finds almost no reader there. A value placed in a reader at
`B` fades over the two or three cells to `U` and is turned by the result's length.

**A placed form founded with its reader** (`FOUND_RING.py`). The situated form
`c_t = (aᵀs_t)β_(d_t)` is pushed into a ring that rides one mode's own moves:
- `r_t = λ_(m,t) r_(t−1) + β_(m,t) conj(r_(t−1)) + c_t`.
- The ring is read at every cell through a lift into the input, `x⁰_t += P(Re r_t, Im r_t)`.
- With no memory this is the machine's present situated lift.
- The pool law founds `a` with no start, against the input covector at every reading cell.

The region is no label: every digit arrival of the eight training parts pushes, and every cell reads.
Fourteen foundings (`χ₁` and the unit, each in modes 41, 16, 56, 48, 15 and 4 and with no memory)
find no crossing:
- the `χ₁` forms hold at most 0.09 of `χ₁(c₀)` at `B` and read 51 to 68 of 495;
- the unit's forms read 34 to 44.

**Which side loses it** (`RING_REGIONS.py`; mode 41, pool `χ₁`):

| pushed at | read at | the outside form's share | the founded form's share | holds `χ₁(c₀)` at `B` | held out, units at `B` |
|---|---|---|---|---|---|
| every digit arrival | every cell | 0.044 | 0.168 | 0.019 | 52 |
| every digit arrival | the sums' `U` cells | 0.152 | 1.076 | 0.777 | 293 |
| the sums' `B` cells | every cell | 0.065 | 0.082 | 0.732 | 296 |
| the sums' `B` cells | the sums' `U` cells | 1.678 | 1.716 | 0.945 | 443 |

Situating either side gives about 0.75 and 295. Situating both gives 443, and situating neither gives
52. Read over the whole text, the crossing is diluted: the outside form takes 0.044 there.

**Reading regions with no label** (`RING_TENSION_READ.py`, `RING_AFTER_RELATION.py`; pushed at every
digit arrival):
- **Where the tension stands out** (the leverage `y Y⁻¹ yᵀ`, top 2 to 20 percent of cells). These
  regions hold 20 to 162 of the 8,986 `U` cells, and the founded forms read 48 to 58.
- **After every line's `=`** (84,951 cells, all `U` cells among them). The founded form holds 0.029
  and reads 52.
- **After `=` on the sums' lines only** (31,337 cells). The operation here is a label, so this is a
  ceiling. The form holds 0.748 and reads 273.

**The operation at `B`** (`OP_TURN_AT_B.py`). The outside form reads the state at `B` along one
direction, fitted on the sums' first operand. On each operation's own `B` cells, a straight-line
read of the form's two channels, refitted there, recovers `χ₁(a₀)`:
- after `+`, 0.966 (8,986 cells);
- after `−`, 0.014 (4,517);
- after `*`, 0.114 (8,941).

A straight-line read in two real channels cannot tell a strand from its reflection, so `a₀`'s units
are not merely turned after `−`: they are absent from the form's direction. The operator changes
what the state carries along it where the second operand arrives. Whether the state carries `a₀`
elsewhere after `−` was not read. So after `=` on every line, differences and products share the
reading cells with a form that cannot read them.

**What it says** [agent-inferred]:
- `G_h` is the right demand for a placed value, but founding on it alone does not tie the crossing at
  `B`. The units' demand reaches `B` spread over the modes. The nodes that carry the crossing have
  no reader at `U`, and a value placed in the readers fades and turns before it arrives.
- A placed form is therefore founded together with its reader. The ring does this. It finds the
  crossing when its push or its read is situated where the crossing lives, and not when both span
  the text.
- The regions the machine has without labels fail in two ways. The tension's loudest cells are not
  the `U` cells. After `=`, the operation decides what the state carries along the form's direction
  at `B`. The knot at `B` slips until the operation crosses it.

The acceptance is not met by the machine's founded forms. The exterior 471 of 495 stays exterior.

**Decided next** [agent-inferred]: the ring's push and read are each crossed with the operation the
state carries.
1. Measure first, as regions read from the state: the push gated by the operator's strand at the
   arriving digit, and the read gated by the relation's arrival with the same strand.
2. If the ceiling from those regions reaches the bar, build them as the ring's own gates: pair
   contacts of the ring with the operator strand, the pools staying the ring's characters.

**The runs.**
- The mode covector reads were projected at 20 to 30 s a part (deadline 90 s, four at a time).
  - At the digit arrivals they took 14.9 to 16.0 s (peak 24 MiB).
  - At the sums' `U` cells they took 14.8 to 15.8 s.
- Every cell's moves and input covectors were projected at 30 to 90 s a part with the filter
  (deadline 180 s, two parts at a time). They took 16.3 to 17.6 s (peak 408 MiB for the moves).
- The eight exterior analyses ran under deadlines set from the earlier foundings' measured times
  (60 to 360 s). No projection was written down before they launched, and that is recorded here as
  missing:

| analysis | deadline | wall time | peak |
|---|---|---|---|
| `FOUND_BY_MODES_AT_B.py` | 240 s | 67.3 s | 1.79 GiB |
| `CROSSING_DEMAND.py` | 120 s | 8.8 s | 137 MiB |
| `FOUND_RING.py` (14 foundings) | 360 s | 221.2 s | 2.96 GiB |
| `RING_REGIONS.py` | 240 s | 68.2 s | 3.64 GiB |
| `RING_TENSION_READ.py` | 240 s | 50.6 s | 2.79 GiB |
| `RING_AFTER_RELATION.py` | 240 s | 49.0 s | 2.79 GiB |
| `OP_TURN_AT_B.py` | 120 s | 33.1 s | 949 MiB |
| `MODE_MEMORY.py` | 60 s | 9.9 s | 922 MiB |

The code change passes the gate (`tools/gate.sh`, every step; its first run stopped when the disk
filled and was rerun after stale build caches were removed) and the tower's 36 tests.

## The operation crosses the reader

The last section left the knot at `B` slipping until the operation crosses it. Here the operation is
crossed in, first by label and then by the state's own reads. Everything is exterior, computed
outside the machine with its moments.

**By label, the ring passes the bar** (`RING_OP_REGIONS.py`; ring in mode 41, pool `χ₁`). The
regions are bounded by an operator's arrival and a relation's arrival on the lines whose last
operator before `=` is `+`:

| pushed at | read at | holds `χ₁(c₀)` at `B` | held out, units at `B` |
|---|---|---|---|
| a sum's second operand (17,073 cells, every sum's `B` among them) | after `=` on a sum's line (31,337) | 0.844 | **385** |
| a sum's second operand | the sums' `U` cells | 0.865 | 424 |
| every digit on a sum's line (34,137) | after `=` on a sum's line | 0.824 | 359 |

For comparison: pushed at every digit arrival and read after `=` on a sum's line, 273.

**The state carries the operation on a straight line** (`OP_GATE.py`). Level 0's state before the
move was read at every cell (`read-tower-modes`, 128 coordinates). Its straight-line read with a
constant was fitted to each label:
- "a sum's second operand" at the digit arrivals: R² 0.992 (mean 0.993 inside, 0.001 outside);
- "after `=` on a sum's line" at every cell: R² 0.824 (0.850 inside, 0.026 outside).

With these fitted reads as soft gates (the ring's push weighted by the push gate's value or its
square, its reading cells by the read gate's), the ring form reads 359 to 392:
- with the push gate and the label read, 388 and 392;
- with both gates, 359 to 372.

These gates are fitted to labels, so they are a ceiling for a strand the state carries, not a
founding.

**Founded blind, the push gate finds the operation only where the sum's result is read**
(`BLIND_GATE.py`, `BLIND_PUSH.py`). Each gate is a pair contact of the ring with the state's
straight-line read `x = (state, 1)`:
- the push gate `g`: the ring is pushed with `(aᵀs)β_d(gᵀx)`;
- the read gate `h`: the form read at a cell is `(hᵀx)r`, against the input covector at every cell.

The form, then each gate, is founded in turn by the pool law from unit gates. How much of each
label the founded gate carries is read outside:

| founded blind | read at | the push gate carries a sum's second operand | held out, units at `B`, by round |
|---|---|---|---|
| the push gate | after `=` on a sum's line (label) | 0.34, 0.46, 0.51, 0.55 | 273, 371, 391, **393** |
| the read gate (push on the label) | its own gate | — (the read gate carries 0.02 to 0.05) | 247, 218, 200, 186 |
| both gates | their own gates | 0.00 to 0.02 | 52, 66, 74, 69 |
| the push gate | after `=` on every line | 0.01 to 0.02 | 52 to 78 over six rounds |
| the push gate | every cell | 0.00 to 0.01 | 50 to 55 over six rounds |

**The push gate alone is not enough, and the crossing is not the loudest thing an operation-free
region holds** (`GATED_PUSH_FREE_READ.py`). The push is gated by the label, and the form is founded
in regions that name no operation:
- read after `=` on every line, it holds 0.759 and reads 321;
- read at every cell, 0.605 and 247.

The label regions' form scores a circular share of 0.112 after `=` on every line, and 0.045 at
every cell. The blind founding found 0.127 and 0.106 there. In those regions something louder
leads, and the founding selects it.

**What it says** [agent-inferred]:
- The knot at `B` ties when the operation crosses both its ends. The push must carry the operation
  (321 without it on the read side, 385 with it), and so must the read.
- The operation is already a strand of the state. A straight line reads "a sum's second operand"
  almost exactly (0.99), and the pool law finds that strand blind as a pair contact of the push,
  once the read stands on the sums' results (393).
- The read gate is not found blind, and an operation-free read does not select the crossing. The
  sum's crossing is one of several crossings, one for each operation, and on all lines together
  another form is louder. A single leading form cannot be the sum's; the founding must keep plural
  forms.

The acceptance is not met by the machine's founded forms. The blind push gate's 393 stands on a
labelled read region.

**Decided next** [agent-inferred]: found plural ranks in an operation-free region, each a ring form
with its own blind push gate, deflating the tension by each founded lift. Then read whether one rank
holds the sum's crossing and its push gate the sum's operand. If one does, the read side is the
rank's own, and the build is the machine's ranked founding with gated rings.

**The runs.** The projection was written in each analysis before it launched:

| run | projection | deadline | wall time | ratio | peak |
|---|---|---|---|---|---|
| `RING_OP_REGIONS.py` | about 90 s | 180 s | 54.8 s | 0.61 | 2.82 GiB |
| the state reads (`read-tower-modes full`, eight parts, two at a time) | 15 to 25 s a part | 180 s each | 11.5 to 12.4 s a part | 0.46 to 0.83 | 193 MiB |
| `OP_GATE.py` | about 120 s | 300 s | 93.5 s | 0.78 | 3.35 GiB |
| `BLIND_GATE.py` | about 330 s | 600 s | 236.2 s | 0.72 | 4.29 GiB |
| `BLIND_PUSH.py` | about 220 s | 400 s | 277.9 s | 1.26 | 4.32 GiB |
| `GATED_PUSH_FREE_READ.py` | about 75 s | 180 s | 67.9 s | 0.91 | 4.50 GiB |

- The first state reads failed in their filter: a state on `2^(−24)` passes 32 bits. They were rerun with
  the rows kept as 64-bit integers, under the same deadline.
- `BLIND_PUSH.py` ran past its projection (its first run's rounds took 16 to 19 s and its second's, read at every cell, 19 to 23 s, against 15). It stayed inside its
  deadline and is reported complete.

## Plural ranks find the sum's operand, and a received landmark is communication

**Ranked, the founding separates the operations itself** (`PLURAL_RANKS.py`). The region is after
`=` on every line, which names no operation. Each rank is a ring form in mode 41 with pool `χ₁` and
its own push gate, founded blind (three rounds from a unit gate). The tension is deflated by each
rank's two channels before the next.

| rank | share (circular) | its push gate carries a second operand of a sum / difference / product | holds `χ₁(c₀)` at `B` | held out, units at `B` |
|---|---|---|---|---|
| 0 | 0.126 | 0.015 / 0.008 / **0.157** | 0.018 | 78 |
| 1 | 0.129 | **0.497** / 0.036 / 0.024 | 0.640 | 258 |
| 2 | 0.110 | 0.000 / 0.040 / 0.000 | 0.032 | 55 |

The first rank leans to products. The second finds the sum's operand with no label anywhere, and its
form holds the crossing at 0.64. Its read still stands on every line's result, so it reads 258.
With the read on the sums' results, the same blind gate reads 393 (`BLIND_GATE.py`).

**The lens** (Brandon, October 25). A label that marks where to look is a landmark, like the ones
navigator paths converge on. A machine that later knows more than whoever marked its text can hand
markers back, and nobody in that exchange cheats: it is communication.
- What separates communication from catered machinery [agent-inferred]: a landmark says where to
  look, never what to find. Nothing in the 385 or 393 was handed the units: the machine's own pool
  law found the form, and the held-out read at `B` uses no marker.
- These landmarks are the text's own `+` and `=`, and the state already carries them (0.992 on a
  straight line).
- A landmark enters as received material at the exterior boundary, a marker stream beside the text.
  It is never a parser inside the machine.

**Decided next** [agent-inferred]: build the machine's situated founding with three parts.
1. Ring forms that ride a placement mode's own moves.
2. A push gate founded blind as the ring's pair contact with the state.
3. The reading cells weighted by a received landmark stream.

The acceptance is then read on the machine's founded forms, with the landmark named in the claim.
The fixed bar and its cell `B` do not move.

**The run.** `PLURAL_RANKS.py` was projected at about 270 s (deadline 500 s) and took 258.0 s (0.96;
peak 4.33 GiB).

## The machine founds the units' ring at a received landmark

The last section handed the ring its pool, the character `χ₁` of the arriving digit: a table of the
digits' values. Here the pool is founded blind over every arriving class, first outside the machine
and then by the machine itself.

**From the unit, the blind pool stays on the digits' common push** (`BLIND_POOL.py`,
`PLURAL_POOL.py`). The form `a`, the pool `b` over every arriving class and the push gate `g` are
founded in turn from the unit pool (every class alike), read after `=` on a sum's line. The pool's
power over the characters of the digits' ring (an exterior read; the founding never sees a digit's
value) sits at `k=0`, 0.98 to 1.00, at every round and in every rank, and the held-out units at `B`
read 40 to 52 (three ranks: 49, 34, 37). The unit is a fixed point of the alternation, as it was for
the form before the ring start.

**The classes' coupling has the digits' ring as a mode** (`POOL_SEED.py`, `POOL_SEEDS.py`). After
the common read `W̄ = S⁻¹Σ_u M_u`, each class keeps the tension it moves beyond what the state says
for every class alike, `M̃_u = M_u − S_u W̄`, and two classes couple by how alike those are,
`K_uv = tr(S⁻¹ M̃_u Y⁻¹ M̃_vᵀ)/√(n_u n_v)`, read over every arriving class with no digit named. Its
third mode sits on the digits (0.999) and on the ring's first character and its mirror, `χ₁` and
`χ₉`, at 0.44 each. Its other leading modes sit on the line's marks (newline, the operations, `=`).
Each mode as a pool start, three rounds, read after `=` on a sum's line:

| start | share (circular) | the pool's power on the digits | held out, units at `B` |
|---|---|---|---|
| the unit | 0.399 | 0.663 | 49 |
| `K` mode 1 | 0.476 | 0.020 | 49 |
| `K` mode 2 | 0.567 | 0.004 | 44 |
| `K` mode 3 | 0.274 | 0.988 (`χ₁` 0.70) | 116 |
| `K` mode 4 | 0.407 | 0.013 | 51 |

From mode 3 the founding stays on the digits and turns towards `χ₁`. Its share is the smallest, so
the pool law (keep the larger share) would not keep it.

**The digits' ring is a basin, and the landmark's breadth decides who leads** (`POOL_REACH.py`).
- *Longer*: from mode 3 for eight rounds, read after `=`, the pool turns to `χ₁` (0.55, 0.64, 0.70,
  0.76, 0.83, 0.90, 0.95, 0.97), the gate comes to carry a sum's second operand (0.32), and the
  held-out units climb 112, 96, 115, 125, 130, 163, 215, 266 and close at 296, still rising. Its
  share closes at 0.324, below the line-mark forms' 0.40 to 0.57.
- *At the units cell*: the landmark after `=` marks about four cells a line, and the result's units
  are news at one of them. Marked at the sums' units cell alone (the cell that codes the result's
  units; the landmark marks where, never what), three rounds:

| start | share (circular) | pool | its gate carries a sum's second operand | held out, units at `B` |
|---|---|---|---|---|
| the unit | 0.486 | `k=0` 1.00 | 0.003 | 42 |
| `K` mode 2 | 0.378 | `k=0` 0.96 | 0.103 | 53 |
| `K` mode 3 | **0.827** | `χ₉` 0.99 | 0.351 | **391** |

At the units cell the digits' ring is the loudest form the cell holds, so the pool law keeps it and
it reads 391. `χ₉` is `χ₁`'s mirror, the same ring turned the other way, and the probe reads both.
After `=` the line's marks were louder only because that landmark marks the line's end as well.

**The machine's founding** (`found-tower-ring`, [`tower_ring.rs`](../../crates/holonics/examples/solenoidal_alpha/complete_language/tower_ring.rs)).
The machine now does what the exterior reads did:
- **The ring** rides placement mode 41's own moves. The tower's reverse now returns each mode's move
  at every cell beside the input covector (`InputCovector::moves`).
- **The push** is `(aᵀŝ)(bᵀx̂)(gᵀx)`. The pool `b` is founded over the present classes and returned
  as its least-norm factor over `x̂`.
- **The starts** are the unit and the classes' coupling `K`'s four leading modes, all computed in the
  machine. Each start is founded for three rounds of `a`, `b`, `g` and a closing `a`, and the start
  whose form gives the larger exact share is kept.
- **The reading cells** are where a received landmark stream marks (`tools/landmarks.py sum-units`:
  one byte per byte of the text, set at each `digits+digits=digits` line's units cell).

The build met three repairs, each found by a development read on one block (27k cells, 1,146 marked):
- The exact inverse of the step's 256-column Gram took 95 s of a 99 s step. The search now inverts a
  released copy, scaled so the Gram's diagonal has one width, with the inverse's identity held at
  the Gram's own width. On `[Q | I]` the first release of a row kept almost none of the inverse's
  digits, and the first step's share fell to 140 thousandths. With the identity at the Gram's width
  it is 528, which is what the exact inverse gives.
- Three founded factors, each bounded over the passage, left 128 bits. Each factor's value is now
  released to below `2^40` at its own bound before the product, so the push is formed exactly
  whatever widths the founding gives the factors. A founded direction is kept as wide as it needs
  inside the 64-bit word, not released to `2^15` after its balancing.
- The tower was read again for every pass (4.7 s of a 4.8 s step). The survey now keeps one reading
  of each stream, and a pass carries the rings over it (0.3 to 1.2 s on one block, 0.5 to 6.4 s on
  the whole text).

**The founding on the training text** (216,131 cells, 9,018 sums' units cells marked, two ranks, 380 s):

| rank | start | circular share at its last step | exact share, all ranks' channels |
|---|---|---|---|
| 0 | the unit | 0.485 | 0.632 |
| 0 | `K` mode 1 | 0.581 | 0.624 |
| 0 | `K` mode 2 | 0.375 | 0.519 |
| 0 | `K` mode 3 (kept) | **0.825** | **1.634** |
| 0 | `K` mode 4 | 0.803 | 1.590 |
| 1 | the unit | 0.435 | 2.149 |
| 1 | `K` mode 1 (kept) | 0.630 | **2.303** |
| 1 | `K` mode 2 | 0.617 | 2.302 |
| 1 | `K` mode 3 | 0.317 | 2.068 |
| 1 | `K` mode 4 | 0.608 | 2.261 |

The exact share counts both faces of each rank as channels, so two ranks can reach 4. The machine's
pool law keeps the digits'-ring start, as the exterior founding did (0.825 against 0.827).

**The acceptance passes** (`read-tower-situated` at every sum's `B` cell of the training text and of
the held-out text, then `tools/tower_modes.py probe --ops +`). The fixed bar was at least 370 of the
495 held-out sums' units read at `B`, the cell where the second operand's units arrive.

| founded forms | held out, units at `B` (commonest 63) | the first operand's units (62) | the second's (57) |
|---|---|---|---|
| rank 0, the digits' ring | **391** | 52 | 53 |
| ranks 0 and 1 | **390** | 65 | 86 |

The claim, with its landmark named: **the machine's own founding, reading where a received landmark
marks the sums' units cells of the training text, founds a form whose instant value at `B` reads a
held-out sum's units in 391 of 495.** The landmark marks where to look on the training text alone.
The held-out text carries no marker, and its read at `B` is a cell the landmark never marks: the
form there has not heard the result, and reads it from the operands it carries. No value of the
text enters the founding: the landmark is placed from each line's shape (`digits+digits=digits`),
and the founding meets the arriving digit only through the tower's own encoding. The pool was
founded over every arriving class from the classes' own coupling, and the unit start, the line-mark
starts and the digits' ring were weighed by the same pool law. The second rank adds nothing to the units (390): its pool sits on the line's marks.

**What it says** [agent-inferred]:
- The step's acceptance is met by the machine, not by an exterior fit. The exterior founding at the
  same landmark read 391 too.
- The landmark's grain decided the founding more than the law did. After `=` the line's end is news
  at three of four marked cells, and the pool law kept the line-mark forms that carry it. At the
  units cell, the units are the news, and the same law keeps the digits' ring.

**The runs.** Each development read and the founding are in `RUNS.tsv`. The founding was projected
at about 1,150 s (the largest pass measured on one block, 1.245 s, times the 8.01 times as many
cells) with a 1,300 s deadline. It took 380.1 s (0.33), peak 646 MiB.

## The ring inside the learner, and the tower's own pass dephases it

The founding's 391 is an exterior read: a probe fitted on the training text reads the ring's form at
`B`. The next step puts the ring inside the learner, so that the tower's own top guess reads it.
**Fixed acceptance:** after one training pass, the tower's own top guess at a held-out sum's units
cell `U` is the units digit in at least 370 of 495, and its code there is below the same pass
without the ring.

**The join** [definition; agent-inferred] ([`RingFace`](../../crates/holonics/src/hnn/tower.rs)). The
founded rank rides mode 41 of level 0 inside the forward step, carried by each stream beside its
modes, and the tower's face reads it through its own readout, `z += V ρ`, with `V` opened at zero.
It is placed after the level's move, not lifted into the level's input: the moves it rides are keyed
by that input, so a lift there would read the ring before it is formed. Its factors are held, as the
pair face's forms are. The tower's material is not held behind it. The covector its face returns
reaches the carried face each push read and the mode's move it rode:

```text
G_t = g_ρ(t) + Mᵀ_(t+1) G_(t+1)
∂ŝ_t = Re(conj(G_t) ∂v_t/∂ŝ_t) 2^(−σ)
∂(λ_t, β_t) = (x gx + y gy, x gy − y gx, x gx − y gy, x gy + y gx) 2^(8−σ)    at r_(t−1) = (x, y)
```

The covector tests read the code's difference for every family of the gated and the pumped pair
towers with the ring joined.

**The joined ring reads the units, from outside.** Joined to the tower it was founded on, the
tower's own guesses are unchanged (48 of 495, 3.49 bits a digit, every code equal to the tower
alone's). The ring's face at `U` turns once round the circle across the ten digits, about 36° a
digit (median turn `0` 49°, `1` 95°, `2` 119°, `3` 145°, `4` 212°, `5` 247°, `6` 279°, `7` 299°,
`8` 321°, `9` 357°). Nearest mean direction, leaving each cell out, reads 340 of 495.

**The pass.** The whole-text pass was projected at 334.3 s from a pass time I could not trace to
this tower on this host. Both towers ran at about 0.29 s a section (the ring's at 9.8 s for its
first 32 sections, the plain tower's at 9.6 s), 1.6 times the projection's rate, so both were
stopped on that evidence, the ring's at section 608 of 1,747. The step moved to a smaller
partition, not a larger deadline: one pass over the training text's arithmetic block (its last
216,131 bytes, where all 9,018 of its sums sit), 211 sections, projected at 65 s with a 90 s
deadline. Each pass took 63 to 70 s.

| after one block pass | top guess right at `U` (of 495) | bits a digit at `U` | held-out text, bits a byte | the ring's outside read at `U` |
|---|---|---|---|---|
| before the pass | 48 | 3.488 | - | 340 |
| the foil, no ring | **72** | **3.267** | 2.709 | 69 (joined after the pass) |
| ring, face fitted to its loudest read | 69 | 3.302 | 2.675 | 68 |
| ring, face a ratio to its own power | 60 | 3.318 | **2.664** | 46 |

**The acceptance is not met.** The ring made the tower's guesses at the units worse than the foil
in both forms. The whole held-out text codes 0.045 bits a byte lower with the ring (2.664 against
2.709), which is a reading beside the failure and not a success.

**Two causes, located.**
- **The face's scale.** The first face released each read so that the passage's largest read lay
  below `2^16`. The ring is loudest on prose: on the held-out arithmetic its face at `U` lay near
  100 units of `2^(−16)`, about `2^(−9)` of the readout's reach. A ring's reading is its turn, so
  each rank's face is now its read as a ratio to its own power, the law the tower's own read obeys
  (`ratio_to_power`), and the covector it returns turns the ring and does not swell it. The joined
  tower still codes every cell as the tower alone. This repaired the scale and not the result
  (60 of 495).
- **The tower's own pass dephases the ring.** The ring's outside read at `U` falls from 340 to
  between 46 and 69 after one pass, and it falls just as far when the ring was never joined: the
  same forms joined to the foil after its pass read 69. The founded factors read a carried face and
  ride a move that the tower's learning changes, and the ring's memory is long (`|λ|` of mode 41 is
  `1073275308` on `2^(−30)`, about 2,300 cells to fall by `e`), so a small change in the move's turn
  accumulates over the cells it carries. With `V` at zero the ring carries no code, so nothing in
  the pass protects what it reads, and it is lost before its readout learns to read it.
  [Corrected in "The ring's readout is a pair contact with the top face": `1073275308` is the
  ungated move; the gate makes mode 41's move at the units cells `|λ_t| ≈ 0.853`, about 7 cells,
  and its turn drifts 0.2 to 0.6 of the line's width a pass. The ring is lost at its push.]

**What it says** [agent-inferred]: a founded form held on a learning tower is a cause carried into
a new consumer without its frame. The founding located the ring in the frame of one tower; the
learner moves that frame. The next loop carries the ring with the tower: its readout founded with
it on the passage it is joined on, so that the ring carries code from the first cell and its
covector protects it, and its factors deposited from the covector that reaches them, as the rest of
the tower's material is.

**The runs** are in `RUNS.tsv`. The join with the fitted face read the training text once (269.3 s
against 277 s projected); the ratio face needs no fitting, and its join takes 0.2 s.

## The ring's readout is a pair contact with the top face

The loop after the dephasing carries the ring with the tower in two parts: its readout founded at
the join, so that the ring carries code from the first cell and its covector reaches what the ring
reads, then one block pass. The acceptance is unchanged: after one training pass, the tower's own
top guess at `U` is the units digit in at least 370 of 495, and its code there is below the same
pass without the ring (the foil: 72 of 495, 3.267 bits a digit).

**The readout's law, chosen by reading.** With the joined tower held, every cell of the block (the
training text's last 216,131 bytes) and of the held-out arithmetic was read once (`read-tower-cells`:
the class that follows, the top face, the ring's face `ρ` and every class's share), and readouts of
each kind were fitted outside the machine on the block and read on the held-out text
(`RING_READOUT_LAW.py`, an exterior float read; the machine reads none of it):

| readout added to the tower's face | right at `U` (of 495) | bits a digit at `U` | held-out arithmetic, bits a byte |
|---|---|---|---|
| none (the tower alone) | 48 | 3.488 | 2.300 |
| a bias | 55 | 3.394 | 2.276 |
| the ring alone, `V ρ` | 96 | 3.223 | 2.271 |
| the top face alone | 71 | 3.357 | 2.207 |
| top face and ring, side by side | 115 | 3.164 | 2.203 |
| a received landmark's gate times the ring | 281 | 2.094 | 2.230 |
| **the top face times the ring, `W (x̂ ⊗ ρ)`** | **309** | **1.916** | **2.156** |

A ring's phase is news at one cell of a line and not at the others. After a sum's second operand
the ring holds the units' turn through `=` and the result's other digits, and a readout of `ρ`
alone must read every cell alike. A landmark gate (a least-squares read of where the training
text's units are, 0.58 on average at the held-out units against 0.018 elsewhere) placed it at 281,
and the top face, which knows which cell codes the units, places it better than the landmark. So
the readout is a pair contact with the top face [definition; agent-inferred]:

```text
x̂_t = (2^16 x_t / ‖x_t‖_rms, 2^16)
z_t += W (x̂_t ⊗ ρ_t)                  W: A × (d + 1)·2R, on the material's 2^(−24)
```

with `(d + 1)·2R = 130` channels at width 64 and one rank. Its covector reaches `W`, the ring's
face (and through it the carried face and the move the ring rode) and the top face, each through
its ratio ([`RingFace`](../../crates/holonics/src/hnn/tower.rs)); the covector tests read the
code's difference with `W` keyed away from zero. On the foil after its pass, with the same forms
joined, the same readout reads 80: the pass had already taken the ring's units away.

**The founding at the join** [definition; agent-inferred] (`found-ring-readout`). The bridge's own
solution gives the readout's direction, the exact least squares `Q D = −M` with `Q = Σ φφᵀ`,
`M = Σ φ yᵀ`, `φ_t = x̂_t ⊗ ρ_t` and `y_t = p_t − q_t` over the joined tower's read of the block
from rest, and the passage's code gives its scale, doubled while the code falls and then narrowed
by golden section. Read outside first, the least squares direction alone read 74 at `U`, and its
multiples by 2, 4, 8, 16 and 32 read 100, 169, 243, 257 and 239 (`RING_READOUT_CLOSED.py`); one
Newton step per class read 190, and the fitted optimum 292 to 309. In the machine the scale came to
`849322` on `2^(−16)` (about 13 of the direction's units) in 37 code reads, and the block's code
fell from 2.288 to 2.236 bits a byte.

| the tower's own top guess | right at `U` (of 495) | bits a digit at `U` | the whole held-out text, bits a byte |
|---|---|---|---|
| joined, readout at zero | 48 | 3.488 | 2.448 |
| **founded at the join, before any pass** | **257** | **2.229** | **2.436** |
| the foil after one block pass | 72 | 3.267 | 2.690 |
| founded, then one block pass, moments at zero | 52 | 3.354 | 3.149 |
| founded with its moments, then one block pass | 65 | 3.279 | 2.845 |

Before any pass, the tower's own guess at the held-out units is 257 of 495, more than three times
the foil's after its pass, and its code there is 1.04 bits a digit below the foil's. It is the machine's own read:
the forms were founded at a received landmark and the readout on the training passage, and the
held-out text was read only to measure it. **The acceptance is not met**: it asks for that after a
pass, and the pass takes it away.

**The moments** [definition; agent-inferred] ([`TowerLearner::open_moments`]). The first pass ran
with the readout's moments at zero inside a learner whose other moments were opened, so its first
steps moved every entry of `W` at two to four times the rate whatever its covector carried, and the
held-out text read 3.149 bits a byte. A founded family's moments are now opened at its passage's own section
statistics: each of the block's 211 sections is read forward and back from the streams' states,
without a deposit, and the family takes the mean covector and the mean square (37.9 s). This
repaired part of the text (2.845) and not the units (65).

**Where the pass loses it, located.**
- *Not the readout.* The pass moves `W` far (its root mean square from `349912` to `1303073` on
  `2^(−24)`), but swapping `W` between the founded and the passed learners
  (`RING_SWAP_READOUT.py`) puts the loss in the tower: the passed tower with the founded readout
  reads 60 at `U` (2.789 bits a byte on the held-out text), and the founded tower with the passed
  readout reads 157 (2.529).
- *Not the move's turn.* At the held-out units the gate holds mode 41's move at `|λ_t| ≈ 0.853`
  (a line 0.147 wide, about 7 cells), not at the ungated `1073275308` on `2^(−30)` the last section
  counted. Over one pass mode 41's turn there moved 0.2 of its line's width in the foil and 0.6 with
  the founded readout (its moments at zero), and the median mode 0.09 in both (`RING_MOVE_DRIFT.py`).
- *The push.* Read by nearest mean direction with each cell left out, the ring's own face reads the
  sum's units at `U` in 339 of 495 before the pass and 45 after, and at the second operand's cell
  `B`, where the push lands, in 379 before and 64 after (`RING_OUTSIDE_AT_U.py`, `RING_AT_B.py`).
  The ten digits' mean turns at `U` go from one turn round the circle (45° to 355°) to a cluster.
  The push is `v = (aᵀŝ)(bᵀx̂)(gᵀ(ŝ, 2^16))`: `b` reads the arriving class over the encoding the
  ring was founded on, held, and `a` and `g` read the level's carried face `ŝ`, which the pass
  re-encodes. The first operand's turn is carried by `ŝ` in the frame of the tower the ring was
  founded on, and `a` still reads that frame.

**What it says** [agent-inferred]: the readout now carries code and its covector reaches `ŝ`, and
that is not enough to keep `ŝ`'s frame: the tower's own learning re-encodes the state everywhere
else at the rate, and the ring's demand is one term of that covector. The cause carried
unrepaired is now located at the push's factors: they are held in the frame of one tower while
the learner moves it. The next loop deposits `a`, `b` and `g` from the covector that reaches them,
with their moments opened on the founding passage, so the push follows the state it reads.

## The push's factors learn with the tower, and the deposit under the ring moves its frame

The last loop located the loss at the push: its factors `a`, `b` and `g` were held in the frame of
the tower the ring was founded on, while the pass re-encodes the state they read. This loop deposits
them. The acceptance is unchanged: after one training pass, the tower's own top guess at `U` is the
units digit in at least 370 of 495, and its code there is below the same pass without the ring (the
foil: 72 of 495, 3.267 bits a digit).

**The factors as material** [definition; agent-inferred] ([`RingFace`](../../crates/holonics/src/hnn/tower.rs),
`factor_on_material`). Each founded factor joins the learned material scaled by `2^k`, so that its
root mean square lies in `[2^24, 2^25)`, the material's unit, and its release moves by the same
`k`. A rank is read as a ratio to its own power, so a factor's scale is a gauge, and on the
material's grain the learner's step moves a factor by the same share of its own power as any other
entry. The founded ring's factors sat far apart (`a` near `2^16`, `b` near `2^60.3`, `g` near
`2^17.4`); on the material their releases are 11, 6 and 10 (from 3, 42 and 3), and the joined tower
reads every held-out cell as before (257 of 495 at `U`). The factors' covectors, from the push
`v = (aᵀŝ)(bᵀx̂)(gᵀ(ŝ, 2^16))` and the covector `G` the ring's face returns:

```text
e = conj(G) β γ / 2^(P+σ)     h = conj(G) α γ / 2^(P+σ)     f = Re(conj(G) α β) / 2^(P+σ)
∂a₀ = Σ Re(e) ŝ    ∂a₁ = −Σ Im(e) ŝ    ∂b₀ = Σ Re(h) x̂    ∂b₁ = −Σ Im(h) x̂    ∂g = Σ f (ŝ, 2^16)
```

with `α = aᵀŝ`, `β = bᵀx̂`, `γ = gᵀ(ŝ, 2^16)`, `P` the push's release and `σ` the face's, each sum
carried to the material's covector grain. The covector tests read the code's difference for the
readout and the factors of both ring-faced towers, and the founded family's moments now open over
the whole ring, readout and factors, on the founding passage.

| one block pass from the founded learner | right at `U` (of 495) | bits a digit at `U` | held-out text, bits a byte | the ring's outside read at `B` |
|---|---|---|---|---|
| founded, before any pass | 257 | 2.229 | 2.436 | 379 |
| the foil, no ring | 72 | 3.267 | 2.690 | - |
| factors held (the last loop) | 65 | 3.279 | 2.845 | 64 |
| **factors learning** | **55** | **3.293** | **3.033** | **62** |

**The acceptance is not met.** The factors' covector reaches them and does not keep the push in
the state's frame: the ring's read at `B` falls from 379 to 62, as it did with the factors held.

**Which deposit moves the frame, located** (`pass-ring-held`). The same pass from the same founded
learner, with chosen families held (their step zero, their moments still moving):

| hold | right at `U` | bits a digit at `U` | held-out text | read at `B` | training block, bits a byte as read |
|---|---|---|---|---|---|
| nothing (factors learning, above) | 55 | 3.293 | 3.033 | 62 | 2.252 |
| everything but the readouts | **253** | **2.039** | **2.512** | **379** | **2.190** |
| the ring's readout `W` only | 75 | 3.277 | 2.860 | 51 | 2.243 |
| what the ring reads (its factors deposit) | **258** | **1.729** | 2.712 | 313 | 2.182 |

- *Not `W`.* Holding the ring's readout leaves the loss as it was (75, read at `B` 51).
- *The tower's own deposit.* With only the readouts depositing, the ring keeps its read at `B`
  (379), the tower's guess at `U` holds (253 of 495) and its code there falls 0.19 bits a digit
  below the founded tower's, the held-out text codes 0.18 bits a byte below the foil's, and the
  block itself codes lower as it is read (2.190 against the full pass's 2.252).
- *What the ring reads.* Holding exactly the material the ring's level is carried by (the
  encoding, the pair lift, the levels below and the ring level's moves, pushes, gates, turns and
  pumps; `Tower::ring_read_families`) and letting the rest deposit (the levels above, the readouts,
  `W` and the factors), the level carries every passage as before: the test reads its modes equal
  after a section, and the ring different only through its factors. The tower's guess at `U` keeps
  258 of 495, and its code there falls to 1.729 bits a digit, 1.54 below the foil's.
- *The factors loosen the ring's digits.* Read outside, the ring's turn at `B` is a near-exact
  adder of two digit turns: each pair of operands' units sits at one angle (median resultant 0.972),
  the founded digits step 25° to 42° round the circle (36° is a tenth of a turn), and a turn for
  each operand's digit, added, leaves 5.8° (median) of each pair's angle unexplained
  (`RING_PHASE_PAIRS.py`). After the pass with the factors depositing, the steps run 22° to 48°,
  7.0° is unexplained, and the outside read falls to 313 at `B` and from 339 to 281 at `U`, while
  the code at `U` falls. The factors' covector serves the readout's code at every cell, not the
  turn each digit makes.

**What it says** [agent-inferred]:
- The cause is the tower's own deposit under the ring. Held, the ring's frame stays, and the
  acceptance's second clause is met: the tower's code at the held-out units is below the foil's,
  1.729 and 2.039 bits a digit against 3.267. The first clause is not: 258 and 253 of 495 against
  370.
- Depositing only the readouts, the bridge in the lap law's word, codes the held-out text best of
  every pass: 2.512 bits a byte, against the foil's 2.690, the full pass's 3.033 and 2.712 with the
  ring's reads held. This is the lap law's reading of a lap that founds nothing
  ([the lap record](2026-10-25_A_LAP_OVER_THE_SAME_TEXT_FOUNDS_ONLY_WHAT_THE_LAST_LAP_MADE_REACHABLE_SO_LEARNING_CLIMBS_STAIRCASES_AND_STEPS_AT_EACH_FOUNDING.md),
  §1): it should move the bridge, and re-encoding the state costs held-out code and dephases what
  was founded.
- The 370 is not reachable by any pass of this ring. Its own outside read at `U` is 339 before any
  pass, and the exterior readout reads at most 309 of it. The ring must carry more.
- The founding stopped short. Its alternation ran an authored three rounds, and its share was still
  climbing at the third: on the kept start the steps read 363, 384, 439, 467, 531, 590, 742, 793,
  814 and 825 per mille, each round gaining more than the last (`RING_FOUND.txt`).

**Decided next** [agent-inferred]:
1. A lap's deposit is the bridge: the readouts move, and the founded constitution stays until a
   founding changes it. The acceptance's foil becomes the same lap on the tower without the ring.
2. The founding alternates its factors to its own fixed point: a round that saves less than one
   bit over the marked cells closes it, and no round count is chosen.

## The founding stops at its own precision, and the readout and the carriage are what the units miss

The last loop decided two things: a lap deposits only the bridge, the readouts, with the same lap
on the tower without the ring as the foil; and the founding alternates its factors to its own fixed
point, closing at the first round that saves less than one bit over the marked cells. The
acceptance is unchanged: after one pass the tower's own top guess at `U` is the held-out sum's units
in at least 370 of 495, and its code there is below the foil's.

**The one-bit rule ran into the alternation's tail.** On the unit start the alternation ran 65
rounds in 257 s (3.0 to 3.5 s a round) and was stopped on evidence when that first start passed
its 180 s share of the 900 s deadline: the run is incomplete and wrote no form. Its share rose
395, 454, 477, 492 and 503 per mille in the first rounds, then 573 at round 55 and 577 at round
65. The first rounds saved 262, 107, 67 and 48 nats over the 9,018 marked cells; round 55 saved
1.7 and round 65 1.3, about two bits a round, falling by about 2% a round (`RING_FIXED_POINT.txt`).

**The precision rule** [agent-inferred] (`round_pays` in the example's `tower_ring.rs`). A round
pays when it moves the factors by more than the error the marked cells leave them: when its saving
reaches half a nat for each free parameter it re-states. A step that refits one factor exactly
saves `½ δᵀHδ`, `δ` its move and `H` the code's curvature in that factor, and the factor's
estimation error has `E[eᵀHe]` at least its count of free parameters. A round saving less moves
the factors by less than one standard error each, a difference no receiver of these cells
resolves. Each factor's scale is a gauge (the ring is read as a ratio to its own power), so the
round re-states `(2·128 − 1) + (2·15 − 1) + 128 = 412` free parameters and pays at 206 nats, 45.7
per mille of share over the 9,018 cells. Since the share is at most one, at most
`(1 − share₀)·N/412` rounds pay on any start, so the founding's time is bounded before it is
launched.

| start | rounds | circular share at the last round | exact share | three authored rounds |
|---|---|---|---|---|
| the unit | 3 | 0.477 | 0.632 | 0.632 |
| `K` mode 1 | 4 | 0.598 | 0.643 | 0.624 |
| `K` mode 2 | 2 | 0.351 | 0.496 | 0.519 |
| `K` mode 3 (kept) | 4 | **0.831** | **1.650** | 1.634 |
| `K` mode 4 | 5 | 0.826 | 1.640 | 1.590 |

The founding took 122 s against a projection of 343 s. On the unit start the rule closes at round
2, where round 1 saved 262 nats and round 2 saved 107. On the kept start it runs one round past
the authored three, whose second and third rounds saved 683 and 1,008 nats.

| from the precision-founded ring | right at `U` (of 495) | bits a digit at `U` | held-out text, bits a byte | the ring's outside read at `B` / `U` |
|---|---|---|---|---|
| the base tower, no ring, no lap | 48 | 3.488 | 2.448 | - |
| founded, before any lap | 245 | 2.259 | 2.437 | 390 / 346 |
| **one lap, the readouts only** | **244** | **2.071** | 2.518 | 390 / 346 |
| the foil: the same lap without the ring | 40 | 3.397 | 2.458 | - |
| the three-round ring (the last loop), founded | 257 | 2.229 | 2.436 | 379 / 339 |

**The acceptance is not met.** Its second clause holds: after the lap the tower's code at the
held-out units is 2.071 bits a digit, against the foil's 3.397. Its first does not: 244 of 495
against 370. The lap leaves the ring as founded (the outside reads do not move) and lowers the
training block's code from 2.190 to 2.171 bits a byte, against the foil's 2.219 to 2.210. On the
held-out text both laps code worse than before them (the block is arithmetic, the held-out text
mixed), the ring's tower by 0.081 bits a byte and the foil by 0.010.

**Two losses, each measured.**
- *The readout reads less than the ring carries.* The ring's own class directions, taken at the
  training text's 9,018 units cells and read at the held-out units by the nearest of them, give 358
  of 495; the tower's own top guess gives 244 (`RING_TRAIN_DIRECTIONS.txt`). On the sums of two
  two-digit operands, 321 against 220 of 399 (`RING_OWN_BY_OPERANDS.txt`). This read is honest: the
  directions are the training text's, and the 346 of the outside read beside it takes each held-out
  cell's class means from the other held-out cells.
- *The ring carries the units only when the second operand has two digits.* By the operands'
  lengths, read outside (`RING_CARRIAGE.txt`):

  | operands | sums | read at `B` | read at `U` |
  |---|---|---|---|
  | two digits and two | 399 | 355 | 311 |
  | one digit and two | 50 | 38 | 27 |
  | two digits and one | 44 | **6** | **3** |

  The three-round ring reads the same split (347, 36 and 7 at `B`). Where the push opens
  (`RING_PUSH_ROLES.txt`, `|aᵀŝ|·|gᵀ(ŝ, 2^16)|` by the arriving byte's role): at `+` after a
  two-digit first operand (the largest), at the second operand's units digit (0.46 to 0.59 of it), and at
  `=` (0.32 to 0.66); at the first operand's digits 0.02 to 0.03. The mode the ring rides turns at
  every byte (`RING_MODE_TURNS.txt`): each digit by 28° to 78°, rising with the digit, at `|λ|`
  0.68 to 0.92; `+` by −25° at 0.44; `=` nearly erases it (0.04, its pump 0.84). So the ring takes
  the first operand at `+`, and before the second operand's units digit arrives a tens digit, when
  there is one, has turned it [inferred from the two reads]. The founding fits the frame of the
  399 sums whose second operand has two digits, and reads the 44 whose second operand has one at
  chance.

**What it says** [agent-inferred]:
- The founding is now bounded by its own precision and gains little over the three authored rounds
  (1.650 against 1.634, 390 against 379 at `B`). More founding of this form will not reach 370:
  the form's honest ceiling at `U` is 358.
- The largest loss is the readout's, 114 sums: the ring carries the units, and the tower's guess
  does not read them.
- The rest is the carriage's: a sum's units are a right-aligned relation, known at the crossings
  `+` and `=`, and the ring reads them on the byte's clock, so the number of digits between the
  crossings sets the frame.

**Decided next** [agent-inferred]:
1. The readout first: split the tower's logits at the held-out units into the part through the
   ring and the rest, and read whether the ring's part alone picks the units. If it does and the
   sum does not, the rest overrides it, and the contact must carry the ring where it reads; if it
   does not, the ring's coefficients are fitted to the cells where the ring carries no units.
2. Then the carriage: a ring whose frame does not depend on how many digits fall between the
   crossings.

## The readout founded to its precision, and the lap that undoes it

The last loop decided to split the tower's guess at the held-out units into the ring's part and the
rest. The acceptance is unchanged: after one training pass the tower's own top guess at `U` is the
held-out sum's units in at least 370 of 495, and its code there is below the foil's (3.397 bits a
digit).

**The split.** `read-tower-at … split` reads the ring's part of the logits, `W φ` with `φ` the ring's
pair read with the top face, and then the same tower with its ring's readout at zero (the rest). On
the precision-founded ring with its readout founded by the last loop's one solve, the ring's part
alone picks the units in 335 of 495, the rest in 48, the whole in 245. The ring's part is right where
the whole is wrong at 133 sums and the reverse at 43; its median margin at the arriving class is 0.14
bits. The ring carries the units into the logits and the rest overrides it.

**The founding to the code's own curvature** [agent-inferred] (`found_ring_readout`). The one solve
`Q D = −M` takes the code's curvature as `Q = Σ φφᵀ`, flat in the masses, so the readout it founds
votes beside the rest instead of adding to it. The readout is now founded in rounds on the exact
code. Each round, for each class `c` that arrives, solves `H_c D_c = −m_c` with
`H_c = Σ p_c(1 − p_c) φφᵀ` and `m_c = Σ φ (p_c − q_c)` over the passage's cells, the masses `p`
read with the current readout (the classes couple only through the normalization, whose cross
blocks the round drops). Each block is solved exactly on a copy released so its largest entry is
below `2^40`, the right side released by the same shift; the direction takes one common lift, the
step `κ` is the passage's least code on a doubling then golden-section line, and the readout moves
by `κD` released to its grain, its code read again exactly. A round pays when it saves half a nat
for each free parameter it re-states (the ring's precision rule): `130 · (15 − 1) = 1820`, since
the normalization's gauge leaves one arriving class's rows free and the classes that never arrive
keep their rows at zero. Three rounds ran, saving 9,434, 915 and 131 nats against 910; the
founding read the block at 2.288 bits a byte before and 2.218 after, in 216 s against a projection
of 535 s.

| | whole right at `U` (of 495) | ring's part alone | rest alone | bits a digit at `U` | held-out text, bits a byte |
|---|---|---|---|---|---|
| founded by one solve (the last loop) | 245 | 335 | 48 | 2.259 | 2.437 |
| **founded by Newton rounds** | **308** | 223 | 48 | **1.977** | 2.580 |
| then one lap depositing the readouts | 247 | 221 | 41 | 2.003 | 2.668 |
| the foil: the same lap without the ring | 40 | - | - | 3.397 | 2.458 |

By the operands' lengths (`RING_SPLIT.txt`), the whole guess reads, from one solve to the rounds
to the lap: two digits and two, 218, 283 and 221 of 399; one digit and two, 22, 19 and 20 of 50;
two digits and one, 5, 6 and 6 of 44.

**What it says** [agent-inferred]:
- Founded on the code's own curvature, the ring's readout stops voting against the rest and adds to
  it: its part alone reads fewer units (223) and the sum reads more (308). The second clause of the
  acceptance holds (1.977 bits a digit against the foil's 3.397); the first does not (308 against
  370).
- The lap undoes the founding: 308 to 247, nearly all of it on the sums of two two-digit operands
  (283 to 221), while the lap lowers the block's code from 2.186 to 2.167 bits a byte at its own
  read. A lap's section steps descend the same code the rounds solved to their precision, and every
  step past that precision moves the readout by the passage's noise. This is the lap law the
  mathematics thread derived (a lap that founds nothing adds nothing; a stepped deposit past an exact founding is noise),
  measured on the readout: here the lap does worse than nothing.
- The held-out text codes worse after the founding (2.437 to 2.580): every class's readout row is
  founded on the arithmetic block alone, and the held-out text is mixed. A reading beside the
  acceptance, which is at the held-out sums.
- The rest of the gap is the carriage's. The whole reads 283 of the 399 sums of two two-digit
  operands, where the ring's own class directions from the training text read 321, and 25 of the 94
  sums whose operands differ in length. Every sum of two two-digit operands right, with the rest as
  it is, would make 424; the present ring form's outside read at `U` is 358 at most (the last loop).
  370 needs the ring to carry the units whatever the operands' lengths.

**Decided next** [agent-inferred]:
1. The training pass is the founding: the survey, the ring's founding and the readout's founding,
   each to its own precision. No lap over the same text follows a founding to precision (the lap
   law; measured here, 308 to 247). A later pass deposits on text the founding has not met.
2. The carriage: the ring's move is founded from the same covector as its push, keyed by the pair
   of the seam (the byte before the arriving one) and the arriving byte, the helical pair contact's
   address, in place of the turns of the mode it rides. Why this form: a sum's units are the
   product of the operands' units turns, `e^(2πi a₀/10) · e^(2πi b₀/10)`, and the ring makes a
   product only through its move. An operand's units digit is the seam at the next crossing (`+`
   or `=`), known only when the crossing arrives, so the move at a crossing must turn by the seam,
   and the move at a digit must hold, whatever the digit. A move keyed by the arriving byte alone
   cannot hold at a tens digit and turn at a units digit (both are digits), and a state factor
   times a class factor cannot hold at every digit for every state and still turn at the crossing;
   a move keyed by the pair can. It reads any medium's byte pairs and names no arithmetic; the
   hold at digits must be founded, not authored. Its acceptance reading: the outside read's split
   by the operands' lengths (355, 38 and 6 at `B`) levels, then the tower's own guess at `U`
   reaches 370.

## The machine locates the carriage key by loop closure

The last loop decided the carriage: the ring's move keyed by the pair of the seam and the arriving
byte, founded, not authored. The acceptance is unchanged.

**The pair move, built** (`RingFace::move_at`). A ring face carries one move for each (seam,
arriving class) pair met in the passage, each a complex multiplier on `2^(−30)`; a pair never met
takes the move of the mode it rides. The face, its text form and its restore carry the table, and
its tests read the covector of every pair against the exact code difference.

**Founding it by steps never left its start.** Three tries founded the 203 met pairs' moves by
steps along their covector from the unit move: a fixed step, a step by an octave line search, and
the same from the ring's rest. Each kept its start:

| founding | exact share | held out, units right by the outside read at `U` (of 495) |
|---|---|---|
| fixed step from the unit | 0.630 | 40 |
| octave line from the unit and from the rest | 0.685 | 48 |
| octave line, the steps kept | 0.686 | 36 |

A move's covector at the unit start carries no sign of the turn it needs: a sum's units turn is
reached only when both operands' crossings turn together, and one pair's step alone changes the
code by less than its noise.

**The ceiling.** A diagnostic held table (authored; read as a ceiling, never as a founding):
newline rests the ring, a digit holds it at `15/16`, `+` and `=` turn it by the seam digit's tenth
of a turn. Founded under it, the ring's exact share is 1.876 and the outside read carries the units
at `E` (the equals sign) in all 495 sums and at `U` in 415. The carriage the units need is a pair
move. The question is how the machine locates it.

**The key by loop closure** [agent-inferred] (`found_closure` in `tower_ring.rs`). This is the
Bombe's reading: the menu of contacts is the passage's crossings, and the key is the turn each pair
gives, located by closing loops. Choose an origin byte; between two arrivals of the origin the
ring's turn is the sum of the turns of the pairs met, `N_t θ` with `N_t` the count of each pair on
loop `t`. A loop closes when that sum is the turn at which the arriving classes stand, `ψ(C_t)`,
modulo the key's modulus `n`. The rows `N_t θ ≡ ψ(C_t) (mod n)` are integer. A modulus `n` exists
only where the system has torsion: `p` divides `n` only if the rank over the integers modulo `p`
falls below the rank over the rationals, which happens exactly when `p` divides every maximal
minor. So the founding reads, for each origin:

1. the rank over the rationals, from an echelon modulo one prime below `2^31`, certified: one
   maximal minor `M` is taken at the echelon's pivots, its determinant and the kernel vectors of
   Cramer's rule are read exactly by the Chinese remainder theorem past twice Hadamard's bound, and
   every row is checked against that kernel;
2. the torsion candidates, the primes below `2^19` that divide `det M`, each tested by an echelon
   modulo that prime (stopping at the rational rank: a prime is torsion when the rank falls);
3. the key: the kernel modulo each torsion prime, combined over the torsion primes' subsets, and
   the first combination whose `ψ` is injective on the arriving classes.

Integer elimination failed twice first. In `i128` a closure row would leave 128 bits; widened to
`BigInt`, the Hermite form grew and thirteen origins took 152 s, two unfinished at the 300 s
deadline. The deadline was not raised; the law changed to one minor read modulo primes.

| origin | rows (distinct) | pair columns | rank | `det M` | torsion | key |
|---|---|---|---|---|---|---|
| newline | 9,018 (9,011) | 149 | 145 | `110 = 2·5·11` | 2, 5, 11 | modulus 10 |
| `-` | 9,016 | 200 | 194 | 74 bits, readable 2, 5, 157 | none | none |
| `*` | 9,018 | 200 | 194 | 112 bits, readable 2, 3, 17, 59 | none | none |
| `+` | 9,018 | 129 | 127 | 1 | none | none |
| the ten digits, `=` | 199 to 7,517 | 29 to 195 | 29 to 191 | 1 | none | none |

All fifteen origins close in 4.7 s, against more than 300 s before. One origin keys the passage:
the newline, modulo 10, with `ψ(d) = d + 2` for the units digit `d` of the line's sum, the move at
`(d, +)` and at `(d, =)` turning by `d + 1` tenths, every other pair holding, and every row exact
(0 failures). The `+ 1` on each crossing and the `+ 2` in `ψ` are the gauge: the two crossings add
`(a₀ + 1) + (b₀ + 1) = a₀ + b₀ + 2`. The torsion primes' products are tried in ascending order;
modulo 2 or 5 alone ten arriving classes cannot be told apart, and 10 is the first modulus that
tells them all. Eleven is torsion as well, and its part is not spare: modulo 11 each line's loop closes on
the operands' and the sum's alternating digit sums, `a + b − c ≡ 0` (casting out elevens), so the
two parts together fix the sum modulo 110; the units key alone is what tells the arriving units
apart. No digit, no base and no sum was named to the founding: the key is located from the
passage's arrivals.

**The ring under the closure key.** The ring's push and readout are founded under the located
moves (`found-tower-ring … pair-moves`, 117 s). Its exact share is 1.834 from the unit start,
against the ceiling's 1.876. Its outside read carries the held-out units at `U` in 469 of 495
(the ceiling's 415): 242 of 256 two-digit sums and 227 of 239 three-digit ones; at `E`, 253 and
235. By the operands' lengths: one digit and two, 44 of 50; two and one, 38 of 44; two and two, 387
of 399. The carriage is located.

**The readout reads only its first turn.** Founded to its precision as the last loop's readout was
(three Newton rounds saving 12,580, 2,147 and 245 nats against 910), the tower's own guess at `U`
is right in 337 of 495 at 1.862 bits a digit (the last loop's 308 and 1.977; the foil 40 and
3.397). The ring's part alone picks 195, the rest 48. Most errors are a neighbouring digit (1 for 2
in 12 sums, 0 for 1 in 17, 9 for 8 in 11). The units' turns stand apart but compressed on the
circle (`RING_PHASE_CENTROIDS.txt`): the digits 9, 0, 1, …, 8 at mean turns of 1, 23, 46, 68, 91,
116, 144, 191, 277 and 329 degrees, each class's resultant 0.92 to 0.997. The readout `W (x̂ ⊗ ρ)`
reads the turn through one cosine, whose peak is wide against classes 23 degrees apart. A
nearest-centroid read of the same turns (leave one out) reads 465: the turns separate the digits;
the readout's one cosine does not. The held-out text reads 2.975 bits a byte after the
founding (2.580 the last loop), its readout rows founded on the arithmetic block alone.

**The readout at every harmonic of the key** [agent-inferred] (`RingFace::with_harmonics`). A
function of a turn that stands on `n` residues is spanned by the turn's harmonics `1, …, ⌊n/2⌋`
and a constant: a discrete Fourier series on `ℤ/n`. So a ring keyed modulo `n` is read at
`H = ⌊n/2⌋` harmonics, `q_1 = ρ` and `q_h = q_(h−1) ρ / ‖ρ‖` rounded to the face's grain (each the
turn taken `h` times, at the face's length), and the readout reads `x̂ ⊗ (q_1, …, q_H)`. The join
reads the key's modulus from the founded forms (`key_modulus=10`, so `H = 5`, 650 channels in place
of 130); nothing names the harmonics but the key. The reverse carries each harmonic's covector back
to the first, `∂ρ += t (−ρ_im, ρ_re)/‖ρ‖²` with `t = Σ_(h≥2) h (G_im q_re − G_re q_im)` before the
ratio's own adjoint: a harmonic moves only the turn. The readout's founding takes the code's
curvature within each harmonic's channels, five blocks of 130 for each class: two harmonics'
cross block averages toward zero over a turn that runs round the circle, as the classes' cross
blocks are dropped, and a block-diagonal curvature is positive, so its step descends and the
exact code's line fixes its scale.

[formal-checked, October 27] Both halves hold in exact arithmetic, in
[`HNN/RingHarmonics`](../../lean/HolonicsResearch/HNN/RingHarmonics.lean). Every real function on
`ℤ/n` is `a + Σ_(1≤h≤⌊n/2⌋) (b_h cos(2πhk/n) + c_h sin(2πhk/n))` (`harmonic_expansion`: the discrete
Fourier inversion, each frequency past `⌊n/2⌋` folded onto `n − j`), and on the residue's face
`r e^(2πik/n)` the harmonic `q_h` is `r e^(2πihk/n)` (`harmonic_residueFace`), so the readout affine
in the harmonics' parts reads every function of the residue (`ring_read_at_harmonics`). Along the
turn the reading `Σ_h ⟪G_h, q_h⟫` moves at `⟪∂ρ, iρ⟫` for the covector above
(`hasDerivAt_reading_turn_adjoint`); along the radius it moves by `⟪∂ρ, ρ⟫` plus the harmonics'
radial part, which `∂ρ` omits (`hasDerivAt_reading_radial_split`), and through the ratio
`ρ = r q/|q|` the radius does not move the reading (`hasDerivAt_ratio_radial`), so the omission is
exact.

Three rounds saved 18,950, 5,603 and 1,747 nats against the 4,550 that 650 · 14 free parameters
ask; the founding read the block at 2.288 bits a byte before, 2.188 under the one-cosine readout
and 2.112 under the harmonics, in 545 s against a projection of 1,020 s (deadline 1,080 s).

| ring21's ring, readout founded by Newton rounds | whole right at `U` (of 495) | ring's part alone | rest alone | ring's margin, median | bits a digit at `U` | held-out text, bits a byte |
|---|---|---|---|---|---|---|
| one cosine (130 channels) | 337 | 195 | 48 | −0.40 bits | 1.862 | 2.975 |
| **five harmonics (650 channels)** | **475** | 437 | 48 | 2.70 bits | **0.623** | 2.968 |
| the foil: the same pass without the ring | 40 | - | - | - | 3.397 | 2.458 |

**The acceptance is met**: after one training pass (the survey, the ring's founding by loop
closure and the readout's founding, each to its precision), the tower's own top guess at `U` is the
held-out sum's units in 475 of 495 (bar 370), and its code there is 0.623 bits a digit against the
foil's 3.397. By the operands' lengths (`RING_SPLIT.txt`): two digits and two, 390 of 399; one and
two, 42 of 50; two and one, 41 of 44; one and one, 2 of 2. Fifteen of the twenty misses are one
digit off (nine above, six below), eight of them on sums whose first operand has one digit.

**What it says** [agent-inferred]:
- The carriage was located by the machine: the key modulo 10 is the closure system's own torsion,
  read from the passage's crossings. The readout was what kept it from the guess, and the key also
  sets the readout's width: `⌊n/2⌋` harmonics read every function of the turn.
- The tower's guess passes the outside centroid read of the same turns (475 against 465 at one
  harmonic and 467 at five): the top face tells the readout where the turn is news.
- The held-out text codes worse than the foil (2.968 against 2.458 bits a byte). The readout's
  rows are founded on the arithmetic block alone, so at prose cells the ring's turn enters the
  logits with weights no prose cell set. A reading beside the acceptance, and the next loop's
  subject.

**Decided next** [agent-inferred]: found the readout on the mixed training passage (the Holonics
text with its arithmetic), so that its rows are set where the ring's turn is news and where it is
not. Its acceptance: the held-out text codes no worse than the foil's 2.458 bits a byte while the
held-out units stay at or above 370 of 495.

## The readout founded on the four media

The last loop decided the passage: found the readout on the mixed training text, 856,045 bytes of
the Holonics text in prose, Lean and Rust with the arithmetic block after it (from byte 639,914),
so that its rows are set where the ring's turn is news and where it is not. The acceptance was
fixed before the run: the held-out text codes no worse than the foil's 2.458 bits a byte while the
tower's own guess at the held-out units stays at or above 370 of 495.

**The curvature on its grain.** Over 168 arriving classes the founding's curvature has
143,815,392 (cell, class) pairs. It is now carried on `2^(−12)` of `p(1 − p)`: a pair whose
curvature falls below `2^(−13)` adds none, and the round prints the pairs that stay live and the
curvature released before it accumulates (25,416,494 live; 2,090 parts in a million released).
The control, the same founding on the arithmetic block at this grain, reads the held-out units in
475 of 495 at 0.619 bits a digit (0.623 at the full grain), and the held-out text at 3.042.

**Two foundings that did not move.** On the four media the founding saved 0.281 nats with one
scale for every row and 0.332 with each row on its own scale under a one-bit trust; both left the
tower at its base reading (48 of 495, the held-out text 2.448). A check placed the cause: the
arithmetic-only readout read behind the passage's last 100,000 bytes of text, before the held-out
sums, still reads 475 of 495, as from rest. The prose before the sums does not hide the ring's
turn. (The first launch of that check, with all 639,914 bytes before the sums, stopped at its
deadline, 651,890 of 651,912 bytes read; the prefix was shortened, not the deadline raised.)

**The cause: the Newton step's units** [agent-inferred, October 25]. A cell's offset is
`(w·φ)·2^(−24)` on `2^(−16)` of a bit, so its logit is `w·φ·2^(−40)` bits, and the code in bits has
gradient `p − q` and curvature `ln 2 · (diag p − p pᵀ)` in it. The solve takes the curvature on
`2^(−12)` and the covector on `2^(−24)`, so its solution `d_j = −H⁻¹m` is the Newton step on
`2^(−28) · ln 2` of a readout unit: the step is `d_j · 2^28 / ln 2`. Both foundings took `d_j`
itself, `2^28.5` short. On the arithmetic block one lift and one line served every row, and they
absorbed the factor; on the four media the rows' steps part by many octaves, and the one
row whose short step already moved an offset past a bit (its step reached `2^22` bits) set the
line for all. With the factor, every one of the 168 rows' Newton steps moves some cell's offset
past one bit (the widest by `2^50` bits), so each row takes the step that moves its largest offset
by one bit, where the log-sum's self-concordance keeps the curvature within a factor of four, and
the line scales them together.

The founding ran two rounds. The line took the first at 5.2 times its trusted step
(`κ = 341,079/2^16`), which saved 76,409 nats, and the second at 3.2 times it (`209,888/2^16`), which
saved 30,214, below the 54,275 that the 108,550 free parameters ask, so it stopped. It took 3,867 s
against a projection of 7,374 s (deadline 7,400 s), at a peak of 9.6 GiB.

| the readout founded on | whole right at `U` (of 495) | ring's part alone | rest alone | ring's margin, median | bits a digit at `U` | held-out text, bits a byte | prose | Lean | Rust | arithmetic |
|---|---|---|---|---|---|---|---|---|---|---|
| nothing (the ring joined, its readout at zero) | 48 | - | 48 | - | 3.488 | 2.448 | 3.067 | 2.364 | 2.067 | 2.294 |
| the arithmetic block (the control, at `2^(−12)`) | 475 | 435 | 48 | 2.60 bits | 0.619 | 3.042 | 4.109 | 3.169 | 2.754 | 2.136 |
| **the four media** | **469** | 305 | 48 | 0.42 bits | 0.959 | **2.335** | 2.969 | 2.242 | 1.968 | 2.162 |
| the foil: the same lap without the ring | 40 | - | - | - | 3.397 | 2.458 | 3.111 | 2.400 | 2.108 | 2.211 |

**The acceptance is met**: founded on the four media, the tower's own guess at the held-out units
is right in 469 of 495 (bar 370), and the held-out text codes 2.335 bits a byte against the foil's
2.458. By the operands' lengths (`RING_SPLIT.txt`): two digits and two, 385 of 399; one and two,
44 of 50; two and one, 39 of 44; one and one, 1 of 2.

**What it says** [agent-inferred]:
- Founded where the turn is not news as well as where it is, the readout keeps the units (469
  against 475) and stops costing the text: every medium of the held-out text codes below both the
  ring at zero and the foil, prose by 0.10 bits a byte, Lean by 0.12, Rust by 0.10 and arithmetic
  by 0.13 against the ring at zero. The rows founded at prose, Lean and Rust cells use the turn
  there. What the turn carries at those cells is not yet read.
- The units moved from the ring's part to the whole: alone, the ring's part names 305 (435 in the
  control) and its median margin falls from 2.60 to 0.42 bits. The digit classes' rows now weigh
  the turn against what the text's classes ask of the same channels, and the top face carries the
  rest.
- Nothing in the founding names a medium: the four media are one passage, and the split by medium
  is an exterior read of the held-out text.

**Decided next** [agent-inferred]: the tens. The closure the machine solved has torsion
`110 = 2·5·11`, and its key took the first modulus that tells the arriving units apart, 10. The
eleven part is the alternating digit sum (casting out elevens); read beside the units it fixes the
sum modulo 110, and the result's length, which the tower already places, fixes the rest (the
mathematics thread's
[newline closure record](2026-10-25_THE_NEWLINE_CLOSURE_HAS_TORSION_B_TIMES_B_PLUS_ONE_A_PAIR_KEY_CARRIES_THE_UNITS_AND_CASTS_OUT_ELEVENS_AND_SPLIT_BY_LENGTH_THE_CLOSURE_IS_THE_SUM.md),
§3 and §9). The next loop founds a second ring under the closure's eleven key beside the units
ring, joins both and founds the readout on the four media. Its acceptance: the tower's own guess
at the held-out sums' tens right in at least 370 of 495, the units staying at or above 370, and
the held-out text no worse than the foil's 2.458 bits a byte.

## The tens, under the closure's whole torsion

The last loop decided the tens: the closure the machine solved at the sums' units has torsion
`110 = 2·5·11`, and its key kept the first modulus that tells the arriving units apart, 10. The
acceptance was fixed before the run: the tower's own guess at the held-out sums' tens right in at
least 370 of 495, the units staying at or above 370, and the held-out text no worse than the foil's
2.458 bits a byte.

**The tens' own landmark closes on nothing.** A landmark at the cell before each sum's tens digit
(`tools/landmarks.py`, kind `sum-tens`: 8,966 marks on the arithmetic block, 495 held-out cells)
gives every origin's loops a closure without torsion (the newline origin's minor is 1): no key
there separates the tens. This is expected: the tens are not read from the digits that arrive
before them alone, since the units' carry enters, and a modulus exists only where the closure has
torsion.

**The key keeps the whole torsion** [agent-inferred, October 25]. The key once took the smallest
modulus that separates every arriving class. At the sums' units that kept 10 and dropped the eleven,
which reads the alternating digit sum: the units key gives the sum modulo 10, the eleven key modulo
11, together modulo 110, and the result's length, which the tower already places, fixes the rest
for operands of at most two places (the mathematics thread's
[newline closure record](2026-10-25_THE_NEWLINE_CLOSURE_HAS_TORSION_B_TIMES_B_PLUS_ONE_A_PAIR_KEY_CARRIES_THE_UNITS_AND_CASTS_OUT_ELEVENS_AND_SPLIT_BY_LENGTH_THE_CLOSURE_IS_THE_SUM.md),
§§2–3). The key now joins the torsion primes' keys over their subsets in descending product and
takes the first that separates the arriving classes: the whole torsion where it does. Founded again
at the units landmark, the newline origin closes with torsion `2:1, 5:1, 11:1` and the key modulus
110 (146.5 s). Its kept start (the origin's) has exact share 0.865 at the units cells, read on the
turn's first character as the founding reads it, against 1.834 under the key modulo 10: one
character of the 110 turn carries less of the units than one of the 10 turn.

**The whole turn, read at every character.** Joined at `⌊110/2⌋ = 55` harmonics with its readout
at zero, the tower codes as the tower alone: its own guess at the held-out tens is right in 311 of
495, at the units in 48. Read outside (`RING_TENS_CENTROIDS.txt`), the turn at the tens cells holds
the tens classes in order around it on its first character, from 35.9 degrees for a tens of 0 to
342.5 for 8, with the 9s at 28.2 beside the 0s (the sums in the nineties lie beside those from 100
to 109, the only sums here whose tens are 0), each class's resultant 0.76 to 0.99. At
the units cells, after the tens are written, it holds the units classes 1.9 degrees apart (76.0 to
93.5 degrees), each resultant 0.996 to 0.998: their spread is wider than their parting. By the
nearest class centroid with each cell left out, the tens are named in 146 of 495 on the first
character, 172, 252 and 323 on the first two, three and four, 320 to 324 on four to eleven, 340 at
best on 22 and 318 on all 55; the units in 130 to 142 on every count.

The readout founded on the arithmetic block at all 55 harmonics has 7,150 channels and 100,100
free parameters over 15 arriving classes. Its one round saved 15,424 nats, below the 50,050 its
free parameters ask, and the founding stopped (1,873 s against a projection of 3,400 s; deadline
3,600 s). The tower's own guess at the held-out tens is right in **428 of 495** at 0.597 bits a
digit (the turn's part alone 266, the rest 311); at the units it falls to **156** (the units ring
founded alone on the same block reads 475). The whole held-out text was not read: at 55 harmonics
the read ran past its 60 s deadline, a deadline set from the five-harmonic reads without a
projection of its own, and the figure is reported incomplete.

**Where the passage's code lies on the characters.** Before its trust and line, the round's Newton
model predicted each harmonic's saving (`½ gᵀH⁻¹g` on the harmonic's own block, summed over the
rows): 222,948 nats in all, 14 times what the round saved. The first five characters hold 44,930
of it, the first eleven 92,222, and the multiples of eleven stand above their neighbours (9,069 at
the 11th against 7,433 and 6,771 beside it; 5,757 at the 22nd; 3,273 at the 33rd; 2,225 at the
44th). On an exact 110 turn the eleventh character, `e^(2πi·11x/110) = e^(2πi x/10)`, reads `x`
modulo 10 alone, the units ring's first character; the predicted savings lean there, but the
founded turn read outside does not part the units on any count of characters [agent-inferred].

**What the founded turn resolves** [agent-inferred]. The turn the tower carries is founded, not
exact. At the tens its first four characters carry what the centroid read names (323 of 495), and
the next seven add nothing (320 to 324); the founding spread its free parameters over all 55 alike
and paid for them with curvature the passage could not fill. So the 110 ring is read at five
characters, declared by the run (`join-tower-ring … harmonics=5`) with this reading beside it; the
key's own count, `⌊n/2⌋`, stays the join's default.

**Two rings side by side.** At five characters the 110 turn does not carry the units, and the
units ring's readout, founded on the four media, does. So the two rings ride the one placement mode
side by side: the units ring under its key modulo 10 and the 110 ring under the whole torsion, each
at five characters. A ring's pair moves are now one table a rank (`RingFace::new` takes a table for
each rank; `RingFace::moves_at` gives each rank's move at a pair, and the reverse sums a rank's
covector into the pair's mode move only where that rank rides the mode). Two regressions hold: the
units ring joined alone writes the learner byte for byte as before (sha256 `e9c2de64…`), and the
units ring's four-media learner reads the held-out units line for line as before. Joined, the two
rings carry 532,614 words of material against 365,699 with the units ring alone.

The units ring's readout is already founded on the four media to its precision. Founding both
rings' channels on that passage would widen each harmonic's block to both ranks' channels: four
times the curvature and eight times the solves of the last founding, whose two rounds took 3,867 s.
So the join carries the founded readout (`readout=LEARNER,SHA`, refused unless that learner's ring
is this one's leading rank on the same tower, with its moves and harmonics) and the founding holds
it (`found-ring-readout … held=1`): a coordinate step on the new rank's channels from the face the
held rank already moves, the curvature between the ranks dropped as between two harmonics. The
carriage is exact: the joined learner reads the held-out units as the units ring's learner did, 469
of 495 at the same code to the unit.

**At five characters, on the arithmetic block.** With the units ring held at zero, the 110 ring's
readout founded on the block (650 channels, 9,100 free, two rounds saving 10,202 and 2,176 nats
against 4,550; 398 s against a projection of 767 s) reads the held-out tens in **442 of 495** at
0.374 bits a digit, against 428 at 0.597 with all 55 characters (the turn's part alone 260, the
rest 311). The units fall to 124 (the units ring's readout is at zero here), and the held-out text
codes 2.439 bits a byte against the tower alone's 2.448. The first five characters' predicted
savings in round 0 equal ring27's to the nat: holding a rank at zero leaves the new rank's blocks
as they were.

**The four media, first launch: stopped on evidence.** The two rings joined with the units ring's
four-media readout carried (sha256 `62c52122…`) and the 110 ring's readout founded on the four-media
passage, the units ring's held. The projection took the largest measured units, scaled by the
block's two-rank ratios: the read 419 s, a round 1,749 s, at most three rounds under the precision
rule, the moments 258 s; 5,924 s, deadline 6,000 s, and a stop if no round-0 line stood by 2,200 s.
The read took 396.9 s. Round 0's curvature took 1,086.6 s against ring26's 853.1 s for the same
channels and classes (1.27 times, where the block's held round had run 1.05 times ring23's) and
its solves 629.4 s, so the round passed its share before its line and the run stopped at 2,200 s.
It is reported incomplete. The projection's error is the block-to-passage ratio, which held for the
read and not for the curvature. Its Newton model's predictions on the four media are no reading
[agent-inferred]: thin rows' released curvature is not positive there, and the model returns
values of either sign past `10^12` nats; the one-bit trust bounds those rows' steps.

**The repair: the sums as wide as their terms** [agent-inferred, October 25]. A curvature term is
below `2^52` (`|φ| < 2^21`, the curvature on its grain at most `2^10`) and a covector term below
`2^45`, yet every sum was carried 128 bits wide from its first term. The sums are now carried 64 bits
wide and cross into 128 every `2^11` live cells: the precision law's dynamic width, a carrier as wide
as its terms need, widened at a declared crossing. Integer addition is exact in any grouping, so the
founded readout is the same integers.

Founded again on the arithmetic block with the units ring held, the 64-bit sums write the same
learner to the bit (sha256 `c8a7c103…`, both rounds' codes and steps alike). Its rounds take 79.9
and 82.5 s against 121.2 and 120.7: the curvature 17.9 and 19.5 s against 65.3 and 63.1 (0.27 and
0.31 of it), while the solves, now the larger part, take 55.3 and 56.6 s (49.7 and 51.7 before).

**The four-media founding, larger than its question** [agent-inferred, October 25]. Under the 64-bit
sums the four-media founding projected at 4,369 s: the read 398 s, at most three rounds of 1,230 s
(the curvature 336 s, the solves 700 s, the line 193 s), the moments 280 s, over 168 arriving
classes and 24.9 million live pairs against the block's 15 and 2.0 million. Nothing the acceptance
asks needs that founding. The tens are coded only on the arithmetic; the units ring's
readout is already founded on the four media and carried; and the whole held-out text is read
whichever passage founds the new rank. So the 110 ring's readout is founded on the arithmetic
block with the units ring's four-media readout carried and held (`ring/joined28m.state`,
`held=1`), and the four-media founding was not launched.

**The acceptance is met.** Founded on the block (650 channels, 9,100 free; two rounds saving 7,689
and 1,545 nats against 4,550; 408.0 s against a projection of 649 s, run beside the code checks),
the tower's own guess at the held-out sums' tens is right in **463 of 495** at 0.304 bits a digit,
at their units in **473 of 495** at 0.781 (469 before the tens were founded), and the held-out text
codes **2.334 bits a byte** against the foil's 2.458. Its first launch ran both rounds and failed to
write its state on a full disk (old debug builds had filled the session's disk); launched again
under the same deadline once they were cleared, its rounds' codes and savings are the first
launch's to the unit.

| the readouts | tens right (of 495) | bits a digit at `T` | units right (of 495) | bits a digit at `U` | held-out text, bits a byte | prose | Lean | Rust | arithmetic |
|---|---|---|---|---|---|---|---|---|---|
| the units ring alone, founded on the four media | - | - | 469 | 0.959 | 2.335 | 2.969 | 2.242 | 1.968 | 2.162 |
| both rings, the 110 ring's founded on the block, the units ring's at zero | 442 | 0.374 | 124 | 2.844 | 2.439 | 3.082 | 2.375 | 2.077 | 2.223 |
| **both rings, the 110 ring's founded on the block, the units ring's four-media readout held** | **463** | 0.304 | **473** | 0.781 | **2.334** | 2.986 | 2.254 | 1.981 | 2.114 |
| the foil: the same lap without the ring | - | - | 40 | 3.397 | 2.458 | 3.111 | 2.400 | 2.108 | 2.211 |

By the operands' lengths (`RING_SPLIT.txt`), the tens: two digits and two, 375 of 399; one and
two, 45 of 50; two and one, 41 of 44; one and one, 2 of 2. The units: 389 of 399, 44 of 50, 39 of
44, 1 of 2.

**What it says** [agent-inferred]:
- The tens are named by the whole face, not by the rings' part alone. Both rings' readouts
  together name 74 of the tens (260 with the units ring's readout at zero), their median margin
  falls from 0.13 to −1.53 bits, and the rest alone names 311; the whole names 463. At the tens
  cells the units ring's readout, founded where the units are coded, pulls the rings' part toward
  its own classes, and the 110 ring's rows, founded against that carried face, move the whole.
- The units gain from the 110 turn read beside the key-10 turn: the rings' part alone names 360
  of the units against 305, and the whole 473 against 469.
- Founded on the arithmetic alone, the new rank pays the arithmetic (2.162 to 2.114 bits a byte)
  and costs each other medium a little (prose 2.969 to 2.986, Lean 2.242 to 2.254, Rust 1.968 to
  1.981); the whole held-out text is one thousandth lower (2.335 to 2.334). The new rows never met the turn at
  prose, Lean or Rust cells.

**Decided next** [agent-inferred]: the tower writes the sums itself. Every reading so far names a
digit with the true characters before it; a written sum feeds the tower its own characters, so a
wrong length or tens is carried into the units. The next loop releases each held-out sum from its
line's prompt, character by character from the tower's own guess, and shows the written sums whole.
Its acceptance: the whole written sum right in at least 370 of 495, with the held-out text at or
under the foil's 2.458 bits a byte.

## The tower writes the sums itself

The loop's acceptance was fixed before the run: written by the tower itself from each held-out
sum's prompt, the whole sum right in at least 370 of 495, with the held-out text at or under the
foil's 2.458 bits a byte.

Each held-out arithmetic line opens on the state the true earlier lines left; at its `=` a fork
releases the rest class by class, each class fed back as the next one read, at 64 agreeing draws
(the face `m^64 / Σ m^64`, near the top class), until it releases a line end or the true length and
five more (`read-lines-stream`; 18.7 s for the 1,253 lines, against a projection of about 15 s and a
deadline of 60 s). The learner is the one that met the tens acceptance (both rings, sha256
`b3ff0e58…`), so the held-out text is its 2.334 bits a byte.

**The acceptance is met.** The tower writes **445 of the 495** held-out sums whole and right, their
length right in 493 (`WRITTEN_SUMS.txt`; every written line in `LINES_founded30_arithmetic.tsv`).
The tower before the tens ring joined, on the same keys, writes 304 (`LINES_founded26m_arithmetic.tsv`).

| the learner | sums written whole and right (of 495) | never met in training (of 248) | met in training (of 247) | length right | two digits and two (of 399) | one and two (of 50) | two and one (of 44) |
|---|---|---|---|---|---|---|---|
| both rings, the tens readout founded on the block | **445** | **219** | 226 | 493 | 367 | 40 | 37 |
| the units ring alone | 304 | 153 | 151 | 475 | 261 | 25 | 17 |

**Seen material, read apart.** The held-out file is never training text, yet 247 of its 495 sum
lines also stand whole in the training passage (the arithmetic block or the four media): two-digit
operands give only so many sums. Read apart, the tower writes 219 of the 248 it never met right and
226 of the 247 it met. It computes the sums it never met almost as often as those it did, and the
acceptance holds on the never-met lines alone at the same rate (219 of 248 is 437 of 495 at that
rate) [agent-inferred]. The reads at `T` and `U` above count both kinds alike.

**Where the writing goes wrong** [agent-inferred]. Of the 50 wrong sums, 26 carry out of the units
(of 223 that do) and 24 do not (of 272): the wrong ones are not the carries. Twenty are wrong in the
tens alone, 16 in the units alone, 12 in both and 2 in the length. Differences (17 of 268 right) and
products (6 of 490) are written as before: the rings are founded where sums are coded, and nothing
in the machine has met a landmark at a difference or a product.

**Decided next** [agent-inferred]: the differences, by the same machine. A landmark at the cell
before each difference's units (received material from each line's shape, handing no value), the
closure founded there by loop closure, its ring joined beside the two, and its readout founded on
the arithmetic block with both rings' readouts held. Its acceptance: the tower writes at least 201
of the 268 held-out differences whole and right (three in four, as for the sums), the sums staying
at or above 370 written right, and the held-out text at or under 2.458 bits a byte.

## The differences by a ring of their own, and the reflection they lack

The loop's acceptance was fixed before the run: the tower writes at least 201 of the 268 held-out
differences whole and right, the sums staying at or above 370, and the held-out text at or under
2.458 bits a byte.

**The ring.** A landmark at the cell before each difference's units (`tools/landmarks.py`, kind
`diff-units`: 4,548 marks on the arithmetic block) gives the newline origin a closure with torsion
`2:1, 5:1` and the key modulus 10 (`RING_DIFF.txt`). The key reads the minuend's units at `−` and
the subtrahend's at `=` with opposite turns: `θ(d, −) = d + 1`, `θ(d, =) = 9 − d`, every pair out of
the newline 2, and `ψ(c₀) = c₀ + 2`, so the turn at the mark is `a₀ − b₀ + 2`. The ring founded there
(100.6 s against 146.5 s projected) was joined beside the units ring and the 110 ring at five
harmonics each, and its readout founded on the arithmetic block with both other readouts held (two
rounds saving 7,447 and 1,965 nats against the 4,550 its 9,100 free parameters ask; 364.2 s against
535 s projected).

**The acceptance fails.** The tower writes **129 of the 268** held-out differences whole and right
(17 before the ring), 65 of the 143 it never met; the sums fall to 424 of 495 (from 445), the held-out
text codes 2.338 bits a byte (`WRITTEN_SUMS.txt`, every line in `LINES_founded31_arithmetic.tsv`).
Of the 139 wrong differences, 68 are wrong in the tens alone, 16 in the units alone, 27 in both and 28
in the length: the units ring of the differences carries their units, and nothing carries their
tens. A landmark at the cell before each difference's tens (kind `diff-tens`, 3,691 marks) closes on
nothing: no origin's closure has a key that separates the tens (40.0 s, refused).

**What the closure lacks** [agent-inferred, joined to the mathematics thread's derivation]. The
mathematics thread's newline closure of written differences
([§10](2026-10-25_THE_NEWLINE_CLOSURE_HAS_TORSION_B_TIMES_B_PLUS_ONE_A_PAIR_KEY_CARRIES_THE_UNITS_AND_CASTS_OUT_ELEVENS_AND_SPLIT_BY_LENGTH_THE_CLOSURE_IS_THE_SUM.md#10-differences-the-torsion-is-2b-and-the-minuends-length-is-its-cause))
has torsion ℤ/20: the one digit-pair move has to count the minuend's tens with `+b` and the
subtrahend's with `−b`, so `2b ≡ 0`. Its two-part is ℤ/4, which a key built from the torsion primes
alone reads as ℤ/2, as this ring's key did (10). The conflict is the hand: a pair key adds a fixed
turn a pair, a rotation, and never reverses the hand, while the subtrahend is read with the hand
reversed (§8 there: the move the closure lacks is the reflection, the dyad `U` of the helical code,
on the ring `z ↦ ωᵈ z̄`). Brandon's lens, October 25, says the same from the other side: `−` is not
another kind of thing beside `+`; it is `+`'s cycle with its polarity reversed, as in algebra, so
the differences should not need a mechanism of their own.

**Decided next** [agent-inferred]. The ring's pair moves may reflect, and the machine locates where.
- A ring move is already `h ↦ λh + βh̄`: a rotation where `β = 0`, a reflection where `λ = 0`. Each
  rank carries its hand, the parity of the reflections since its last restart, and is read in its own
  hand, `(Re h, ±Im h)`. A turn met after a reflection then counts with the reversed hand, so a
  closure row counts each pair with the hand in force where it is met.
- The closure is solved with no reflector and with each class the rows meet as the reflector, and
  keeps a key that closes the loops exactly (its rational kernel) before one that closes them modulo
  its torsion, and a larger modulus before a smaller. No reflector is named to it.
- What this predicts, to be read off the closure: on the differences' units alone, `−` as the
  reflector removes the `2b` conflict, so the closure is exact and holds the whole difference. On the
  sums' and the differences' units together, exactly one of `+` and `−` reflects (which one is a
  gauge), and the one ring keys the units of both; the result still enters with one hand against
  the left side in a sum and the other in a difference, so the shared key stops at the units.
- The acceptance of the first loop: the closure, given the sums' and differences' units together and
  no reflector, locates `+` or `−` as the reflector with a key that separates every arriving class;
  given the differences' units alone, it closes exactly with `−` or `+`. The writing's acceptance
  stays: at least 201 of 268 differences and 370 of 495 sums whole and right, the held-out text at or
  under 2.458 bits a byte.

## `−` is `+` reversed: the ring's hand reflects and restarts, and the closure locates where

Brandon's lens (October 25): the mechanism behind the landmarks `+` and `−` is one mechanism with a
polarity; `−` is `+`'s cycle reversed, as in algebra, so the differences need no mechanism of their
own. The last section decided the build; this one is its loop.

**The hand** [agent-inferred]. A ring move `h ↦ λh + βh̄` keeps the ring's hand where its
determinant `|λ|² − |β|²` is positive, reverses it where negative (a reflection: `λ = 0`, or `β`
outweighing `λ`), and restarts it where zero (a collapse, the origin's zero move), `hand_after`.
Each rank is read in its own hand, `(Re h, ±Im h)`, and its covector carries the hand back. A rank
may also restart its hand at a class (`RingFace::with_restarts`): where that class arrives on a
reversed hand, the ring is re-based into the hand it reads, `h ↦ (Re h, −Im h)`, its read there
unchanged. A reflection between restarts then reverses exactly the turns met between them, which
is the mathematics thread's composition of two reflections into a turn
([its §11](2026-10-25_THE_NEWLINE_CLOSURE_HAS_TORSION_B_TIMES_B_PLUS_ONE_A_PAIR_KEY_CARRIES_THE_UNITS_AND_CASTS_OUT_ELEVENS_AND_SPLIT_BY_LENGTH_THE_CLOSURE_IS_THE_SUM.md#11-with-the-hand-reversible-a-reflection-at--reads-every-difference-and-with-a-restart-at--one-key-reads-sums-and-differences)).
The library's tests check the hand against a replica of the read, the covector against the code
difference with reflections and with restarts at every class, and the face's text. The hand's law is
formal-checked (October 26, [`HNN/RingHand`](../../lean/HolonicsResearch/HNN/RingHand.lean)): the
move's matrix is `ring_carry` and its transpose `ring_carry_adjoint` (`handMatrix_mulVec`,
`transpose_handMatrix`), its determinant is `|λ|² − |β|²` (`det_handMatrix`), the re-basing is an
involution whose covector is `(g_x, −g_y)` (`flipY_mul_self`, `flipY_adjoint`), and the hand that
`hand_after` reaches from rest makes `o · ∏ det M_i > 0` (`hand_from_rest_reads_positive`).

**The closure locates the reflector and the restart.** Each origin is solved with no reflector and
with each other class as the reflector; each closure row counts every pair with the hand in force
where it is met. A restart is then sought beside each reflector whose closure keys, with each third
class. A key that closes the loops over the integers (a vector of the rational kernel whose
`ψ` tells the arriving classes apart) is kept before a torsion key. No reflector or restart is
named to it.

**What the search cost, and the echelon kept reduced.** Solving every origin with every reflector
and every restart at once (2,955 closures on the sums' and differences' units) ran at 1.4 closures a
second against the 4.2 projected and was stopped at 210 (`ring/found32sd.txt`, 188 s). Solving the
origins one row count at a time saved nothing, as nearly every origin precedes every mark; all three
runs reached their deadlines (360, 150 and 200 s). Seeking the restart only beside a reflector that
closes (225 closures, then a restart beside each keyed reflector) was stopped on its rate: 79, 174
and 129 closure lines in the first minute against the 84, 225 and 222 projected. The cost was the
echelon over a prime: each arriving row was reduced by every basis row in turn and the basis
back-substituted once at the end. It is now kept reduced as rows arrive: a row is reduced only by the
basis rows at its own nonzero pivot entries, and a new pivot column is cleared from the basis when
it enters. The echelon is the same, since the reduced row is the one vector of its coset that
vanishes at every pivot (the library's test compares it with the in-order reduction over six primes
and four stops). The closures then ran at 6.7 a second on the differences' units (277 in 41.6 s),
5.6 on the sums' and 3.8 on both (251 in 65.8 s), within their projections.

**What the closure located.**
- On the differences' units alone (4,548 marks), `−` reflecting closes the loops **exactly**: the
  key is a vector of the rational kernel, with no torsion, `ψ(c₀) = 9 − c₀`, the turns
  `θ(d, −) = d + 1` and `θ(d, =) = 9 − d` (`ring/found35d.txt`). Without the reflector the same marks
  close only modulo 10, the `2b` conflict of the last section. No restart improves it.
- On the sums' units alone (9,018 marks), no reflector is needed: the newline origin keys modulo
  `2·5·11 = 110`, the units ring's own key (`ring/found35u.txt`).
- On both together (13,566 marks), the closure with no reflector has torsion `2:1` and no key, and
  `+` or `−` reflecting alone keys modulo 10. **`−` reflecting with `=` restarting** keys modulo
  `2·5·11 = 110` with no failure, and it is the only choice of the 251 that does: `+` reflecting with
  `=` restarting keys modulo 10 (`ring/found35sd.txt`, `RING_REFLECT.txt`). Its turns: a sum's
  operand units `θ(d, +) = θ(d, =) = 11(d + 1)`, a difference's minuend units
  `θ(d, −) = 99 − 11d`, the newline's `#10d` turns `82 − 10d`, `θ(+, d) = 108 − 10d` and
  `θ(−, d) = 90 − 10d`, all modulo 110.

So the machine, told nothing of either sign, found `−` to be `+` with the hand reversed from `−` to
`=`, and one key reads both. This is the mathematics thread's §11 table, located rather than named.
The prediction of the last section was half right: one of `+` and `−` reflects, but which one is
not a gauge once the hand is restored at `=` (`+` reflecting with `=` restarting keys modulo 10
only), and the shared key does not stop at the units in the arithmetic: modulo `110` it holds the
result's elevens beside its units. Whether the ring founded there carries them to the tens is the
writing's question.

**The writing.** The ring founded at the kept key (203.4 s against 346 s projected, its exact share
1.006) was joined as a fourth rank beside the units ring, the 110 ring at the sums' tens and the
differences' units ring, at five harmonics each with their readouts carried. Its readout, founded on
the arithmetic block with the other three held, took one round saving 4,461 nats against the 4,550
its 9,100 free parameters ask (277.4 s against 486 s).

**The acceptance fails.** The tower writes **144 of the 268** held-out differences whole and right
(129 before the joint ring), 74 of the 143 it never met; the sums hold at 422 of 495 (424), and the
held-out text codes 2.414 bits a byte (2.338), under its bound but worse in every medium except
arithmetic: prose 3.135 (3.018), Lean 2.390 (2.278), Rust 2.093 (1.998), arithmetic 2.038 (2.056)
(`WRITTEN_SUMS.txt`, every line in `LINES_founded33_arithmetic.tsv`). Of the 124 wrong differences,
63 are wrong in the tens alone (68 before), 17 in the units alone (16), 19 in both (27) and 25 in
the length (28). At the differences' own tens cells the tower is right at 133 of 223 (112 before) at
1.34 bits a digit (1.57), and the joint ring's part of the guess names 2 of them. The sums lost
since the two rings wrote 445 are wrong in the units: 35 in the units alone, against 16 then.

**Why the tens stay** [an exterior reading]. The joint ring's first-harmonic turn at the
differences' tens is ordered by the tens, from 157° at 1 to 269° at 9, but crowded into 112° of the
circle with resultants 0.65 to 0.90, and a leave-one-out nearest-centroid read from its five
harmonics names 48 of the 223 (`RING_RANK_CENTROIDS.{py,txt}`). The ring was founded at the units
marks: its key reads the result's units where they arrive, and what it holds of the tens is what the
units' loop leaves on the circle a cell earlier, not a turn located at the tens. The sums' tens are
carried by a ring founded at their own tens marks (the 110 ring), and the differences' tens closed on
nothing in the last section, when the ring had no hand.

**Decided next** [agent-inferred]. The closure at the tens, with the hand: the sums' and the
differences' tens together (`sum-diff-tens`) and the differences' alone (`diff-tens`), each searched
for its reflector and restart as here. The prediction: `−` reflecting with `=` restarting closes the
tens of both with one key, as it closed their units, and the ring founded there carries the
differences' tens as the 110 ring carries the sums'. The acceptance stays: at least 201 of 268
differences and 370 of 495 sums whole and right, the held-out text at or under 2.458 bits a byte.

## The tens with the hand: the key located at the units, the ring read at the tens

The last section's acceptance stays: at least 201 of 268 held-out differences and 370 of 495 sums
whole and right, the held-out text at or under 2.458 bits a byte.

**The tens close on nothing, with the hand or without it.** The closure at the differences' tens
(`diff-tens`, 3,691 marks) and at the sums' and differences' tens together (`sum-diff-tens`, 12,657
marks), each searched for its reflector as above, keys on nothing: every origin, every reflector,
no torsion and no exact key (225 closures in 37.2 s and in 59.0 s; `RING_TENS_HAND.txt`). This is
the sums' tens' own result (two sections above) carried to the differences: a tens digit is not
fixed by the digits before it alone, since the units' carry, or borrow, enters.

**The key's torsion holds the tens.** The joint key located at the units reads, at the tens cell,
the whole result modulo 110. Its turns at `=` are `θ(=, d) = −10d` and its residues
`ψ(c₀) = c₀ + 102`, so a ring pushed at the newline alone and turned by the key holds
`c₀ + 102 + 10c₁ = c + 102` where the result's first digit arrives: for a result below 110, the
tens and the units both, in sums and differences alike. What reads it is a ring founded where it
is read. The founded joint ring was chosen by the share it gives where its key closes, the units,
and kept the start whose turn is crowded at the tens (the last section).

**The build** [agent-inferred]. The founding takes a second landmark, `pair-moves-at KEY_MARKS`:
the closure is solved at the cells it marks (the units of sums and differences), and the ring is
founded, its start kept by its share, at the cells the first marks (their tens). With both
landmarks the same, the key is ring35s's to the byte.

**What it founded.** With both landmarks the units, the key line is ring35s's to the byte (stopped at
the key, 98.3 s against 104 s projected). With the key at the units and the founding at the tens
(12,657 marks), the newline origin's ring keeps 772 per mille of the tens marks' exact share,
against 622 to 699 for the other starts (198.5 s against 197 s projected; `RING_TENS_HAND.txt`,
forms `c365c22d…`).

**Where the arithmetic line stops** [agent-inferred]. The ring is not joined or read. Brandon asked
(October 25) that arithmetic stop being the road while GSM8K, MNIST and LibriSpeech wait, and the
section above measured the cost of the last ring: every other medium of the held-out text coded
worse (prose 3.018 to 3.135 bits a byte) while arithmetic moved 2.056 to 2.038. The hand, the
closure and the key located at its own landmark are the library's and the example's; they are read
again where a GSM8K answer's arithmetic is the failure in front of the line, as one section of what
the tower hears.

## The recorded failures this step could repeat

- **Text run on its codec's grain as the exception.** This is the failure this step exposed: a
  moment byte chosen where digits ask. The lock now reads every medium alike, and the next loop
  places the moment where a located key fires, in any medium.
- **Bits read as progress.** The held-out code stands beside the writing, and the success reading
  is the lock. The block's join is read the same way: its code is shown beside its
  writing, which does not change in kind.
- **Seen material graded as unseen.** Held-out files are never training files. Held-out sum lines
  that also stand whole in the training passage are read apart from those it never met. The join's weight is
  chosen on the training text alone, and the held-out text is read at every weight. The lock splits met
  and unmet lines, and no held-out text line is met verbatim.
- **Catered machinery.** Nothing in the tower names a medium. The media are an exterior partition of
  the held-out text, and the moment byte was a declared exterior choice, which this step retires as
  the moment. The ring founding's landmark is received material placed from each line's shape: it says
  where a sum's units are coded, hands no value, and marks nothing on the held-out text.
- **A refusal answered with a larger limit.** The plain run stopped at its bound. It was continued
  under the largest measured pass, its own measurement, and reported here as stopped. The pair
  tower's foil stopped at its bound too. It is read at the state it reached and not continued.
  When the block's search left its 64-bit grain, the floor and `L`'s fraction were each moved once
  within the same word and the failure only moved; the repair was the elimination's order, and no
  deadline or width beyond the word was raised. The pair forms' first launch stopped on evidence at
  its first block, 1.001 of a bound that took the largest measured block alone. It was relaunched
  with a changed declared read, not a raised one: the projection takes every block measured before
  the launch (the stopped launch's among them), their largest plus their largest spread, as the stop
  rule's measured spread asks. The stop is reported here, and its log kept. The ring founding's
  refusal (three founded factors bounded together past 128 bits) was answered by a changed law,
  each factor released at its own bound before the product, not by a wider carrier. The ring's
  whole-text passes ran 1.6 times past the projection's rate and were stopped on that evidence; the
  step moved to a smaller partition (the arithmetic block), not a larger deadline. The founding run
  to a one-bit fixed point was stopped on evidence when its first start passed its share of the
  deadline; it was answered by a changed law, the precision rule, under which the founding's rounds
  are bounded before launch, not by a larger deadline. The closure founding's integer elimination
  was refused in `i128` and ran two origins past its deadline in `BigInt`; it was answered by a
  changed law, one exact minor read modulo primes with the rank certified, not by a wider carrier
  or a larger deadline. The context check behind the four media's text stopped at its deadline; it
  was answered by a shorter prefix, not a larger deadline. The whole held-out read at the 110
  ring's 55 characters stopped at its deadline and is reported incomplete; the ring is read at five
  characters, a changed declared read with its own reason, and the 55-character figure was not
  re-read under a longer deadline. The closure's search with the hand was stopped three times on
  its rate or reached its deadline; each was answered by a changed law (the restart sought only
  beside a reflection that closes, then the echelon kept reduced), never by a larger deadline.
- **A located cause carried unrepaired into a new consumer.** The founded ring entered the learner
  with its factors held in the frame of the tower it was founded on, and one pass of the tower's own
  learning dephased it. This is recorded as the step's failure, and the next loop carries the ring
  with the tower. The founded readout carried code and still did not keep the frame. Depositing
  the push's factors did not keep it either: the cause is the tower's own deposit under the ring,
  located by holding families one at a time, and a lap now deposits the bridge and leaves the
  founded constitution as it was founded. The readout founded to its precision then went into a lap and the lap
  undid it (308 to 247); the lap after a founding to precision is retired by the lap law, not
  answered by another hold.
- **An uncertified deposition step.** A founded family joined with its moments at zero moved at two
  to four times the rate on its first sections. Its moments now open on its founding passage, read
  without a deposit, and every step stays the certified one.
- **A run larger than its question.** The second four-media founding projected at 4,369 s, and
  nothing the acceptance asked needed it: founded on the arithmetic block with the units ring's
  four-media readout carried, the run that met the acceptance took 408 s. A run is sized by what
  its acceptance reads, not by the passage the last founding used.
- **An index of contexts counted as learning.** The pair face is carried at every pair. Which pairs
  the training text met is read only outside the machine, to split the held-out reading.
- **An authored routine standing in for learning.** The located moment is the passage tree's lock, a
  receiver of the machine's own kind, and no list of relation tokens. It chooses only where the
  exterior reading looks. Nothing in the tower reads it.
  The carriage's ceiling table is authored and read only as a ceiling; the move the learner keeps
  is located by loop closure, its modulus the closure system's own torsion, and the readout's
  harmonics are set by that modulus, or declared by a run beside the outside reading of what the
  founded turn resolves. No digit, base or sum is named to either founding. The tens landmark says
  where a sum's tens are coded and hands no value; the closure at it, which found no key, was not
  answered by naming one. No reflector or restart is named to the closure either: the reflection is
  the ring move's own hand, and which class reflects and which restores is located by the loops.

## Receipts

In [the receipts](2026-10-24_THE_TOWER_HEARS_THE_HOLONICS_TEXT_AND_EVERY_LOOK_IS_READ_BY_ITS_LOCK_receipts/):

- `MANIFEST.tsv`: the terrain's pieces.
- Training logs: `TRAIN_LOCK.txt`, `TRAIN_PLAIN_STOPPED.txt` and `TRAIN_PLAIN.txt` (the continuation),
  and the development passes in `DEV_PLAIN.txt` and `DEV_LOCK.txt`.
- The prompts, `PROMPT_<medium>.txt`, and each tower's writing, `WRITE_<tower>_<medium>.txt`, as
  bytes.
- `LOOKS_<tower>_<medium>.tsv` and `LINES_<tower>_<medium>.tsv`: every look and every line's codes.
- `READ_LOCK.txt`: the lock per medium (`tools/text_looks.py`).
- `RUNS.tsv`: each run's binary, command, projection, deadline, wall time, ratio and peak resident
  set.
- The pair towers: `DEV_PAIR.txt`, `DEV_PAIR_LINEAR.txt`, `TRAIN_PAIR.txt`,
  `TRAIN_PAIR_LINEAR_STOPPED.txt`; their writing `WRITE_{pair,pair8,pairlin8}_<medium>.txt`; their
  looks at `=` in `LOOKS_*` and `LINES_*` under the same names; `PAIR_RUNGS_*.txt`.
- The located looks, `LOCATED_LOOKS_<tower>_<medium>.tsv`, and their lock, `READ_LOCATED.txt`.
- The audit's writing, `AUDIT_WRITE_<tower>_<prompt>_a<draws>.txt`, and the digit prompt with its
  context, `PROMPT_arithmetic_ctx.txt`.
- Eight times the text: the terrain's pieces `BIG_MANIFEST.tsv`, the training log `BIG_TRAIN.txt`,
  the new Lean prompt `BIG_PROMPT_lean.txt`, the writing `BIG_WRITE_big_<prompt>_a<draws>.txt` and
  the htext1 pair tower's on the new Lean prompt `BIG_WRITE_pair_lean_a<draws>.txt`, both towers'
  located looks `BIG_LOCATED_LOOKS_{big,pair}_<medium>.tsv`, and their lock `BIG_READ_LOCATED.txt`.
- One more pass: `CONT_TRAIN.txt` (stopped on evidence after pass 0), the writing
  `CONT_WRITE_<prompt>_a<draws>.txt`, the located looks `CONT_LOCATED_LOOKS_<medium>.tsv` and their
  lock `CONT_READ_LOCATED.txt`.
- The tension: `TENSION_SLICE.txt` (the timing slice, 1,200 bytes of each medium's held-out text),
  `TENSION_DEV_cont.txt` and `TENSION_DEV_big.txt` (the held-out text through each tower),
  `TENSION_DEV_cont_starts.txt` and `TENSION_TRAIN_cont.txt` (line starts and the region added,
  held out and on the training text).
- The floor: `FLOOR_SLICE_1.txt` (the timing slice with all 256 count coordinates, stopped at its
  deadline), `FLOOR_SLICE_2.txt` and `FLOOR_SLICE_3.txt` (the arriving classes only, then with the
  chains run together: every reading identical), and `FLOOR_FULL.txt` (the training and held-out
  text, stopped at its deadline in the last step).
- The founding: `FOUND_SLICE.txt` (the timing slice, two ranks), `FOUND_FULL.txt` (the training and
  held-out text, four ranks, every step's line included), `FOUND_SLICE_SPECTRUM.txt` and
  `FOUND_FULL_SPECTRUM.txt` (the same with the ceiling's spectrum).
- The block: `BLOCK_SLICE_FAILED_1.txt` to `BLOCK_SLICE_FAILED_4.txt` (the slice under the search in
  the given order, each failure's line), `BLOCK_SLICE.txt` (the slice, largest diagonal first) and
  `BLOCK_FULL.txt` (the training and held-out text, 32 forms).
- The install: `INSTALL_SLICE.txt` (the timing slice), `INSTALL_FULL.txt` (32 forms joined, the
  training and held-out text), `INSTALL_FACE.txt` (the same with no forms), the writing
  `INSTALL_WRITE_<prompt>_a<draws>.txt` and the zero-weight check `INSTALL_WRITE_eta0_prose_a1.txt`.
- The pair forms in the learner: `FACE_JOIN.txt` (the join and the reach), `FACE_DEV_JOINED.txt`
  and `FACE_DEV_PLAIN.txt` (the 60 s development reads), `FACE_TRAIN_JOINED_STOPPED.txt` and
  `FACE_TRAIN_PLAIN_STOPPED.txt` (the first launch, stopped on evidence), `FACE_TRAIN_JOINED.txt`
  and `FACE_TRAIN_PLAIN.txt` (the passes), `FACE_CELLS_{start,joined,plain}.txt` (met and unmet
  pairs), the writing `FACE_WRITE_<state>_<prompt>_a<draws>.txt` as bytes, and the leverage
  `FACE_LEVERAGE_SLICE.txt`, `FACE_LEVERAGE_joined.txt` and `FACE_LEVERAGE_plain.txt`.
- Their second pass: `FACE2_TRAIN_JOINED.txt` and `FACE2_TRAIN_PLAIN.txt` (the passes),
  `FACE2_CELLS_{joined,plain}.txt` (met and unmet pairs), the writing
  `FACE2_WRITE_<state>_<prompt>_a<draws>.txt` as bytes, and the leverage
  `FACE2_LEVERAGE_joined.txt` and `FACE2_LEVERAGE_plain.txt`.
- The circuit at the result: `ANSWER_DIGITS.txt` (`tools/answer_digits.py` over the 37 digit-prompt
  writings), `CIRCUIT_{p1,…,p7,j6,j7}.txt` (`tools/tower_circuit.py` over each pass's reading:
  plain passes 1 to 7, joined passes 6 and 7) and `CIRCUIT_READS.txt` (each raw reading's state,
  cell count and SHA-256; the raw readings, 2.3 MB each, stay outside the repository).
- The flux at the units: `MODES_PROBE_<tower>_<operation>.txt` (the units probe: `pair7` the mixed
  pair tower at pass 7, `arith` the arithmetic terrain's pumped tower, `plain12` and `pair12` the
  first mixed terrain's towers), `MODES_FLUX_{pair1,pair7,arith}.txt` (each mode's push, kept share
  and orientation by role), `MODES_TURNS_{pair1,pair7,arith,plain12,pair12}.txt` (how each mode's
  move depends on the arriving digit), and `MODES_READS.tsv` (each raw mode reading's state, text,
  cells and SHA-256, wall time and peak; the readings stay outside the repository). The `after`
  reads' cells are `tools/tower_modes.py cells <text> A,B,E,U` (they reproduce byte for byte); the
  `full` reads name every cell of the held-out equations, 0 to 11,996.
- The situated pool: `SITUATED_RUNS.txt` (every founding's, read's and probe's log lines),
  `SITUATED_FORMS16.txt` (the sixteen real forms), their probes at four, eight, twelve and sixteen
  forms `SITUATED_PROBE_r{4,8,12,16}.txt`, the input covector's probe `COVECTOR_PROBE.txt`, the
  lookup at the probe cells `UNITS_LOOKUP.{py,txt}`, the tension's energy read from rest and as one
  passage `ENERGY_{FROM_REST,ONE_PASSAGE}.txt` (by `ENERGY_WHERE.py`, the text contexts left out),
  and the exterior crossing reads
  `CROSSING_{CEILING,SPECTRUM,TURN}.py` with their outputs `CROSSING_*.txt` (run from the run
  directory, beside the moments and the covector reads, which stay outside the repository).
- The complex forms: `COMPLEX_RUNS.txt` (the timing rank and the stopped founding's log lines),
  `SITUATED_FORMS_c4.txt` (the four complex forms) and their probe `SITUATED_PROBE_c4.txt`; the
  outside readings `CHARACTER_AT_B.{py,txt}`, `IDEAL_FORM.{py,txt}` with the one form
  `IDEAL_FORM_{quiet,free}.txt`, its share `IDEAL_SHARE.txt` and probe `IDEAL_PROBE.txt`,
  `FORM_DILUTION.{py,txt}`, `CROSSING_AT_U.{py,txt}` and `LOCK_AT_B.{py,txt}` (run from the run
  directory).
- The crossing at its own loudness: `REGION_SHARE.{py,txt}`, `REGION_FOUNDING.py` with the
  lock-region founding `REGION_FOUNDING.txt`, the stopped ranks `REGION_FOUNDING_stopped.txt` and the
  state-first founding `REGION_FOUNDING_state.txt`, `TURN_FORMS.{py,txt}`, `CLASS_MODES.py` with
  `CLASS_MODES.txt` and `CLASS_MODES_labels.txt`, and `MODE_PARTNER.{py,txt}` (run from the run
  directory, each with `REGION_SHARE.py` as its first argument).
- The carried turns: `CARRIED_TURN.{py,txt}` (stopped at its deadline) and `CARRIED_SELECT.{py,txt}`
  (run the same way).
- The ring's sense: `HANDED_RING.{py,txt}` and `RING_SPAN.{py,txt}` (`RING_SPAN.py` takes
  `HANDED_RING.py` as its second argument).
- The knot at `U`: `U_FORMS.{py,txt}`, `U_SHARE.{py,txt}`, and the covector reads' receipt lines
  `U_COVECTORS.txt` (the covectors stay outside the repository).
- The blind reads at `U` and the split at `B`: `U_TURNS.{py,txt}`, `U_TENSOR.{py,txt}`,
  `LAG_AT_B.{py,txt}`.
- The crossing placed where it carries: `MK_PATHS.py`, the mode reads' receipt lines `BU_MODES.txt`
  (the reads stay outside the repository), `CARRY_B_TO_U.{py,txt}`, `FOUND_AT_B_BY_U.{py,txt}`,
  `FOUND_POOL_AT_B.{py,txt}`, `FOUND_PLACE_AT_B.{py,txt}`.
- The demand at the modes: `GH_READS.txt` (the mode covector reads' and every cell's reads'
  receipt lines and commands; the reads stay outside the repository),
  `FOUND_BY_MODES_AT_B.{py,txt}`, `CROSSING_DEMAND.{py,txt}`, `MODE_MEMORY.{py,txt}`,
  `FOUND_RING.{py,txt}`, `RING_REGIONS.{py,txt}`, `RING_TENSION_READ.{py,txt}`,
  `RING_AFTER_RELATION.{py,txt}` and `OP_TURN_AT_B.{py,txt}` (run from the run directory;
  `RING_REGIONS.py` takes `FOUND_RING.py` as its argument, the region reads take both, and
  `OP_TURN_AT_B.py` takes `REGION_SHARE.py`).
- The operation crossing: `STATE_READS.txt` (the state reads' receipt lines; the reads stay outside
  the repository), `RING_OP_REGIONS.{py,txt}`, `OP_GATE.{py,txt}`, `BLIND_GATE.{py,txt}`,
  `BLIND_PUSH.{py,txt}` and `GATED_PUSH_FREE_READ.{py,txt}` (run from the run directory; each takes
  the scripts it loads as its arguments, as its docstring names them).
- The plural ranks: `PLURAL_RANKS.{py,txt}` (run the same way).
- The blind pool and its starts: `BLIND_POOL.{py,txt}`, `PLURAL_POOL.{py,txt}`, `POOL_SEED.{py,txt}`,
  `POOL_SEEDS.{py,txt}`, and `POOL_REACH.py` with `POOL_REACH_long.txt` and `POOL_REACH_U.txt` (run
  the same way, each taking the scripts its docstring names).
- The machine's ring founding: the development reads on one block `RING_BLOCK0_ring{1,2,3,4,5}.txt`,
  the founding on the training text `RING_FOUND.txt` and its forms `RING_FORMS.txt`, and the
  acceptance `RING_ACCEPT.txt` (the reads' receipt lines and the probes; the reads stay outside the
  repository). The landmarks are `tools/landmarks.py sum-units` over each text.
- The ring inside the learner: `RING_JOIN.txt` (the fitted join), `RING_PASS_TEXT_STOPPED.txt` and
  `RING_FOIL_TEXT_STOPPED.txt` (the whole-text passes, stopped on evidence), `RING_PASS_BLOCK.txt`,
  `RING_FOIL_BLOCK.txt` and `RING_PASS_BLOCK_RATIO.txt` (the block passes), and `RING_AT_U.txt` (each
  tower's read at the held-out units: the receipt lines and the counts; the reads stay outside the
  repository).
- The ring's founded readout: `RING_READOUT_LAW.{py,txt}` and `RING_READOUT_CLOSED.py` (the exterior
  reads that chose the readout's law and its founding, with the every-cell reads' receipt lines;
  the reads stay outside the repository), `RING_FOUNDED_READOUT.txt` (the joins, foundings, passes
  and reads, and the swapped readouts by `RING_SWAP_READOUT.py`) and `RING_DEPHASING.txt` (every
  mode's move by `RING_MOVE_DRIFT.py`, and the ring's own read of the units at `U` and `B` by
  `RING_OUTSIDE_AT_U.py` and `RING_AT_B.py`).
- The push's factors and the held passes: `RING_FACTORS_AND_HOLDS.txt` (the join, the founding, the
  passes and the reads of each loop) and `RING_PHASE_PAIRS.{py,txt}` (the ring's turn at `B` and `U`
  by the operands' units, before and after the pass holding what the ring reads).
- The founding to its precision: `RING_FIXED_POINT.txt` (the one-bit founding's every round to its
  stop, the precision founding, the join, the readout's founding, the lap, the foil's lap and every
  read), `RING_CARRIAGE.{py,txt}` (the ring's units read outside by the operands' and the result's
  lengths), `RING_PUSH_ROLES.{py,txt}` (where the push's state factors open, by role),
  `RING_MODE_TURNS.{py,txt}` (the move of the mode the ring rides, by arriving byte),
  `RING_TRAIN_DIRECTIONS.{py,txt}` (the held-out units read by the training text's class
  directions) and `RING_OWN_BY_OPERANDS.{py,txt}` (the tower's own guess at the held-out units by
  the operands' lengths).
- The readout founded to its precision: `RING_READOUT_ROUNDS.txt` (the split on the last loop's
  ring, the Newton rounds, the lap and every read) and `RING_SPLIT.{py,txt}` (the whole guess, the
  ring's part and the rest at the held-out units, by the operands' lengths; run from the run
  directory on the reads' `SPLIT` lines, which stay outside the repository).
- The carriage key by loop closure: `RING_PAIR_MOVES.txt` (the three step foundings of the pair
  move and the ceiling, each joined and read outside at the held-out units, the ceiling's table by
  `RING_CEILING.py`), `RING_CLOSURE.txt` (the refused and stopped eliminations, the closure
  founding's every origin, its key, the ring founded under it and every read),
  `RING_HARMONICS.txt` (the join at five harmonics, the readout's rounds and every read) and
  `RING_PHASE_CENTROIDS.{py,txt}` (the units' turns at `U` and their leave-one-out centroid
  reads); the splits are appended to `RING_SPLIT.txt`.
- The readout founded on the four media: `RING_MIXED.txt` (the control's founding, the development
  read, the three foundings on the four media, the context checks and every read's receipt lines;
  the reads stay outside the repository) and `DEV_BY_MEDIUM.py` (the held-out text's code by medium,
  run from the run directory); the splits are appended to `RING_SPLIT.txt`.
- The tens: `RING_TENS.txt` (the closure at the tens, the ring under the whole key, both joins,
  the regressions, every founding's rounds and every read's receipt lines) and
  `RING_TENS_CENTROIDS.txt` (the 110 ring's turn at the held-out tens and units, by class, and the
  centroid reads over counts of characters, from `RING_PHASE_CENTROIDS.py … harmonics=…`); the
  splits are appended to `RING_SPLIT.txt`.
- The written sums: `LINES_founded30_arithmetic.tsv`, `LINES_founded26m_arithmetic.tsv` and
  `LINES_founded31_arithmetic.tsv` (every held-out arithmetic line's head, true rest, written rest
  and codes) and `WRITTEN_SUMS.txt` (their receipt lines and counts, from `WRITTEN_SUMS.py …
  --train modes/block.txt ring/mixed.txt`, which reads each line apart by whether a training file
  holds it whole, and each operation's wrong lines by where they go wrong).
- The differences: `RING_DIFF.txt` (the closure at the differences' units and its ring, the join,
  the readout's founding, its reads, and the closure at the differences' tens).
- The tens with the hand: `RING_TENS_HAND.txt` (the closures at the differences' tens and at the sums' and
  differences' tens, none keyed; the key located at the units, founded at the units and at the tens).
- The reflection: `RING_REFLECT.txt` (every keyed closure with the hand on the differences' units,
  the sums' units and both, their summaries and kept keys, the joint ring's founding, the join, its
  readout's founding, every read and the writing) and `RING_RANK_CENTROIDS.{py,txt}` (each ring
  rank's turn by class at the held-out differences' tens and units, and its leave-one-out
  centroid read); the written lines are `LINES_founded33_arithmetic.tsv`, counted in
  `WRITTEN_SUMS.txt`.
- `READS.txt`: every read's and writing's receipt lines (moments located, looks spent and settled,
  SHA-256 of `LOOKS.tsv` and `LINES.tsv`, wall time, peak).

The binaries are `arith22` for the first two towers' training and writing (SHA-256 `744ef118…`),
`arith23` for their repaired reads and the pair towers' training (`cb2ea60a…`), and `arith24` for
the located reads, the pair towers' reads and writing, and the rungs (`a3cc250c…`). The tension
reads use `tension1` (`5295f6c6…`, the timing slice and the first held-out reads) and `tension2`
(`c25dda3f…`, with line starts and the region). The floor reads use `floor1` (`4480bbcb…`),
`floor2` (`79266042…`) and `floor3` (`e0edd479…`, the last slice and the full text). The founding
uses `found1` (`d2ebd83e…`) and, with the spectrum, `found2` (`7e93511f…`). The block uses
`block1` (`95057b05…`; its failed slices ran earlier builds of it, the first `3d69f641…`). The
install and its writing use `install1` (`522b9cfa…`). The pair forms in the learner use `face1`
(`44ed341e…`) for the join, the passes, the met and unmet reads and the writing, and `face2`
(`60db5291…`, the same source with the leverage read) for the leverage, in both passes. The
circuit readings use `circuit1` (`604a10c8…`), and the mode readings `modes1` (`25db693e…`). The situated pool uses `situated1` (`a27cf8df…`, the energy foundings), `situated3`
(`6b4b79b5…`, the code-weighted), `situated4` (`6a20bb33…`, the covector reads), `situated5`
(`0cdf49dd…`, the warm start, the sixteen forms and their reads), `situated6` (`fa381fdc…`, the
resume), `situated7` (`25f4309f…`, the complex forms, their reads and the modes at the sums' cells)
and `situated8` (`1abd5ebb…`, the mode covectors, every cell's reads and the state reads). The ring
founding uses `ring1` to `ring5` (its development builds, in order) and `ring5` (`c2801523…`) for the
founding on the training text and the acceptance reads. The ring inside the learner uses `ring6`
(`9b4954f6…`, the fitted face) and `ring7` (`128f340b…`, the face as a ratio). The founded readout
uses `cells8` (`e69cbdb0…`, the every-cell reads), `ring9` (`8813e43b…`, the founding with its
moments at zero, its pass and the moves) and `ring10` (`8cdc8135…`, the founding with its moments,
its pass, the swapped readouts and the reads at `U` and `B`). The push's factors use `ring11`
(`6f1d433f…`, the factors as material, their founding and pass), `ring12` (`0e8600ae…`, the held
passes), `ring13` (`9f7edb09…`, the pass holding what the ring reads), `ring14` (`7d21f6f4…`, the one-bit
founding, stopped) `ring15` (`1854df21…`, the precision founding, its join, readout, laps and
reads, and the modes and training reads) and `ring16` (`d9711a49…`, the split, the readout's Newton
rounds, its lap and reads). The carriage uses `ring17` (`38c856bc…`, the fixed step), `ring18`
(`63813946…`, the octave lines and the ceiling), `ring19` (`6e703b2f…`, refused), `ring20`
(`9122131d…`, stopped), `ring21` (`bd8fba28…`, the closure founding, the ring under its key, the
readout at one cosine and every read) and `ring22` (`6f0bbab7…`, the readout at five harmonics and
its reads). The four media use `ring23` (`4a89dc6d…`, the curvature on its grain: the control and
the development read), `ring24` (`2b3fe76c…`, one scale for every row), `ring25` (`179dbef4…`, each
row on its own scale, and the context checks) and `ring26` (`7c510f7d…`, the Newton step in readout
units, its founding and reads). The tens use `ring27` (`8a69dee5…`, the closure at the tens, the
ring under the whole key, its readout at 55 harmonics and reads), `ring28` (`ea85d668…`, the
regressions, the two rings, their foundings and reads) and `ring29` (`e4417b54…`, the sums carried
64 bits wide, the block check, the founding that meets the acceptance and its reads). The
reflection uses `ring32` (`0f8aeac3…`, the whole search, stopped), `ring33` (`69def066…`, the
search by row count, at its deadlines), `ring34` (`7d17d3cb…`, the restarts beside the keyed
reflectors, stopped) and `ring35` (`4a76318b…`, the reduced echelon: the three closures, the joint
ring's founding, the join, its readout, its reads and the writing).
