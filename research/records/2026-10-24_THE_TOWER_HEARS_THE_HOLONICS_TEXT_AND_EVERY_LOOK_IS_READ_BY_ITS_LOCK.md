# The tower hears the Holonics text, and every look is read by its lock

Refs #405 #404. Follows [the digit terrain](2026-10-23_ON_A_TERRAIN_OF_INTERACTING_DIGITS_THE_TOWER_COMPUTES_WHAT_IT_NEVER_MET_WHERE_IT_KNOWS_THE_LEVEL.md#every-look-read-by-its-lock-and-the-turn-to-the-holonics-text)
and the mathematics thread's [one face law](2026-10-24_ONE_FACE_LAW_A_FACE_IS_A_CONGRUENCE_SO_LANGUAGE_ARITHMETIC_AND_ANY_OPERATION_ARE_READ_BY_ONE_CONTACT.md)
and its record on cycles (PR #426). Status: [measurement; agent-inferred, October 24], on the host.

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

## The recorded failures this step could repeat

- **Text run on its codec's grain as the exception.** This is the failure this step exposed: a
  moment byte chosen where digits ask. The lock now reads every medium alike, and the next loop
  places the moment where a located key fires, in any medium.
- **Bits read as progress.** The held-out code stands beside the writing, and the success reading
  is the lock.
- **Seen material graded as unseen.** Held-out files are never training files. The lock splits met
  and unmet lines, and no held-out text line is met verbatim.
- **Catered machinery.** Nothing in the tower names a medium. The media are an exterior partition of
  the held-out text, and the moment byte was a declared exterior choice, which this step retires as
  the moment.
- **A refusal answered with a larger limit.** The plain run stopped at its bound. It was continued
  under the largest measured pass, its own measurement, and reported here as stopped. The pair
  tower's foil stopped at its bound too. It is read at the state it reached and not continued.
- **An authored routine standing in for learning.** The located moment is the passage tree's lock, a
  receiver of the machine's own kind, and no list of relation tokens. It chooses only where the
  exterior reading looks. Nothing in the tower reads it.

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
- `READS.txt`: every read's and writing's receipt lines (moments located, looks spent and settled,
  SHA-256 of `LOOKS.tsv` and `LINES.tsv`, wall time, peak).

The binaries are `arith22` for the first two towers' training and writing (SHA-256 `744ef118…`),
`arith23` for their repaired reads and the pair towers' training (`cb2ea60a…`), and `arith24` for
the located reads, the pair towers' reads and writing, and the rungs (`a3cc250c…`).
