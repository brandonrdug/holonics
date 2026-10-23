# The released ratio opens the whole GSM8K partition

Refs #405 #404 #73. Follows [on GSM8K the tree's depth carries the code](2026-10-23_ON_GSM8K_THE_TREE_DEPTH_CARRIES_THE_CODE_AND_THE_PASSAGE_ADDS_ITS_NEWS.md)
and the mathematics thread's contacts record, §7 in
[PR #412](https://github.com/brandonrdug/holonics/pull/412) (the telescope and its width rules). Status: [proved-derived; agent-inferred,
October 23], built and measured on the host.

## The wall

The receiving tree (`compression::landmark::context::Landmarks`) certified its executed face
against the ideal tree weighting over the whole passage. That ideal's mixture ratio `β` is never
released: on the 6,726 GSM8K training problems `|log₂ β|` reaches 5,169,736 bits. The
certificate's drift and the derived widths therefore hold `n* P²` units, and the depth-24 tree
refused every declared population past `2^21` cells: at the whole partition's `2^24` the opening
derived 133-bit operands, past the 128-bit carrier. So the route trained on 1,000 problems only.
The mathematics thread's exterior measurement placed the gain at 14% (0.5529 bits a cell on
1,000 problems, 0.4742 on all 6,726, at depth 24).

## The released ratio

A node's mixture is `q = (β k + x)/(β + 1)` of its KT face `k` and its child's face `x`, with the
step `β' = β k/x`. For any release `β_(t+1)` of `β'_t` the passage telescopes,

`Σ −ln q = Σ −ln x + ln(1 + β_0) − ln(1 + β_n) + Σ [ln(1 + β_(t+1)) − ln(1 + β'_t)]`,

and the same holds in `k` with `1/β`. Each term of the last sum is one cell's own. A rounding of
`ln β` by `δ` costs at most `δ`, a release into `[2^(−K), 2^K]` costs at most `ln(1 + 2^(−K))`,
and a node pays at most `K + 1` bits to turn from one face to the other over any stretch.

`RatioLaw::Released` releases every stepped, split and chained ratio (`Beta::released`, the
interval's nearest point, decided exactly on the odd ratio's bits). Its widths read the population
only through the KT floor: `2^(M_p) ≥ 3 B L_R (2^j n* + 2)(2P + 1)`, `2^W ≥ 24 B L_R (P + 2)`,
`2^K ≥ 12 B L_R P`, so each cell's face stays within half a grain (`Landmarks::face_rule`). The
depth-24 tree over four classes now declares past `2^28` cells. A released read's residual is
its rounding alone. `ReceiverDeclaration` carries the law (`ratio`). Every existing
declaration stays carried; the modes route declares the released ratio.

Tests (`compression::landmark::context::tests`): the released widths open at populations up to
`2^28` and depths up to 73 with the face rule below half a grain, where the carried law refuses
`2^24` at depth 24; `Beta::released` returns the interval's nearest point on exact cases; and over
a 400-cell passage every chart stays in `[2^(−K), 2^K]` and reaches its bottom, while the carried
chart's exponent passes `−300`. The 164 receiving tests pass.

## What more data does

| corpus | ratio | tree alone | tree and passage | bits a character |
|---|---|---|---|---|
| 1,000 problems (2,078,532 cells) | carried | 0.507 | 0.469 | 1.88 |
| 1,000 problems | released | 0.506 | 0.467 | 1.87 |
| 6,726 problems (14,112,672 cells) | released | **0.448** | **0.413** | **1.65** |

Every code is prequential. On 1,000 problems the release costs nothing: it codes slightly lower,
runs 9% faster (130.8 s against 144.3 s) and rests 15% smaller (211 MB against 249 MB). On the
whole partition the tree alone falls 11.5% and the joined route 11.6%. By digit position within a
byte the whole partition codes `[0.166, 0.438, 0.663, 0.383]` (on 1,000 problems
`[0.195, 0.483, 0.748, 0.441]`). Over the last 726 problems alone the route codes about 0.40 bits
a cell and the tree about 0.42 (from the cumulative totals' three decimals, within 0.005).

The held-out prompt "John volunteers at a shelter twice a month for 3 hours at a time.  How many
hours does he volunteer per year?" (the first problem of the dev partition, never trained on)
codes at 0.366 bits a cell from the whole-partition state, against 0.458 from the 1,000-problem
state.

## Generation

From the whole-partition state, the sample opens its passage at the prompt and releases each cell
by an exact draw from the joined face, not counting its own release (the previous record's law).
Its first 512 released bytes, as they are:

```text
Jufflowing once.  How far drinks taller trum. How many hours at a servings per sister theater
than her player sped 3,000=320>>320000+y save by multiplynn and dehyena ran 4 month and has
sclass: 25 seeds at a salon necklaces the month n 3 times as each and in 203+14=21>>21 minutes
does J = A +4 = 4 + 4 = $<<100*3/12 / 2 foot is half as long his at hersellyballons < 3 less the
vowever.  How many firm. His day, How many square pack at a time.  How many hours lunchel have
the old toddle saw with demand in 2 fli
```

It carries the problems' question shape, the answers' calculator annotations and equations, and
the prompt's "hours" and "at a time", with no loop. Its longest run copied from the corpus is
22 bytes (" at a time.  How many "). It is not yet sentences, and its arithmetic is not
arithmetic: what the tree does not carry is the relation between cells (a copied quantity, a
computed result), which is the located-equality contact the mathematics thread names next.

## What was retired

- **The standing passage chain as the tree.** The passage tree's backoff chain alone, standing
  in for the receiving tree to escape the wall, coded 1.760 bits a cell over the first 11,000
  cells against the landmark tree's 0.839, and stopped there on a joined face with mass. The
  release is the fix; the stand-in is gone.
- **A sharpened release.** Drawing from `p^2` or `p^3` instead of `p` collapses the sample into
  "How many hours at a time." repeated (`p^3`: eight times in 512 bytes). The release draws from
  `p`.

## Speed and receipts

The whole-partition run took 1,042.6 s (74 µs a cell including the state's write; the read and
the take cost 33 and 37 µs a cell at the end, against 21 and 28 at the start) and 3.6 GiB peak
resident set. It was projected at 890 s (upper 1,330 s) from the 1,000-problem run's 63 µs a
cell, under a fixed 1,500 s deadline: measured over projected is 1.17. Memory was projected at
8 to 10 GiB by scaling the 1,000-problem state; the state grows less than the corpus (659 MB
against 211 MB for 6.8 times the cells), because the passage tree's decayed counts dissolve and
the receiving tree's paths share. The sample took 9.9 s and 2.6 GiB.

[`RUNS.tsv`](2026-10-23_THE_RELEASED_RATIO_OPENS_THE_WHOLE_GSM8K_PARTITION_receipts/RUNS.tsv)
and [`SAMPLES.tsv`](2026-10-23_THE_RELEASED_RATIO_OPENS_THE_WHOLE_GSM8K_PARTITION_receipts/SAMPLES.tsv)
hold every run above with its code, projection, deadline, wall time, peak resident set and
hashes.

## Owed

- The Lean statement of the telescope and its release cost (#410).
- The card's tree (`holonics-cuda`, `kernels/tree.cu`) carries the ratio unreleased; its release
  is owed beside the card's other debts (#76).
- The located-equality contact: the relation between cells that the tree's contexts cannot
  carry, the next consumer of this route.
