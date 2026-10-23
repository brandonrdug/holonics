# On GSM8K the tree's depth carries the code, and the passage adds its news

Refs #405 #404 #73. Follows [the native face reads its own receiving tree](2026-10-22_THE_NATIVE_FACE_READS_ITS_OWN_RECEIVING_TREE.md)
and the mathematics thread's
[order is torsion record](2026-10-22_ORDER_IS_TORSION_AND_SUBGRAIN_INFORMATION_DISSOLVES_INTO_THE_CARRIED_RESIDUE.md)
(PR #412, its §5 and the passage-tree measurement). Status: [definition; agent-inferred, October 23],
built and measured on the host.

## The route

`complete-language train-modes` and `sample-modes`
(`crates/holonics/examples/solenoidal_alpha/complete_language/modes_train.rs`) join three owners
at the receiver's face, `p̂(c) ∝ q(c) 2^(w_c)`:

1. the receiving tree (`Landmarks`), declared as the native route declares it, at a declared depth;
2. the keyed modes (`hnn::keyed_modes`, atlas `hnn.keyed-modes-*`): each arriving class selects
   every mode's swing and push, read linearly and through each class's square law;
3. the passage tree (`hnn::passage`, atlas `hnn.passage-tree`): the same contexts' counts at
   `γ = 1 − 2^(−13)`, backed off to the tree's own face, read as its news over that face,
   `w_c += α_e f_c` with `f_c = log₂ p_loc(c) − log₂ q(c)` and one weight per evidence depth.

Text enters as base-four cells (`Base4Bytes`); a code length is in bits a cell, and four cells
make a byte, so bits a character are four times bits a cell. The corpus is the first 100 or 1,000
problems of the GSM8K training partition (`train_indices` of the local `partition-indices.json`),
question and answer as plain text (216,540 and 2,078,532 cells). Every code below is prequential: each cell's face is read before its class arrives.

## What carries the code

**Depth.** The receiving tree alone, 100 problems:

| depth (cells) | 6 | 8 | 9 | 10 | 11 | 12 | 16 | 20 | 24 |
|---|---|---|---|---|---|---|---|---|---|
| bits a cell | 0.864 | 0.769 | 0.726 | 0.699 | 0.675 | 0.650 | 0.613 | 0.607 | 0.605 |

On 1,000 problems depth 16 codes 0.533 and depth 24 0.507 (2.03 bits a character; the native
route's depth 6 codes 0.864 on 100 problems, 3.46 bits a character). A depth of 12 cells or more needs a declared population near the
corpus's own (`2^18` for 100 problems, `2^21` for 1,000): at the default population the tree's
derived widths outgrow the 128-bit carrier and the declaration refuses.

**The keyed modes add nothing past a deep tree.** 32 keyed modes at depth 24 on 1,000 problems
code 0.510 against the tree's 0.507; read also through the square law, 0.509 to 0.513 over three
step rungs. This is the bound of the mathematics thread's §5: once the tree conditions on its
context exactly, anything else adds at most `I(u_t ; far past | C_t)`, and a mode driven by the
symbol alone splits into a function of the context plus `λ^D` of its far state. A mode whose
memory sits inside the tree's horizon is the tree again. The modes stay in the route at `K = 0`:
their next consumer is the tower drive (modes fed by the tree's news), not the symbol.

**The passage adds its news.** On 100 problems at depth 24, modes off:

| passage form | best bits a cell |
|---|---|
| none (tree alone) | 0.605 |
| backed off to a flat face, feature `log₂ p_loc` | 0.589 |
| deepest evidence node only, backed off to the tree's face | 0.592 |
| full chain backed off to the tree's face, feature `log₂(p_loc/q)` | 0.576 |

The full chain over the tree's face is the declared form: the passage reads only what the tree
does not already predict. On 1,000 problems, at a hand-set step rung, it codes 0.483 (rung 14) or
0.510 (rung 12): a fixed step that suits 100 problems overshoots on 1,000.

## The step is set by the comparison's curvature

The cell's code is a log-partition in each passage weight, so it is convex with
`∂²ℓ/∂α_e² = ln 2 · Var_p̂(f)`. Each section's covector `G_e = Σ δ_c f_c` now takes the Newton
step of the cumulative second-order model, `α_e ← α_e − G_e / (ln 2 · Σ Var_p̂(f))`, the variance
summed over every cell its evidence depth has met (`KeyedModes::passage_stepped`, atlas
`hnn.passage-weight-newton`). `ln 2` is its series face `Σ 1/(k 2^k)` at `2^(−30)`. No rung is
chosen.

| corpus | tree alone | hand-set step | curvature step |
|---|---|---|---|
| 100 problems | 0.605 | 0.576 (rung 12), 0.586 (rung 14) | 0.578 |
| 1,000 problems | 0.507 | 0.483 (rung 14), 0.510 (rung 12) | **0.469** |

0.469 bits a cell is 1.88 bits a character. By digit position within a byte it codes
`[0.196, 0.485, 0.752, 0.444]`. The located weights settle between 0.10 and 0.17 at every
evidence depth from 1 to 25. The run's running total trailed the hand-set run's for the first
80,000 cells and led it from about 120,000 cells on.

## Generation

A sample is a fork of the rested state: the receiving tree is frozen, the passage opens at the
prompt and receives it, and each cell is released by an exact draw from the joined face.

- **A released cell is not received.** Counting it as passage evidence is reafference: measured
  on the 1,000-problem state at the hand-set step, the passage then repeats its own release
  ("added 3 sibli…" seven times in 512 bytes).
- **The passage opens at the prompt.** The rested passage holds the last training problems, and a
  sample that continued it copied them: 114 of 512 bytes inside runs of 20 bytes or more copied
  from the corpus (longest 47) when released cells were also counted, 72 of 512 (longest 28)
  when they were not. Opened at the prompt and not counting its release, the same state's sample
  had none (longest 18).

The held-out prompt "John volunteers at a shelter twice a month for 3 hours at a time.  How many
hours does he volunteer per year?" (the first problem of the dev partition, held out of the corpus) codes at 0.458
bits a cell. From the 1,000-problem state, its first 512 released bytes:

```text
Jugglorious day.  How feet she pays at a time.  If there vacation. Ary time.  How many hours at a
third now.  How many hours at a third as many hours at a shells at a points. Cheryl has there the
times?
During how many more than Jerry, briefcase and twice as many hours at leaves
Her the 1. How many does Jonah a meal area mangoes at a third meat the ten yoghurt arpenters he
makes her the doubtractin 10 x 1 = <<90*5=3>>3 down 1 individuan will animal she team westward a
time.  How many as would plans on the p
```

It carries the prompt's words ("hours", "at a time", "twice"), the problems' question shape and
an answer's calculator annotation, with no loop; its longest run copied from the corpus is 20
bytes. It is not yet sentences.

## Speed

With the modes off, a cell costs 40 to 55 µs (reading the faces and taking the class, both trees),
against about 50 ms a cell on the native route before this work. The 1,000-problem run takes
144 s and 1.25 GiB peak resident set (the passage tree holds about 550,000 nodes; the rested state
is 249 MB of text, mostly the receiving tree's standing).

## Receipts

[`receipts`](2026-10-23_ON_GSM8K_THE_TREE_DEPTH_CARRIES_THE_CODE_AND_THE_PASSAGE_ADDS_ITS_NEWS_receipts/RUNS.tsv)
lists every run above with its code, wall time, peak resident set and state hash. The two
curvature-step runs were projected from the hand-set run's measured 151 s and 13 s, under a 240 s
deadline; they measured 144.3 s and 12.7 s (ratios 0.96 and 0.98).

## Owed

- The passage tree's decayed count is the transported release with its residue carried
  (`CarriedRelease`, PR #412). Its lazy decay agrees with the stepped decay within one
  count numerator (Rust test `lazy_decay_is_the_stepped_decay`); the Lean statement is owed in #410.
- The curvature step's descent: the cell code is convex in `α_e` with the stated second
  derivative (a log-partition). Owed in #410.
- What the tree cannot reach past depth 24 is what a mode must carry: the tower drive, modes fed
  by the tree's news rather than the symbol, is the modes' next consumer.
