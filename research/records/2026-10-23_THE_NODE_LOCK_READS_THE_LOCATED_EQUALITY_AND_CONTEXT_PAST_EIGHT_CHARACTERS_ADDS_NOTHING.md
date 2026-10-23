# The node lock reads the located equality, and context past eight characters adds nothing

Refs #405 #404. Follows [the released ratio opens the whole GSM8K partition](2026-10-23_THE_RELEASED_RATIO_OPENS_THE_WHOLE_GSM8K_PARTITION.md)
and the mathematics thread's located equality, §8 of its contacts record in
[PR #412](https://github.com/brandonrdug/holonics/pull/412). Status: [definition; agent-inferred,
October 23], built and measured on the host.

The previous record ended on the relation between cells that the tree's contexts cannot carry: a
copied quantity, a computed result. Two levers were measured on the GSM8K route: a longer
context, and the located equality joined at the face.

## Longer context

The passage tree packed a node's key (context, phase, depth) into 64 bits, so four classes refused
depths past 27 cells. The key is now 128 bits (`hnn::passage`), which reaches depth 59, and a node
at depth 48 keeps a context that differs 41 cells back apart from its common suffix
(`a_deep_context_keeps_its_far_cells`). On the first 1,000 problems, bits a cell:

| depth (characters) | route | tree alone | wall |
|---|---|---|---|
| 24 (6) | 0.467 | 0.506 | 130.8 s |
| 32 (8) | 0.462 | 0.504 | 272.1 s |
| 48 (12) | 0.462 at 2,053,000 of 2,078,532 cells, stopped at its 450 s deadline | 0.504 | - |

Eight characters codes 1% below six. Twelve codes the same as eight wherever both were read. The
two deeper runs ran side by side, so their wall times overstate the cost; the deeper state is 80%
larger (380 MB against 211 MB). The route keeps depth 24 (agent-inferred: 1% for twice the cost).

## The node lock

The mathematics thread's law: a located equality is the pair contact `(t, t − δ)` with slip
`[u_t ≠ u_(t−δ)]`. A run of `ℓ` held contacts closes `ℓ` squares, so the offset `δ` is located by
loop closure. The deepest node on the cell's path with an earlier visit locates it, and the class
that followed that visit is the lock's prediction `ĉ`. That class is the node's indicator at
`λ = 0`, beside its tree count (`λ = 1`) and its passage count (`γ = 1 − 2^(−13)`): each passage
node now keeps it (`next`, two bits of information), set at every deposit. Nothing of the passage
is kept. A held offset that reads the cell `δ` back past the tree's depth would need a strand of the
passage, which retention refuses, so it is not built.

The lock joins the face as one more exponent, `w_c += α_b [c = ĉ]`
(`hnn::keyed_modes::Lock`). Its weight sits in a bin `b`: the octave of the run of correct locks
(sixteen octaves, runs past `2^15` sharing the last) and the locating depth's quarter. The weights
take the passage weights' Newton step on their cumulative curvature from a prior of one
(`KeyedModes::lock_stepped`):

```text
G_b = Σ_t (p̂(ĉ) − [t = ĉ]),   C_b = Σ_t p̂(ĉ)(1 − p̂(ĉ)),   α_b ← α_b − G_b / (ln 2 · (1 + Σ_sections C_b))
```

The cell's code is convex in `α_b` with curvature at most `(ln 2)/4`, so the step descends (the
mathematics thread's certificate). The weight's gradient matches the exponent's change exactly
(`lock_weight_gradient_is_exact`), and a lock that is always right raises its bin's weight
(`a_held_lock_weight_grows`).

| corpus | route | with the node lock | tree alone |
|---|---|---|---|
| 1,000 problems | 0.467 | **0.463** | 0.506 |
| 6,726 problems | 0.413 | **0.410** (1.64 bits a character) | 0.448 |

The lock is right at 84% of cells. It lowers the code by 0.9% on 1,000 problems and 0.7% on the
whole partition. The held-out prompt codes 0.371 bits a cell against 0.366. The mathematics
thread's exterior read gained 4% on 1,000 problems, but over a base that weights the passage once
(0.4886); the route already weights the passage at each evidence depth (0.467, below that read's
node lock at 0.4692), and the evidence depth carries most of what the locating depth does. At the
corpus end the weights are small where the last lock failed and reach 2.7 bits for runs of 256 to
511 locked cells at the deepest quarter.

From the whole-partition state, under the previous record's prompt and keys, the first 512
released bytes, as they are:

```text
Jufflowing once.  How far drinks taller trum. How many hours at a servings per sister theater
than throught 2/3 ft = <<3812 votes - 3f * 3 hens at a spools after than play one is home she
applying thers at a salinder the owluebers at l 300 rabbit amounted for two times the cars does he
walked?
Her shop for a then 3 hours does he antasx(2)/3 = <<1/4*80=4>>4 lines <<2*400=<<6.  How many hour
trashers are at the number of perfect John peroni intervals at equal to 2 * 140 minutes to make a
city. He answer than
```

It shares its first 99 bytes with the previous sample and is no more readable. Its longest run
copied from the corpus is 23 bytes (" the number of perfect "). One calculator annotation is
well formed (`<<1/4*80=4>>4`), with a wrong result.

## What remains of the relation between cells

The mathematics thread's roles name where the lock cannot reach. The repeat after `>>` points the
lock at an older calculation, because its true offset is the result's own length plus two, a
relation of the annotation that no recurring context locates. New numbers in the question cost
more under a lock, a confident wrong copy. The held lock's further 0.0077 bits a cell (exterior)
is what a lawful held offset would have to earn. The code is mostly prose: on 1,000 problems
question and answer prose are 85% of the bytes and about 80% of the bits.

## Speed and receipts

The host ran about 1.45 times slower than at the previous record's runs: its binary, run again,
reached 274,000 cells in 18.4 s against 12.7 s. At that speed the lock costs nothing measurable
(17.9 s to the same cell). The 1,000-problem lock run took 200.3 s (projected 140 s before the host
check, deadline 240 s); the whole partition 1,452.5 s and 3.6 GiB (projected 1,512 s from the host
check, deadline 1,930 s: measured over projected 0.96). The sample took 12.1 s.

[`RUNS.tsv`](2026-10-23_THE_NODE_LOCK_READS_THE_LOCATED_EQUALITY_AND_CONTEXT_PAST_EIGHT_CHARACTERS_ADDS_NOTHING_receipts/RUNS.tsv)
and [`SAMPLES.tsv`](2026-10-23_THE_NODE_LOCK_READS_THE_LOCATED_EQUALITY_AND_CONTEXT_PAST_EIGHT_CHARACTERS_ADDS_NOTHING_receipts/SAMPLES.tsv)
hold every run with its code, projection, deadline, wall time, peak resident set and hashes.

## Owed

- The lock's certified step in Lean (#410, the mathematics thread's §9).
- The relation the lock cannot locate: the annotation's own repeat and the arithmetic of a result.
