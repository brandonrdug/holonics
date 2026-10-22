# The native face reads its own receiving tree

Refs #73 #62. Follows [the native contact step](2026-10-22_THE_NATIVE_CONTACT_STEP_IS_CERTIFIED_BY_REREADING_THE_SAME_COMPARISON.md),
whose training command delivered real text through the native route and coded it at about the
flat rate. Status: [definition; agent-inferred, October 22], built and measured on the host.

## The cause

The native route coded 40 bytes of THE_MACHINE at 1.952 bits per base-four digit (flat is 2), a
constant byte at 0.96 and a period-4 byte at 1.55, and none of them fell with more passage. Four
exterior readings located the cause (scripts and logs are not kept; their conclusions are what
the decision uses):

- **The readout's prior is not the limit.** Sweeping the prior's scale over the measured features
  moved the code by hundredths of a bit.
- **The readout's inputs carry no usable context.** The native feature is `[fresh, actual − fresh]`
  at the receiver ring, 12 coordinates. An ideal linear readout fitted to the 40-byte run's own
  features, in their operand charts, still codes them at 2.06 bits per digit: they do not separate
  the next digit.
- **The receiving tree does.** The constitution already carries the shift navigator's landmarks at
  the receiver ring (`compression::landmark::context::Landmarks`, the receiving parametron's
  storage, atlas `landmark.context-tree-standing`). Read prequentially at depth 6 over the same
  addresses, it codes the first 1,024 bytes at 1.22 bits per digit, the constant byte at 0.05–0.12
  and the period-4 byte at 0.09.
- **The native route never read it.** `observe_native_current_section` cloned the tree into its
  stage as an unused legacy operand, and the native face had no tree term
  (atlas `hnn.native-current-prediction`, "without a tree or population operand").

## The decision

The native face is the receiving tree's face joined with the readout's wave
(`NativeCurrentFace::joined`, atlas `hnn.native-tree-join`):

```text
weight_c = q_c(a) · 2^(w_(2c) − top),   F = weight / Σ weight,   covector F − e_t
```

1. `q(a)` is the tree's face at the cell's address `a`: the framing path when the tree has an
   observation width, then the causal letters truncated to the receiver's depth
   (`NativeTreeAddress`). It is read before the cell.
2. The joined face is the native face. Its score, its draw and the receiving covector all use it,
   so the readout learns only the correction to what the tree already predicts. The contact's
   reread (`native_objective`) joins the same tree faces, so the contact is judged on the face
   that is actually emitted.
3. Every actual cell deposits its class at the address it was read at: during a section, into the
   working tree that the stage publishes with R at the section end; at a contact cell, into the
   constitution's tree through `observed_epoch_prefix`. Forecast and released cells read the frozen
   tree at their moving address and deposit nothing.
4. The covector is the logit gradient of `−log₂ F_t` with the tree mass held fixed (a constant
   factor of each class's weight), so the R law is unchanged. The Lean statement is owed in #62.

**The readout's metric takes the producing face's Fisher bound** (`native_fisher_weight`, atlas
`hnn.native-fisher-weight`). Each native sample enters the Gram at
`μ = min(p_max, 2(1 − p_max))`, held at its dyadic ceiling. Both halves bound the face variance
(`faceVariance_le_centred`, and the second moment about any class). With the unit weight, a
sharply read face still added full curvature, and every later step shrank against a metric that
kept growing. The step is still certified by `receiving_fisher_face`. The complement half's Lean
statement is owed in #62.

What it repeats from the lessons, and why it is refused there:

- **No authored routine stands in for learning.** The tree is the machine's own landmark owner,
  and its counts are located from the passage.
- **Seen material is not graded as unseen.** Every code below is prequential: each cell is read
  before it is deposited. The held-out control is reported separately.
- **Recitation is not counted as generation.** The sample is read beside its longest run copied
  from the corpus.
- **Bits are not read as progress.** The output is shown as it is.

## The measurement

`complete-language train-native` (host, optimized build without LTO, 4 cores; the 1k run shared
them with the gate). Prequential bits per base-four digit; flat is 2. "Before" is the same
command at `22cb440fc`, which had no tree join.

| Corpus | Cells | Before | Joined | Tree alone | Last section, joined |
|---|---|---|---|---|---|
| `U` × 40 (constant digit) | 160 | 0.96 | 0.082 | 0.089 | 0.006 |
| ESC × 64 (period-4 digits) | 256 | 1.55 | 0.066 | 0.067 | 0.005 |
| THE_MACHINE, first 40 bytes | 160 | 1.952 | 1.621 | 1.606 | 1.440 |
| THE_MACHINE, first 256 bytes | 1,024 | 1.926 | 1.368 | 1.347 | 1.242 (last 200 cells) |

- The 256-byte run took 743 s for 1,024 cells, with 75 contacts published and 28 refused at the
  represented physical ray. The 40-byte run took 52 s, against 82 s before.
- **On text, the readout's wave does not yet add to the tree.** The joined code is 0.02 bits per
  digit above the tree alone on 256 bytes. It is lower on the constant byte and equal on the
  period-4 byte. The readout's features carry no context (above), so its correction is noise on
  text. This is the next loop's subject.
- **The digits are not equal.** On 256 bytes the joined code by byte digit is 0.70, 1.39, 1.83 and
  1.55 bits. The top digit (which of four byte quarters) is mostly predicted, and the low digits
  are near flat.
- **Incomplete:** the first 1,024 bytes (4,096 cells) were stopped at cell 930. The projection was
  0.45 s per cell against a 2,400 s deadline. Under contention with the gate and a sample, the
  measured rate was about 1 s per cell, so the run could not meet its deadline.

Exact totals are in [exact_totals.json](2026-10-22_native_tree_join_receipts/exact_totals.json).
Logs:
[ff40](2026-10-22_native_tree_join_receipts/train_native_tree_ff40.txt),
[esc64](2026-10-22_native_tree_join_receipts/train_native_tree_esc64.txt),
[m40](2026-10-22_native_tree_join_receipts/train_native_tree_m40.txt),
[m256](2026-10-22_native_tree_join_receipts/train_native_tree_m256.txt),
[1k, stopped](2026-10-22_native_tree_join_receipts/train_native_tree_1k_stopped.txt).

**The sample.** The 256-byte state was restored cold, conditioned on the prompt `# The machine: `
(60 cells coded at 60.04 bits, frozen, no learning), and released 512 keyed cells. The output, as
it is:

```text
thpmniedxJI([Cgn/CdTxlasiniaEDUS al.iner.imsc.N n-(pomd)-s inene(#bteas. ee(/A](.un
[l.tiedior, iieden enteods).\te, sr-vhiny, o
```

Its longest run copied from the 256 training bytes is 3 bytes; greedy longest matches cut it into
86 pieces of 1.49 bytes on average. Every byte is printable and from the corpus's alphabet, with
the corpus's brackets, parentheses and periods. Before the join, the same 1,020 training cells
sampled control bytes and invalid UTF-8
([before](2026-10-22_native_contact_reread_receipts/sample_native_1020_cells.txt)). Receipts:
[log](2026-10-22_native_tree_join_receipts/sample_native_tree_512_cells.txt),
[output](2026-10-22_native_tree_join_receipts/sample_native_tree_512_cells.json).

**The controls hold.** Optimized build at this source:

- `represented_native_contact_learning_held_out`: 9.3 s. The contact arm codes the ten held-out
  cells at `8724052434521312555/2^64` bits against the R-only arm's `8819256026257726841/2^64`,
  about 0.473 against 0.478 bits for all ten cells, against 18.56 and 18.74 bits before the join.
  The contact arm is strictly lower.
- `represented_native_zero_motion_continuity`: 9.0 s. Continuity, positive material influence,
  cold restores and the four frozen decisions all pass.

Receipts: [held out](2026-10-22_native_tree_join_receipts/held_out_tree_join.txt),
[continuity](2026-10-22_native_tree_join_receipts/control_tree_join.txt).
