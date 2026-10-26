# The gated tower's training pass runs on the card and returns the host's bits

Refs #404 #76. Status: [measurement; agent-inferred, October 25], on B-PC (Ryzen 9 7900X, 24
threads; RTX 4080 SUPER, 80 multiprocessors), the GPU under `.local/gpu.lock`. Owners:
`holonics::hnn::tower::realization` (the section's pass and its host realization) and
`holonics_cuda::hnn::tower` with `kernels/tower.cu` (the card's); atlas `hnn.tower-pass-realization`
and `hnn.card-tower-pass`. Receipts: [`receipts/2026-10-25-tower-card/`](receipts/2026-10-25-tower-card/) (each run's output as `.txt`).

## Why

Athena's milestone is connected sentences about Holonics after a cold restart, and the listener
must hear far more text than the host's cores allow: the gated tower on both turn ladders hears
about 37,000 classes a second on the 7900X. The tower's pass is exact integers, so a card that
runs it bit for bit changes how much the learner hears and nothing it learns.

## The claim fixed first

Declaration: gated, rectifying contacts, not turned, not pumped, no pair or ring face, no passage
credit, founded on `TurnLadder::Both` at 128 modes, width 64, 256 contacts, 2 levels, alphabet
257, sections of 128 classes, rate `2^(−7)` (182,017 material entries). Any other declaration is
refused on the card before a launch. Acceptance, decided before the build and nothing past it:

- (a) for 32 sections of the declared passage, every face code and the whole covector equal, host
  against card;
- (b) one full pass at 24 streams leaves a saved learner whose SHA-256 is the host's;
- (c) classes a second on the card at the stream count that fills it, with the realization
  reported as it runs.

The declared passage (`compose_docs_passage.py` in the receipts): `docs/*.md` in path order, one
class an octet, the end letter 256 after each file and after the first blank line that closes 4 KiB
or more since the last end letter: 725,141 classes with 151 end letters. Held out: `README.md`
(28,757 classes). Keys: SHA-256 of `athena-card-keys` and a counter.

## What was built

**The hook** (`tower/realization.rs`, a child module, so the rest of `tower.rs` is untouched but
for `section_compared` becoming `section_realized`, `face_code` read off a face's mass and total,
and a `Realization` refusal). A `PassRealization` owns the section's forward (each stream's faces
at their targets, the swell, the continuing states) and its reverse (the streams' covector,
summed); the moments, the step, the certificate and the deposit stay in `section_realized`, one
law for every realization. `HostPass` is the reference: the same parallel forwards and reverses
the learner ran before. `Tower::resident_law` exports what a realization reads of one section:
the families' places, their reaches, the gated moves' founded faces (`u`, `|λ|`, `log₂|λ|`), the
exponential's resident roots at both grains, and `(ln 2)²`. The consumer (`tower_train::fit`)
takes a realization; every host command passes `HostPass`, and `holonics-cuda`'s `tower_pass
train` passes the card.

**The card** (`holonics_cuda::hnn::tower::TowerCard`, `kernels/tower.cu`). Realization as it
runs, at 24 streams of 128 cells:

| Kernel | Block | Thread | Loops over |
|---|---|---|---|
| `tower_forward` | one stream: 24 blocks | 256: one output of each stage (push and gate logits, a mode's move, a read, a contact, a return part, a class's face) | the stream's 128 cells in order; within a stage its outputs, each over its row |
| `tower_reverse_top`, `_contacts`, `_dx` | one cell: 3,072 blocks | 256: one output of each stage | its column |
| `tower_reverse_modes` | one stream of one level: 24 blocks | 128: one mode | the cells in reverse order (the scan) with each cell's gated move adjoint |
| `tower_outer_x32`, `_x64`, `_reduce` | a tile of 16 × 64 covector entries × a group of streams (`4·SM` blocks a family) | four entries of one column | the group's streams, 32 cells at a time in shared memory |
| `tower_encoding`, `tower_moves` | one class; one level | one face coordinate; one mode | every cell; every stream |

[agent-inferred] The decisions, each from the law:
- **Time is sequential within a stream, so the forward is one block a stream.** Every step
  releases to the grain, so the recurrence is not a scan. The reverse's per-cell parts are
  independent once the scan has run, so they are one block a cell.
- **The card sums the streams' covector.** Integer addition is associative, so a sum over streams
  and cells in the card's order is the host's stream-by-stream sum. Only the moves' Cartesian
  covector is nonlinear per stream (its releases), and it is formed per stream before the sum.
- **Each sum runs in 64 bits where the host's own bound admits it and in 128 otherwise**, with the
  host's refusals: an affine sum whose bound reaches `2^126`, a released value past its carrier, a
  gated move on the unit circle. An outer sum runs a stream in 64 bits when
  `Σ_t max|y_t| max(max|x_t|, 1) < 2^63` (the biases are the ones column), else in 128.
- **The matrix families are copied transposed** each upload, so a forward thread walks its row at
  consecutive addresses across the warp; the reverse reads the material as it is.
- **The outer sums split their streams over groups** and an exact reduction sums the groups. The
  first build gave each family 8 to 34 blocks over all 40,960 cells of 320 streams; the outer sums
  took 128 of a reverse's 155 ms (measured with each launch timed alone). Split over `4·SM`
  blocks a family, the reverse took 43 ms.
- **No float.** `2^x` is the host's dyadic navigator read through its roots; square roots are
  exact digit by digit.

## Measured

**(a) passes.** 32 sections at 24 streams (`parity_a.txt`): 98,304 faces, every mass and total and
so every code equal; 5,824,544 covector entries, every one equal; after every section the two
learners' receipts, texts and continuing states equal. Also at 320 streams for 4 sections (163,840
faces, 728,068 entries, all equal), and in `tests/tower_pass.rs` on a small declaration with every
other place held out of the comparison and on the refusals.

**(b) passes.** One pass at 24 streams through `train-two-ladder-tower-classes`: the card's
`STATE.0` SHA-256 is `6470451f07d29034cf2bb9d7aa3561a70695f63a9017a470e9ee1ac7c8f1ed69`, the host's.
At 96 streams too: `8ee11071090df3ab68808d47a1657f8b09d476b7b59e938c441b5612b6ed9a38` on both.

**(c)** One pass of the passage (`scale_v2_*.txt`; the card's time is its forwards and reverses,
transfers included; the rest is the host's moments, step and certificate):

| Streams | Classes | Pass (s) | Classes a second | Card (s) | Host part (s) |
|---|---|---|---|---|---|
| 24 (host, 24 threads) | 724,992 | 19.69 | 36,800 | — | — |
| 96 (host, 24 threads) | 724,992 | 21.59 | 33,600 | — | — |
| 24 | 724,992 | 8.69 | 83,400 | 6.24 | 2.45 |
| 48 | 724,992 | 5.90 | 122,900 | 3.42 | 2.48 |
| 96 | 724,992 | 5.50 | **131,800** | 2.21 | 3.29 |
| 160 | 716,800 | 7.12 | 100,700 | 1.76 | 5.36 |
| 320 | 696,320 | 10.81 | 64,400 | 1.64 | 9.17 |

- The card fills at 160 to 320 streams: its forward is 10.5 ms for 24 streams and 19 ms for 320
  (4 blocks a multiprocessor), and its pass takes 1.6 to 1.8 s whatever the count; card alone,
  that is about 420,000 classes a second.
- The pass is fastest at 96 streams, 3.9 times the host at the same count and the same bits. Past
  it the host's certificate dominates: `fewer_bits` multiplies every face of the section into four
  big integers, so its cost grows faster than the faces (0.5 s a section at 320 streams). The
  next loop's subject is that comparison, not the card.
- Bits a class rise with the stream count (2.71 at 24, 5.29 at 320) because one pass then makes
  fewer deposits (236 against 17). It is not read as a property of the card.

Receipts (projection, fixed deadline, measured wall, peak resident set):

| Run | Projection | Deadline | Measured | Ratio | Peak RSS |
|---|---|---|---|---|---|
| host, 8 streams | ≤ 145 s (cloud 5,000 classes/s) | 300 s | 31.2 s | 0.22 | 282 MB |
| host, 24 streams | ≤ 145 s | 300 s | 20.0 s | 0.14 | 426 MB |
| parity (a), 24 streams | 15 s (32 × 0.47 s) | 180 s | 9.0 s | 0.60 | 790 MB |
| card, 24 streams | 11 s | 120 s | 9.9 s | 0.90 | 147 MB |
| card sweep, each count | ≤ 20 s | 90 s | 6.0 to 16.2 s | ≤ 0.81 | ≤ 166 MB |
| host, 96 streams | ≤ 25 s | 120 s | 22.0 s | 0.88 | 1,714 MB |

The card was shared with a desktop client's 535 MiB throughout; it was not idle.

## The recorded failures this step could repeat

- *A located cause carried unrepaired into a new consumer*: the card realizes the host's law and
  nothing else; every difference would have shown in (a), section by section.
- *An uncertified deposition step*: the certificate is the learner's, unchanged, and runs on every
  section's rereads through the card's forward.
- *Bits read as progress*: the table's bits a class are receipts of how many deposits a pass made,
  not of the realization.
- *A refusal answered with a larger limit*: no deadline or budget was raised; the card refuses
  what the host refuses, and a declaration it does not carry.
- *A design thought in the programming language*: the kernels carry the tower's own objects (the
  modes' turns and their carry through the contacts) at the host's grains; the layouts are the
  hardware law's report, not the law.
