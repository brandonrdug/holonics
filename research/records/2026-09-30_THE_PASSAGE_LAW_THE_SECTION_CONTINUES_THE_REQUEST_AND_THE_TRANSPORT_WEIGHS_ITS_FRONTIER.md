# The passage law: the section continues the request, and the transport weighs its frontier (pinned before its runs)

**Date.** September 30. **Issues.** #73, #148, #63 (THE_REBUILD U6). **Grade.** [definition;
agent-inferred] for the law's choice and the pins; [proved-derived; formal-checked] for Lean
`HNN/IndexedOpen`'s passage section; [proved-derived; implemented-exact] for the owners' laws held by
their tests; [measured] for the development reads (§4), which used development seed 41 only.

**Occasion.** The [executed comparison's record](2026-09-30_THE_EXECUTED_COMPARISON_JOINED_A_CERTIFIED_MOVE_DESCENDS_IT_AND_ORDER_TWO_LEARNS_ONLY_THE_TERMINATION.md)
§6 fixed the next loop: the placement's weights, in their owner. Two measurements drive it. The
fitted `E`, read natively from the open section, released 97 sections of 128 that follow the rule
among their own stations from the wrong seed (17 whole). The order-2 continuation depends on the
request's last two cells, which entered at `ν̂(40)` against the placed section cells' `ν̂(v)`, up to
`ν̂(1) = 1`, because each placement was normalized over its own population.

The computational object is the helical pair interaction; the rings are complex parametrons. Of the
[winding guide](../../docs/WINDING_CARRY_AND_PLACEMENT.md)'s six objects it touches four: **the
tube** (the request and its section as one clocked span), **the helix** (the placed phases, now
carried by a rotation–dilation), **the cell holonomy** (the monodromy the bank reads over the turn),
**faces and placement** (each datum's placement and its transported weight). The pair (each
crossing's contact with the ring) and the tower thread stay attached.

## 0. The recorded failures this work could repeat, and how each is avoided

From the [lessons record](2026-09-29_LESSONS_THE_FAILURES_THAT_REPEATED_AFTER_THEY_WERE_RECORDED.md):
- **1 and 2, an authored routine; a window or a copier.** Recency must not become a context window.
  The weight of a crossing is its transport's modulus over the span's transported mass: every
  crossing of the passage enters, none is dropped or truncated by length, and nothing reads a
  suffix, a position table, a pair offset or the terrain's lag. The modulus is one scalar a source
  ring, one at the founding, moved only by the executed comparison's certified move; no value of it
  is authored. The float fits of §4 scanned it only as a diagnostic, never as a choice.
- **3, text as the exception.** One law for every stream: a cell, pixel, sample or screw word is a
  crossing of the ring's clock carried by the same transport. Nothing reads a byte.
- **4, a located cause carried unrepaired.** The located cause (the two populations) is repaired in
  its owners, `hnn::moment` and `hnn::prediction::BankPlacement`, and every consumer of the old law
  moves with it (the readout path's `stage`, `generate` and `comparison_code`, the bank's face path,
  the executed comparison's returns, `reference::compose_return`). A second cause located by the
  development reads (§1, a lossless transport cannot mark the frontier) is repaired in the same
  owners by the transport's modulus, not carried to a new consumer.
- **5, an uncertified step.** The modulus moves inside the committed move, under every commit guard:
  passive (`ρ ∈ [ρ/2, 1]`), on the lattice, the first order certified on the exact carried storage
  moves, `F` strictly lower by disjoint enclosures.
- **6 and 8, seen as unseen.** The confirmation seeds below are read by no run before this commit;
  the seed test re-reads Stage 0's held-out requests for comparability only and makes no transfer
  claim.
- **9, a larger limit.** Every run is projected from a development read and pinned with its
  deadline; a run that reaches it is reported incomplete and not rerun.
- **11, the programming language.** The law is stated as a transport's modulus, a span's
  transported mass and the lag at which a term enters a phase-carried face; ages, arrays and
  batches are its realization.

## 1. The law, derived

**The span.** The request's cells cross the receiving ring's section at its ticks up to `τ`, the
section's stations at `τ + 1 + j`: one clocked span, one tube. Each crossing's datum is carried to
the reading frame by the source navigator's transport `Ĝ(τ ← τ_k)`, and the span is read over its
transported mass:

```text
w_k = |Ĝ(τ ← τ_k)| / Σ_(l∈span) |Ĝ(τ ← τ_l)|          (Lean transportedWeight)
Σ_k w_k = 1                                          (transported_weight_mass)
w(c·m) = w(m)                                        (transported_weight_frame_invariant): frame-free
a split of one span into request and section leaves every weight   (passage_weight_split_invariant)
separate populations weigh a section datum n/v times a request cell, alike iff n = v
                                                     (separate_populations_ratio)
```

Both candidates (a) and (b) of the brief are this law; they differ in the transport's modulus.

**(a) A unitary transport** (the closing rotor ring's rotation, modulus one on every node): every
crossing weighs `1/(n + v)`, the one population (`transported_weight_unitary`,
`passage_weight_one_population`, `passage_read`). It removes the asymmetry between the seed and the
section. It does not make the seed readable: in the bank's phase-carried face `Σ_k u^(r_k) g_k` at
a unit phase `u`, a crossing's term has the same modulus at every lag `r`
(`lossless_term_modulus`), so the only lag-selectivity left is `E`'s key through the pump's square
law, against every other crossing of the passage at equal weight. The development reads (§4)
measure it: a teacher-forced fit under (a) reads 386 of 1,024 held-out decisions (the retired law's
fit read 869), and an on-policy fit releases no whole section.

**(b) A dissipative transport** of modulus `0 < ρ ≤ 1` a tick (a rotation–dilation; the winding
guide §3): a datum `a` ticks old at the span's end weighs `ρ^a / Σ_k ρ^(a_k)`; older crossings weigh
no more (`decayed_weight_antitone`), the weights are frame-free (`decayed_weight_frame_free`), and at
`ρ = 1` it is (a) (`decayed_weight_lossless`). The term at lag `r` of the face has modulus
`ρ^r |g|` (`dissipative_term_modulus`): the span's frontier, where every continuation's seed lies,
is marked by the transport itself. Every crossing still enters; nothing is dropped by length.

**The choice** [agent-inferred]: **(b), with the modulus a constitution locus the executed
comparison learns, one at the founding.** Reasons:
1. The section continues the request's passage; the weights are the span's (both candidates).
2. At a unitary transport no reading of the phase-carried face marks the frontier (the Lean
   statement above), and the order-2 continuation, like any continuation of a stream by its most
   recent crossings, lives at the frontier. The development reads confirm the derivation: under
   (a) the fitted `E` cannot read the seed; with the transport's decay it can.
3. The decay is the passage's physics, a passive element of the navigator (`ρ² ≤ 1`, dissipation
   `1 − ρ² ≥ 0`), "weak waves die at comparison": the comparison that the release executes sets how
   fast, through its own covector (`BankPlacement::modulus_derivative`), not a declared horizon.
4. "Nothing is lost by default": the founding's modulus is one; dissipation appears only where the
   executed comparison's descent puts it.

**The modality statement.** A text cell at its tick, an image pixel at its scan tick, an acoustic
sample at its sample tick and a motor screw at its step are crossings of a ring's clock, carried by
the same transport and weighed by the same law. Nothing reads a window, a suffix depth, a position
table or the terrain's lag; the modulus is one scalar a source ring.

**Scope, owed** (THE_REBUILD U6; #62 text in the result record). The ages are read from the phases,
exact within one turn: a passage whose ticks and extent exceed the ring's period, or one re-keyed
within its span, is refused below modulus one (`HnnError::AliasedAges`); the leaky count that
carries the weights across turns is owed. The card refuses a modulus below one (its open reads one
population). The bank's face path refuses it (`FaceTransport`: its shared resonance is one a
request only at modulus one).

## 2. What is built (`bdf21a13`)

- `hnn::moment`: `SourceMoment::continued` (the section counted into the request's phase counts;
  it replaces `SourceMoment::section`), `phase_weights`, `open_parts`, `PopulationChart::chart`.
- `hnn::prediction`: `BankPlacement` on the passage (`weights`, `storage`, `modulus_derivative`),
  `Refinement::passage`, one passage for `stage`, `generate` and `comparison_code`; `injection`
  retired (an alias of `open_storage` once there is one passage).
- `hnn::executed`: the returns in one form for the request's phases and the section's classes, the
  modulus's slope `γ_ρ` and the joint committed move; `SourceMove` retired (a storage move is the
  successor's storage less the base's).
- `hnn::constitution`: the transport modulus (`with_transport`, guards), `ConstitutionRead::transport`.
- `holonics-cuda`: the publication refuses a modulus below one.
- Lean `HNN/IndexedOpen`, section 4: 13 theorems, standard axioms only.
- The probe mirrors the owner (`model.placement_counts`, `DECAY`); `eO_fit.py` fits `E` and `ρ` on
  the release's own trajectory; `export.py` writes `ρ`; `native-release` reads it; the executed
  loop's `E` files carry `ρ`.

## 3. The acceptance, fixed before any measured run

1. **Every exact check holds**, every guard a commit guard: every adopted move holds every guard
   (the harness prints each); on every read release every lock certified, no refused certificate;
   the gates of §6.
2. **The seed test.** The probe fits `E` and `ρ` on the release's own trajectory from the opening
   (`E₀` the sign sequence over two, `ρ = 1`): `eO_fit.py order2 400 256 101 0.03 0.05 1 16`
   (400 steps, 256 training requests at the probe's seed 101, Stage 0's training draw; batch 16;
   the entry bound's box). The last `E` and `ρ` are exported (`export.py … order2 1000104 128 … ρ`)
   and read natively from the open section (`bank_causes -- native-release`) on Stage 0's 128
   held-out requests (seed `101 + 1,000,003`), `E` and `ρ` rounded to the source port's lattice.
   Reported: released, held, refused; whole sections (against 17); the first lock at station 0 or 1
   (against 44) and the first lock right (against 57); sections following the rule among their own
   stations (against 97); stations right (against 404); native against float agreement; the fitted
   `ρ`. **Item 2 improves** when whole sections exceed 17 and the first lock is right more often than
   57.
3. **Confirmation, if item 2 improves.** The certified executed comparison trains `E` and `ρ` from
   the opening along the machine's own open-section trajectory (`executed train executed-open order2
   2026093011 8 16 3600000 …`: 16 moves of 8 fresh requests at training seed `2_026_093_011`), then
   the opening and the trained constitution generate 128 fresh order-2 requests at seed
   `2_026_093_012` (`executed evaluate order2 2026093012 128 … opening executed-open=…`). Neither seed
   is read by any run before this commit. Reported: whole sections against the opening; the first
   lock at station 0 or 1 and whether it is right, separately; holds and incorrect releases; the
   trained `ρ`; the complete synthetic outputs (a receipts file). Passes when the trained constitution
   releases strictly more whole sections than the opening, with item 1 holding.
   **Regressions**: the same arm, 8 moves of 8, on the alternation (training seed `2_026_093_013`,
   confirmation `2_026_093_014`) and on the line (`2_026_093_015`, `2_026_093_016`), 128 requests
   each; each passes with no fewer whole sections than its opening.
4. **Time and memory**: every run within its deadline and a resident set of 4 GB; a run past its
   deadline is reported incomplete, never rerun with a larger one.

## 4. The development reads (development seed 41 only)

**Teacher-forced fits by transport modulus** (the probe's `eR_fit.py order2 executed 400 256 41 0.03
causal` at a fixed `ρ`, then `eG_generation.py` on 128 development held-out requests; floats in an
exterior probe only; the counts are exact):

| `ρ` | held-out teacher-forced (of 1,024) | release, the machine's order: whole / stations / first lock at 0 or 1 | release in clock order: whole / stations |
|---|---|---|---|
| 1 (a) | 386 | 0 / 351 / 43 | 0 / 324 |
| `9/10` | 907 | 0 / 1 / 0 | 56 / 653 |
| `4/5` | 1,016 | 0 / 230 / 0 | 120 / 992 |
| `13/20` | 1,023 | 0 / 277 / 0 | 128 / 1,024 |
| `1/2` | 1,024 | 0 / 237 / 0 | 128 / 1,024 |

At a unitary transport the seed is not read even teacher-forced; with the decay the rule is read
whole in clock order, and the release's own order, which the teacher-forced fit never trained, locks
the far stations first from their own image.

**On-policy fits** (`eO_fit.py order2 300|400 256 41 0.03 lr_ρ ρ₀ 16`, the release's own trajectory):

| Start | `lr_ρ` | Steps | Final `ρ` (float) | Whole | Stations | First lock right | Consistent |
|---|---|---|---|---|---|---|---|
| `ρ = 1` held | 0 | 300 | 1 | 0 | 251 | 27 | 0 |
| `ρ = 4/5` held | 0 | 300 | `4/5` | 31 | 676 | 127 | 93 |
| `ρ = 13/20` held | 0 | 300 | `13/20` | 0 | 530 | 128 | 1 |
| `ρ = 1` learned | `1/50` | 300 | between `7/10` and `3/4` | 10 | 635 | 127 | 33 |
| `ρ = 1` learned | `1/20` | 400 | between `7/10` and `3/4` | 39 | 668 | 128 | 128 |
| `ρ = 1` learned | `1/10` | 400 | between `7/10` and `3/4` | 9 | 619 | 128 | 42 |
| `ρ = 9/10` learned | `1/50` | 300 | between `7/10` and `3/4` | 32 | 641 | 128 | 118 |

The pinned protocol takes `lr_ρ = 1/20` from these reads. The released sections of the best fit
follow the rule on the chain seeded by the request's last cell and repeat it on the other chain
(the development native read below shows `0 0 1 1 2 2 3 3`-shaped releases): the seed `x_38` is the
weaker read.

**Native development reads.** The best on-policy fit exported and read natively on 16 development
held-out requests: its rounded modulus `782945/1048576`; native and float releases agree at 128 of
128 stations; 57,336 ms, resident 99,135,488 bytes. Three moves of the native `executed-open` arm
from the opening at development seed 41 (8 requests a move): nothing released at the opening, `F`
fell at every move, the modulus stayed at one; 5,721, 6,967 and 79,122 ms; resident at most
171,675,648 bytes.

**Projections and deadlines:**

| Run | Projection | Deadline |
|---|---|---|
| seed test fit (float, 400 steps) | 1,000,000–1,600,000 ms | 2,400,000 ms |
| seed test native read, 128 requests | 400,000–600,000 ms | 900,000 ms |
| order-2 training, 16 moves of 8 | 200,000–3,000,000 ms | 3,600,000 ms |
| order-2 confirmation, 2 × 128 | 100,000–700,000 ms | 1,200,000 ms |
| alternation and line training, 8 moves of 8 each | 100,000–1,800,000 ms each | 2,400,000 ms each |
| their confirmations, 2 × 128 each | 100,000–700,000 ms each | 1,200,000 ms each |

The runs go one at a time on the host's cores; the float fit alone.

## 5. What is expected, named before the runs [agent-inferred]

- The seed test: the transport's decay lets the fit read the chain seeded by `x_39`; the chain
  seeded by `x_38` stays the weaker read under the release's own lock order, so whole sections sit
  near those whose two seeds agree plus the ones read right.
- The confirmation: the native move is certified and small; from the opening nothing is released
  and the modulus's slope may keep it at one for the first moves (the development read). **The
  expected blocker** is that 16 certified moves do not move `ρ` far enough from one for the
  frontier to be read: the executed comparison's descent then learns the threshold and the
  termination first, as on September 30.
