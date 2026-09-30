# The bank reads a superposed passage: the locks continue a spectral line, and the order-2 terrain stays at the marginal

**Date.** September 29. **Issues.** #73, #148, #63 (THE_REBUILD U6). **Grade.** [measured] for the
runs (§3, §4), each run once under the
[pins](2026-09-29_THE_BANK_READS_A_SUPERPOSED_PASSAGE_PINNED_BEFORE_ITS_RUNS.md) (`24691714`) at the
build `e70e992f`; [proved-derived; formal-checked] for the Lean (§2); [agent-inferred] where marked.

**What ran.** The parametron record's open item (§6 there): the bank read two cells, each pumping its
own crossing, not the superposed passage. The build reads the passage: the receiving ring's storage
(every datum placed at its residue through the source port) crosses the section node by node as the
ring turns, each crossing pumps every member, and the passage's monodromy over the turn is read by
its exact growth. Generation locks the section's stations by the bank's reading. `hnn::ring`'s
header, "The passage's monodromy", and `hnn::prediction`'s, "The bank reads the superposed passage",
own the definitions.

```sh
cargo run --release -p holonics --example hnn_prediction -- order2 bank
cargo run --release -p holonics --example hnn_prediction -- text .local/cuts/curated-u6-passage-cut.bin <owner-only file> bank
```

The computational object is the helical pair interaction, the rings complex parametrons. Of the
[winding guide](../../docs/WINDING_CARRY_AND_PLACEMENT.md)'s six objects it touches four: the helix
(the pump's clock and the placed phases), the cell holonomy (the passage's monodromy), faces and
placement (the bank's locked faces, the section's placement) and the tube (the section's span, the
turn's ticks). The pair (two crossings composing through the transport) and the tower thread (the
growth enclosed at a dyadic grain) stay attached.

## 1. The lessons it answers

The pin's §0, each held:
- **1, an authored routine.** No class is computed by a routine: the bank is the parametron record's
  declared bank, unchanged, and a station's class is the candidate its own Floquet growth reads
  strictly highest. Nothing names a lag, a shift or the terrain's rule.
- **2, recitation or an index.** The bank reads the ring's storage, the moment's placement through
  `E`; no window, pair table or copier. The held-out requests are fresh draws.
- **3, text as the exception.** One construction for every stream: the ring's storage through `E` at
  the data's residues. Its one known truth, a spectral line (§2), is the periodic component any
  image or acoustic stream carries.
- **4, the byte marginal.** Named before the run as text's expected blocker (the request's moment
  normalized over its population holds the marginal's image at `n ≫ D`).
- **7, bits read as progress.** The bank's sections have no code; the order repair's training code is
  reported beside the runs only.
- **9, a larger limit.** No bound moved; each run ran once within its bound.

## 2. The law and its Lean

**The pump, the monodromy, the growth.** Tick `t` of the turn reads node `d − 1 − t` of the receiving
ring's storage (the passage in its own time order around the turn); member `(a, s)`'s stiffness is
`K − 2p R(a² s^t z_t)`, each tick certified by its signed form. The monodromy `M = T_(d−1) ⋯ T_0` is
carried on integers as `N/Δ`; its growth `lower ≤ ρ(M) < upper` is enclosed at the relative grain
`2^(−g)` by bisection, each step the Schur–Cohn test on `det(Δμ − N)` (every root strictly inside a
circle), the bracket attained on a shifted copy and certified by two exact tests. The certificate of
a lock attains its metric by the Stein solve of the rounded monodromy and certifies it by inertia on
the exact one, and runs the executed turn with every balance checked. A member reads a turn only
when its pump's period divides the turn; the bank's joint growth is the largest member's.

**What it reads.** Lean `HNN/FloquetPassage` (the kicked chart, a crossing `Rot_v(1 + p R_u)`), with
`#print axioms` propext, Classical.choice and Quot.sound only:
- a reflection absorbs a turn on either side, and two crossings separated by the ring's transport
  compose to the turn by their relative phase less the transport, `R_u Rot_v R_w = Rot(u v̄ w̄)`
  (`reflection_mul_rotation`, `rotation_mul_reflection`, `reflection_transport_reflection`,
  `reflection_transport_reflection_carriers`, `rotation_trace_carrier`; the carrier forms
  `rot_mul_rot`, `rot_mul_ref`, `ref_mul_rot`, `ref_mul_ref`);
- one crossing more composes the passage's expansion in the pump (`kick_coeff_zero`, `kick_coeff_one`,
  `kick_coeff_two`), and over a whole passage of `n` crossings `c₀ = Rot(v^n)`,
  `c₁ = Σ_t R(v^(n−t) u_t v̄^t)`, and the second order is every ordered pair's transported turn,
  `c₂ = Σ_(t<n) Σ_(s<t) Rot(v^(n−t) v̄^(t−s) v^s u_t ū_s)` (`passage_coeff_zero`,
  `passage_coeff_one`, `passage_coeff_two`): for a unit transport, the carriers read at the ring's
  parametric resonance;
- at a whole turn the second order's trace is the passage's power spectrum,
  `2 Re Σ_t w_t conj(Σ_(s<t) w_s) = |Σ w|² − Σ |w|²` (`pair_sum_power_spectrum`).

**Known truth: the bank reads a spectral line and its lock's flip continues it** (the owner's test
`the_bank_reads_a_passages_spectral_line_and_its_flip_continues_it`, exact at the grain `2^(−10)`, on
every class and every offset). On a turn of 8 unit cells stepping one quarter-turn class `j` a
crossing, member `m`'s reading depends only on `m − j (mod 4)`:
- the line's own member (a standing pump) grows in `[46, 1473/32]`;
- the two quarter-turn neighbours, nearest the node's parametric resonance, grow in
  `[1061/16, 531/8]`;
- the half-turn partner is certified silent, in `[827/1024, 1655/2048]`.

The lock pattern names the line's class. With the last cell open, the candidate completing the line
reads the joint growth `[1061/16, 531/8]`, strictly above the others' (`[35, 1121/32]` twice and
`[1779/64, 445/16]`), and the bank locks there. [re-derived] The parametron record's reading of the
bank ("locks at the one member whose declared phase aligns the cells") holds for two cells at
`p = 5/8`; on a passage the quarter-turn neighbours grow more than the aligned member, because a
quarter-turn pump sits nearer the node's parametric resonance (`2θ`, `e^(iθ) = (3 + 4i)/5` less its
port's loss) than a standing one. The class is read by the silent member, not the loudest.

**The consumer.** `generate_by_bank`: every unlocked station's every class placed with the locked
data (`BankPlacement`, held to `injection` exactly by the owner's test), the bank's joint growth read,
a station's top taken by the lock's flip on exact enclosures (`θ = a/(a + K) > ½ ⇔ a > K`) where the
bank locks, the largest gap locking, each lock certified, the release through `receiver::release`.

## 3. The runs

**Acceptance 1, the exact checks: holds on both runs.**

| Run | Training refinements: balances, pairings, commits, energy bound | Unreached checks (loci) | Bank locks: members certified, executed ticks closed |
|---|---|---|---|
| `order2 bank` | 512 of 512 each | 32 of 32 (224) | 8,192 of 8,192; 491,520 of 491,520 |
| `text … bank` | 770 of 770 each | 50 of 50 (350) | 256 of 256; 8,960 of 8,960 |

The certified storage growth was 0 at every deposit (its product 1) on both. The standing's fold took
31 of 31 lock proposals on the order-2 training (999 half-turns) and 46 of 49 on text (1,310
half-turns); the order repair's own generation closed 1,872 of 1,872 refinements' balances.

**Acceptance 2, known truth: the order-2 terrain.** 256 fresh requests, 2,048 held-out stations.

| Reading | Released | Exact | Stations right | By station (of 256) |
|---|---|---|---|---|
| **the bank's locks** | 256 | 0 | **508** | 56, 62, 78, 60, 55, 55, 67, 75 |
| the order repair's linear readout, this run's constitution (control) | 255 | 21 | 638 | 82, 79, 81, 79, 83, 76, 81, 77 |
| the order repair's linear readout, its own receipt (`af5e7de6`) | 249 | 39 | 866 | 112, 112, 111, 108, 108, 107, 108, 100 |
| the static marginal (class 0) | — | — | 512 | — |
| the per-station marginal | — | — | 520 | — |

- **The bank reads 508 of 2,048**: 4 below the static marginal and 12 below the per-station one. It
  does not reach order: the acceptance's comparison fails.
- Every section was released at width zero (2,048 refinements, one lock each; 46,080 turn readings);
  every lock was the lock's flip on exact enclosures, the locked readings' growth from `33347/8192`
  to `138036`, the least margin over a runner-up `753/2048`.
- **The training reaches nothing the bank reads.** On the first 32 held-out requests the bank on the
  declared opening (`Constitution::initial`, nothing deposited) generates sections equal to the
  trained constitution's on 256 of 256 stations (64 of 256 right, the marginal's quarter).
- **The control moved.** On this build the order repair's linear readout reads 638, not its
  receipt's 866: the training now takes the standing's fold's half-turns (31 of 31 proposals), and
  the trained constitution differs. Its training code over the compared stations is
  `4020 + 7/16 + ε` bits (the order repair's `4212 + 1/16 + ε`), beside the counts.

**Acceptance 3, text: fails.** Two passes over the U6 choosing role's 385 pairs (`D = 35`, the bank
its standing member alone), then the 8 validation requests F0's rule selects. All 8 sections were
released at width zero (256 locks, one a refinement; 1,085,568 turn readings; the locked readings'
growth from `96447/4096` to `130771/128`, the least margin over a runner-up `59/4096`), of 32, 32, 32,
20, 31, 15, 32 and 32 bytes before the termination. **None is UTF-8; the output is illegible.** The
sections are owner-only and were shown in the conversation whole, with nothing beside them. What
they read, by count only: one small set of byte values recurs across all eight requests (control
bytes and bytes that form no UTF-8 character, with `%`, `.` and `>`), and the two requests of 2,932
bytes gave identical sections. The training code over the compared stations was `95129 + 1/16 + ε`
bits, beside the run.

## 4. Time and memory

| Run | Measured | Projection | Peak resident bytes |
|---|---|---|---|
| `order2 bank`: training | 225,461 ms | 150,000–300,000 | |
| the order repair's generation | 82,886 ms | 60,000–150,000 | |
| the bank's generation | 1,053,993 ms | 900,000–1,400,000 | |
| the opening's diagnostic | 61,503 ms | 100,000–200,000 | |
| in all | 1,423,845 ms | bound 2,400,000 | 1,218,473,984 |
| `text … bank`: training | 438,715 ms | 350,000–540,000 | |
| the bank's 8 sections | 670,750 ms | 600,000–1,500,000 | |
| in all | 1,109,477 ms | bound 2,400,000 | 858,509,312 |

No run reached its bound or stop; every run is complete. The opening's diagnostic finished below its
projection (it reused the trained sections instead of generating them again).

## 5. What the measurement located [agent-inferred]

- **The bank reads the passage, and continues only what the passage carries.** The reading is exact
  and certified at every lock (8,192 and 256 member certificates, every executed tick closed), and
  on known truth its lock's flip continues a spectral line. The order-2 terrain's rule is not a line
  of its request: the request is 40 uniform cells, and the rule relates each station to the cell two
  back. A declared bank has no key naming that lag and that relative phase, so its stations read at
  the marginals (508 against 512 and 520; each station between 55 and 78 of 256).
- **The training reaches nothing the bank reads** (the blocker, by its measurement: 256 of 256
  stations equal on the declared opening). The placement `E` is trained through the linear readout at
  certified steps of `2^(−16)` and below, and no covector of the lock's decision reaches `E` or a
  member's pump. The certified step now reads a pumped ring's reach (main `57b1d9a8`), but that path
  runs the field's declared pumps, linear in the data; the bank's square law is in no comparison.
- **The section outweighs the request in the turn.** Each placement is read over its own population
  (the source contract's port): a lone candidate weighs one, a request cell one over the request's
  length. So the turn's growth is set mostly by the candidate's and the locked cells' own images
  through `E`'s declared sign sequence: on text one small set of bytes recurs across all eight
  requests, and identical requests give identical sections. This is failure 4's located cause in
  the bank's reading: the request's moment at `n ≫ D` is its marginal's image, and the section's own
  cells are not.
- **The linear readout moved on this build.** The order repair's control reads 638 where its receipt
  read 866: the standing's fold now takes the lock's half-turns in this training (31 of 31). Its
  located cause (the placement's linear separability) stands; the fold changed the trained
  constitution it reads.
- **The next loop's subject** is the learning path the bank lacks: a covector of the lock's decision,
  the second order's quadratic form in the placed amplitudes (`passage_coeff_two`'s turns), carried to
  `E` and the members' pumps and stepped under the pumped monodromy's certified reach.

## 6. Owed in #62

"The bank reads a superposed passage" (September 29):
1. **The executed law's second order.** The kicked chart's closed form is proved
   (`passage_coeff_two`); the executed Cayley tick with the pumped stiffness, expanded in `p`, its
   pair terms the transported pairs of the executed transport, is owed.
2. **The growth against the second order.** Past the perturbative regime, the ordering of
   candidates by the monodromy's growth against their ordering by the passage's power spectrum at
   the resonance.
3. **The spectral line's symmetry.** A member's reading of a line depends only on its step less the
   line's class and not on the line's offset (a global phase on every carrier conjugates the
   monodromy by the half-angle turn), and the half-turn partner's silence; measured exactly, not
   stated.
4. **The Schur–Cohn test** over `ℝ[X]` (every root strictly inside the unit disc iff `|c₀| < |c_n|`
   and the reduced polynomial's are), and with it the growth enclosure's correctness.
5. **The bank's learning path.** A covector of the lock's decision (a smooth face of the growth: the
   second order's quadratic form in the placed amplitudes) reaching the placement `E` and the
   members' pumps, and the certified step through the pumped monodromy it reads.

## 7. The verdict

- **Acceptance 1 holds**: every balance, pairing, commit, energy bound, unreached-locus check,
  Floquet certificate and executed turn closed on both runs.
- **Acceptance 2 fails its comparison**: the bank's stations read 508 of 2,048, at the marginals
  (512, 520) and below the linear readout (638 on this build, 866 at its receipt).
- **Acceptance 3 fails**: 8 sections released, none legible.
- **The reading itself is built and exact**: the passage's monodromy through every crossing's pump,
  its second order proved in closed form (Lean `HNN/FloquetPassage`), its growth enclosed and
  certified, and its lock's flip continuing a spectral line on known truth. Generation from it
  waits on its learning path.

## 8. Gates

- `cargo check --workspace --all-targets`: clean.
- `cargo test -p holonics --lib`: 949 passed, among them the passage reading's
  (`the_turn_reading_is_the_executed_monodromys_growth`,
  `the_bank_reads_a_passages_spectral_line_and_its_flip_continues_it`,
  `the_placed_schedule_of_unit_cells_is_the_modulated_schedule`,
  `a_member_reads_a_turn_only_when_its_period_divides_it`) and generation's
  (`the_bank_placement_is_the_sections_injection`, `the_bank_generates_by_its_certified_locks`).
- `bash tools/lean_check.sh Holonics HolonicsResearch`: 10,249 jobs built, no `sorry`.
- The GPU suite: not run. No HNN behaviour on the card changed (the CUDA crate reads none of the
  changed items; the field's words and deposition are unchanged, and their host tests pass), and the
  worker's isolated worktree could not take the card's lock.

Main was merged at `57b1d9a8` (the certified step reads the Floquet reach) before the pin; the one
conflict was `hnn_prediction`'s imports.
