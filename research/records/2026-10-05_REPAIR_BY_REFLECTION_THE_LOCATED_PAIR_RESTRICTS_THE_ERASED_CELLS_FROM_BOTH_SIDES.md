# Repair by reflection: the located pair restricts the erased cells from both sides, every released cell is its truth, and a held chain costs one patch

**Date.** October 5. **Issues.** #73, #148, #63, #62. **Lanes.** B and C of U6 (THE_REBUILD, "U6's
order from October 5", the paragraph "The task is repair, not continuation"). **Grade.**
[definition; agent-inferred] for the pins of §0, fixed and committed before any read (`7109bc11`,
amended before the read at `43788fb9`); [measured] for every count of §4–§7 (the runs of
`2026-10-05_REPAIR_BY_REFLECTION_receipts/runs.sh` at `43788fb9`); [proved-derived] where marked.

**Occasion.** Brandon, October 5: "the predicting next tokens is just not a good computational
ontology"; the use is "repairing/decrypting information generally in order to produce
codecs/generators about the information". Generation is the progressive restriction of a
compatible family, `F_(k+1) = T_(g_k)(F_k) ∩ C_k` (atlas `tube.generation-step`, Lean
`Transport/ArtifactRelease.step`); continuation is the special case whose damage is the tail. This
loop builds the first repair terrain on known truth and reads it once.

## 0. The claim and the pins, fixed before any read

**The terrain** [definition; agent-inferred].
- **The field**: the order-2 declaration unchanged (`order_declared`: three rings of period
  `60 = 2²·3·5` in a chain, ring 0 the source ring, its port chart `port(x) = x mod 60`). Only ring
  0's clock and port chart are read: a distance `δ` is a residue of its clock.
- **The passage**: `L = 48` cells (`n + m` of step 1's shape, one span within one turn of the ring,
  `48 < 60`): a request-like **opening** of `o = 8` cells, then 40 cells of the rule. The emitters
  are the harness's one terrain owner (`terrain_pairs`) with the request `8` and the stations `40`:
  - **order-2**: the opening drawn uniformly on `ℤ/4`, then `x_t = x_(t−2) + 1 (mod 4)`;
  - **the line**: `x_t = x_0 + s t (mod 4)` over the whole passage (`x_0, s` drawn), so
    `x_t = x_(t−4)`;
  - **the alternation**: `a b a b …` over the whole passage (`a, b` drawn), so `x_t = x_(t−2)`
    (`f = id`; a full terrain here: the bank's release reads it whole since #365, and the
    restriction below reads no bank).
- **The alphabet** `A = ℤ/4` (the terrain's residues; the exterior chart's termination is not a
  class of the passage). Each class holds its own port.
- **The damage**, declared, the same positions on every passage of a read set (cells indexed from 0):
  - **A, spans**: `{3}` (inside the opening, beyond the rule's reach), `[6, 10)` (straddling the
    opening's end: two antecedents and two stations), `[20, 25)`, `[33, 37)`, and the tail
    `[44, 48)` (continuation as the special case). 18 erased, 30 intact, 25 intact stations.
  - **B, a residue chain**: every odd cell `7, 9, …, 47`. 21 erased, 27 intact, 20 intact stations.
- **The seeds**, searched in every ref's history (`git log --all -G`), the tree and the local run
  artifacts: `2_026_100_7xx` appears nowhere (`2_026_100_501`–`503` are test seeds;
  `2_026_093_0xx` are THE_TWO_COUNTS' and are spent or reserved). Development (readable, timing and
  checks): `2_026_100_701`. **The read, once each, 64 passages**: damage A, order-2 `2_026_100_711`,
  the line `712`, the alternation `713`; damage B, order-2 `2_026_100_721`, the line `722`, the
  alternation `723`.

**The path** (no target is read before release; the truth is read only to score).
1. **Differentiate.** An observation is an intact station `t ≥ o`, read in passage order. It reads
   its edge `port(x_(t−δ)) → port(x_t)` at every distance `δ ∈ [1, min(t, d − 1)]` whose antecedent
   is intact: an erased cell contributes no edge, as antecedent or as station. The edges enter lane
   B's turn menus (`compression::keys::TurnMenu` through `hnn::keys::PairLocation`), and the pair is
   located by the windings law (`PairSurvivors::located`) at the read set's end.
2. **Integrate by reflection.** The located pair `(δ, f)` is the relation `x_t = f(x_(t−δ))` at the
   stations it was read at (`t ≥ o`). Every cell's compatible family (its class if intact, `A` if
   erased) is restricted jointly from both sides, the antecedent through `f` and the consequent
   through `f⁻¹`, until no family changes. A class whose consequence was never read restricts
   nothing (the turn menu's publication law). A cell is released where its family is one class and
   the restriction is certified (every class left in every family is held by a member of the
   nonempty joint fibre); it is held with its plural family otherwise, through `receiver::release`
   at tolerance zero.
3. **The codec** (the Fold's side residual): the located key, written as `δ − 1` in
   `⌈log₂(d − 1)⌉ = 6` bits and each class's consequence (or "unread") in `⌈log₂ 5⌉ = 3` bits,
   `6 + 4·3 = 18` bits once per read set; then, per passage, while a cell is held, the truth's
   index in the first held cell's family in `⌈log₂ |F_t|⌉` bits, that cell pinned and the
   restriction re-run. It is decoded by the same restriction and checked to reopen every passage
   exactly.

**The measures** [definition]. Per terrain and damage: cells released and held; certified
fidelity (released cells equal to their truth); valid decode (every released cell is a class of
`ℤ/4`: true by construction, since a family is a subset of `A`); the codec's bits (key plus
residual) against the literal erased cells' bits (`2` a cell), with the Fold's lower bound
`⌈log₂ N⌉`, `N` the joint fibre of a passage's held cells (`residual_injective_on_fibre`);
`n*_machine`, the observations from which the located pair holds to the read set's end, against
`n*_terrain`, the least observation count at which the declared reference family (THE_TWO_COUNTS'
global family: lags `[1, 40]` and every map `ℤ/4 → ℤ/4`, `10240 = 2¹¹·5` keys, each lag reading
only intact arguments) restricts every erased cell of the read set to its family under the
terrain's generating key (the union over the surviving keys, an unobserved argument emitting every
class).

**The claim, fixed before the read** [derived from the law on the declared damage; agent-inferred].
On every terrain the machine locates the generating key: order-2 `(2, y ↦ y + 1)`, the line
`(4, id)`, the alternation `(2, id)`, each total on `ℤ/4`. Then:
- **damage A**: 17 of 18 erased cells released per passage, every one equal to its truth; cell 3
  held with family `ℤ/4` (neither its antecedent nor its consequent is a station the key was read
  at); residual 2 bits a passage; the codec `18 + 2·64 = 146` bits against the literal
  `36·64 = 2304`;
- **damage B**: order-2 and the alternation hold all 21 erased cells with family `ℤ/4` (the chain
  `7, 9, …, 47` touches no intact cell through a read station: the edge `5 → 7` lies in the
  opening), joint fibre `N = 4`, one 2-bit patch reopening all 21; the line releases the chain
  `9, 13, …, 45` (10 cells, from the opening's cell 5 through the station 9) and holds the chain
  `7, 11, …, 47` (11 cells, `N = 4`); the codec `146` bits against `42·64 = 2688`.

A released cell that differs from its truth, a located key other than the generating one, or a
codec at or above the literal falsifies the claim.

**Amendment, after the development read (`2_026_100_701`) and before the read** [agent-inferred;
receipts `development/`]. The development read met the claim's every count on all six units, and
found two defects in the read-only `n*_terrain` instrumentation, none in the machine's path:
- **The repair's grain is ill-posed where the reference keeps weak aliases.** On the line and the
  alternation under damage A the stopping object does not hold even at the read set's end: lags
  such as `(40, id)` on the line are true of the terrain, so no observation removes them, and they
  restrict less (cell 6 is joined only to cell 46, itself erased), so the union over independent
  keys stays wider than the generating key's family. The reference treats each lag as a separate
  emitter and cannot prefer the generator over its windings.
- **It is degenerate under damage B** on order-2 and the alternation: the generating key releases
  no cell there, so the union equals its families before any observation (`n*_terrain = 0`).

Both are reported as pinned. Beside them the read reports the two counts' own **syntactic class**
(their pin §4): the least observation count from which the reference survivors (each lag's life
and map) no longer change, well-posed on every terrain and damage. Nothing else changed.

The computational object is the helical pair interaction. Of the
[winding guide](../../docs/WINDING_CARRY_AND_PLACEMENT.md)'s six objects this loop touched **the
pair** (the contact between crossings `δ` ticks apart, now read in both directions: `f` from the
antecedent, `f⁻¹` from the consequent), **the tube** (generation as a tube whose cross-section is
restricted, `F_(k+1) = T(F_k) ∩ C_k`) and **the helix** (a distance is a residue of the source
ring's clock; the relation's chains are the residue classes of `ℤ/δ`). The cell holonomy (the turn
menu's loop law, which locates the pair unchanged), faces and placement (the bank's reading, not
read here) and the tower thread stay attached and unchanged.

## 1. The recorded failures this loop could repeat, and how each was held

From the [lessons](2026-09-29_LESSONS_THE_FAILURES_THAT_REPEATED_AFTER_THEY_WERE_RECORDED.md), the
[prototypes' lessons](2026-09-24_LESSONS_FROM_THE_WORKBENCH_AND_ATHENA_PROTOTYPES.md) and the
[contamination cycles](2026-10-05_THE_CONTAMINATION_CYCLES_EVERY_COPY_PIPELINE_FOLLOWED_A_DEMAND_FOR_OUTPUT_BEFORE_THE_FIELD_COULD_RELEASE.md):
- **1, an authored routine standing in for learning.** The restriction reads no rule: it applies
  whatever pair the turn menus located from the intact cells, in both directions. No distance,
  map or terrain is named to it; the harness's generating key is read-only instrumentation for
  `n*_terrain` and enters no restriction the machine runs. A wrong key is refused (an emptied
  family), never repaired around.
- **2, recitation or an index of contexts.** The repair reads the passage's own intact cells and the
  located pair (one distance, four consequences). Nothing is copied from another passage; a held
  cell is held, never filled from a seen one.
- **3, text as the exception.** A relation joins two ticks of a clock: a pixel's scan ticks, a
  sample's ticks and a motor step's join alike, and a damaged image or recording is restricted by
  the same law. The class relation is read from the located map through the port chart, refused
  where a port holds two classes (as the deposit refuses), so the byte chart's folded ports are a
  typed refusal here, not a special case.
- **Lesson 3, a located cause carried into a new consumer.** The bank's release is not this loop's
  consumer: the restriction reads the located pair directly, so the bank's open causes (the
  members' quarter-turn lines, the Lock interface) are not inherited. The located pair's
  location law is lane B's, unchanged.
- **6, seen graded as unseen.** The erased cells' truths are read by no run before the release; the
  read seeds are fresh (§0), distinct per terrain and damage, and the development seed is apart.
- **7, bits read as progress.** The codec's bits are reported beside the repaired passages and their
  fidelity, never as the success.
- **9, a refusal answered with a larger limit.** Each run has its deadline from a development
  measurement (§6).
- **11, the programming language.** The design is stated as a relation's chains (residue classes of
  `ℤ/δ`), a family's restriction from both sides of the clock, and the joint fibre's count.

## 2. The design, and its equations

**Differentiate** (`hnn::keys::damaged_station_pairs`, then lane B's `PairLocation` unchanged). An
observation is an intact station `t ≥ o`; it reads `port(x_(t−δ)) → port(x_t)` at every
`δ ∈ [1, min(t, d − 1)]` with `x_(t−δ)` intact. The pair is located by the windings law at the read
set's end (the aeon's boundary), and read as a relation on the classes
(`hnn::keys::LocatedPair::relation`): `R(a, b) :⇔ f(a) unread ∨ f(a) = b`.

**Integrate by reflection** (`compression::keys::repair`, the library owner; it lives beside the
turn menu because it is the Bombe's relation read the other way: the key known, the cells unknown).
With `D = [max(o, δ), L)` the stations where the relation holds:

```text
F_t⁽⁰⁾ = {x_t} (intact),  A (erased)
F_t ← F_t ∩ R(F_(t−δ))      if t ∈ D             the antecedent's side, f
F_t ← F_t ∩ R⁻¹(F_(t+δ))    if t + δ ∈ D         the consequent's side, f⁻¹
each sweep along the clock and back, until no family changes; an empty family refuses the key
```

The edges `(t − δ, t)`, `t ∈ D`, join each residue class of `ℤ/δ` into chains: a forest of paths.
On a forest the fixed point is the joint fibre's projection at every cell [proved-derived: arc
consistency on an acyclic constraint graph is global consistency; Lean owed, #62], and the owner
checks it exactly: along each chain, the members holding class `a` at cell `t` number
`fwd_t(a) · bwd_t(a)`, and the certificate holds at `t` when every class of `F_t` has a positive
count. The joint fibre is `N = Π_chains Σ_a fwd_end(a)`. An erased cell is decided by
`receiver::release` at tolerance zero on its class reading over the joint fibre: width `0` when its
certified family is one class (released), `1` otherwise (held with its family).

**The codec** (the Fold's side residual; Lean `Transport/Fold.reopen_apply_fold`,
`residual_injective_on_fibre`). The damage is the transition that drops the erased cells; the key
and the residual reopen them:

```text
key       = (δ − 1 in ⌈log₂(d − 1)⌉ bits) · (each class's consequence or "unread" in ⌈log₂(|A| + 1)⌉ bits)
residual  = while a cell is held: index of the truth in the first held F_t, ⌈log₂ |F_t|⌉ bits; pin; restrict
reopen(damage(x), key, residual(x)) = x         (decode(T_native(encode x)) = x at the consumer)
```

The residuals over one passage's joint fibre are a prefix code (each reopens its member and reads
no further), so Kraft's sum is at most one and the longest is at least `⌈log₂ N⌉`; when `f` is a
bijection each held chain costs one patch, whatever its length.

## 3. What was built

- `crates/holonics/src/compression/keys/repair.rs`: `PairRelation`, `DamagedPassage`, `restrict`,
  `Restriction::{families, chains, joint, support, release}`, `CellRelease`, `key_code`,
  `read_key`, `residual_code`, `reopen`; its tests (`keys/repair/tests.rs`): interior spans
  restored from both sides with a held cell in the opening; **a held chain where both sides leave
  the family plural** (every odd cell from 3 on order-2: every cell held with `ℤ/4`, `N = 4`, one
  2-bit patch reopens the chain); an unread consequence restricting nothing from its side; a key the
  intact cells refuse; and the brute-force check (400 drawn passages: the families are the joint
  fibre's projections, `N` its count, the restriction refuses exactly when the fibre is empty, the
  certificate holds, every member reopens from its residual, the residuals are a prefix code).
- `crates/holonics/src/compression/{mod.rs, cost.rs}`: the refusals `ZeroOffset`, `Contradicted`,
  `ReleaseLaw`; the cost owner's fixed-width index writer and reader opened to the crate.
- `crates/holonics/src/hnn/keys.rs`: `damaged_station_pairs`, `LocatedPair::relation`; the test
  `a_damaged_passage_locates_its_pair_from_intact_cells_and_is_repaired_through_it`.
- `research/notebook/hnn_design/hnn_repair_loop.rs`: `executed repair <terrain> <A|B> <seed>
  <count> <out>`, no per-terrain branch in the machine's path.

## 4. Measured: the read, once each (at `43788fb9`'s build)

[measured] `executed repair`, 64 passages a run, one thread; receipts `<terrain>_<damage>.{log,
sections, curve}`. Nothing changed after the pin's amendment. The claim of §0 holds on every count.

| Terrain, damage (seed) | Located key | `n*_machine` (first lock) | Released / held of erased | Released equal to the truth | Joint fibre `N` | Codec / literal (bits) |
|---|---|---|---|---|---|---|
| order-2, A (`…711`) | `(2, y ↦ y + 1)`, turns `15, 45` | 75 = 3·5² (75) | 1,088 / 64 of 1,152 | **1,088 of 1,088** | 4 on every passage | **146 / 2,304** |
| line, A (`…712`) | `(4, id)` | 74 = 2·37 (7: `δ 1`, a swap on `{0, 2}`) | 1,088 / 64 of 1,152 | **1,088 of 1,088** | 4 | **146 / 2,304** |
| alternation, A (`…713`) | `(2, id)` | 203 = 7·29 (7: `δ 1`, a swap on `{1, 3}`) | 1,088 / 64 of 1,152 | **1,088 of 1,088** | 4 | **146 / 2,304** |
| order-2, B (`…721`) | `(2, y ↦ y + 1)` | 40 = 2³·5 (40) | 0 / 1,344 of 1,344 | — | 4 | **146 / 2,688** |
| line, B (`…722`) | `(4, id)` | 161 = 7·23 (60: `(4, id)` on `{1, 3}`) | 640 / 704 of 1,344 | **640 of 640** | 4 | **146 / 2,688** |
| alternation, B (`…723`) | `(2, id)` | 81 = 3⁴ (40: `(2, id)` on `{0, 2}`) | 0 / 1,344 of 1,344 | — | 4 | **146 / 2,688** |

- **Every released cell equals its truth**: 1,088 of 1,088 on each damage-A run (17 a passage) and
  640 of 640 on the line under B (10 a passage). No key other than the generating one was located,
  no passage refused its key, and every certificate held.
- **Valid decode**: every released cell is a class of `ℤ/4`, `3,904 = 2⁶·61` of 3,904 over the six
  runs, by construction (a family is a subset of `A`).
- **The codec**: the key in 18 bits once, then 2 bits a passage (`64·2 = 128`), equal to the Fold's
  bound `Σ⌈log₂ N⌉ = 64·⌈log₂ 4⌉ = 128`: `146 = 2·73` bits against the literal `2,304 = 2⁸·3²`
  (damage A, ratio `73/1152`) and `2,688 = 2⁷·3·7` (damage B, ratio `73/1344`). Decoded from the
  one code (the key read back, each passage reopened in turn): 64 of 64 passages reopened exactly
  on every run, no trailing bit. A passage alone: `18 + 2 = 20` bits against its 36 (A) or 42 (B).
- **The restriction's work**: at most 2 sweeps (one through the passage and back that changes,
  one that does not); 1 ms for 64 passages.

**Four repaired passages, whole** (synthetic `ℤ/4`; `·` erased, `?` held with the family `ℤ/4`):

```text
order-2, A, passage 0
  damaged  013·12····2233001122·····12233001····3001122····
  repaired 013?12001122330011223300112233001122330011223300
  truth    013212001122330011223300112233001122330011223300
line, A, passage 2 (s = 1)
  damaged  123·12····3012301230·····23012301····2301230····
  repaired 123?12301230123012301230123012301230123012301230
  truth    123012301230123012301230123012301230123012301230
order-2, B, passage 1
  damaged  3110331·2·3·0·1·2·3·0·1·2·3·0·1·2·3·0·1·2·3·0·1·
  repaired 3110331?2?3?0?1?2?3?0?1?2?3?0?1?2?3?0?1?2?3?0?1?
  truth    311033122330011223300112233001122330011223300112
line, B, passage 14 (s = 3)
  damaged  0321032·0·2·0·2·0·2·0·2·0·2·0·2·0·2·0·2·0·2·0·2·
  repaired 0321032?032?032?032?032?032?032?032?032?032?032?
  truth    032103210321032103210321032103210321032103210321
```

In the first, cells 6 and 7 are restored through `f⁻¹` from the stations 8 and 9, which are
themselves restored through `f⁻¹` from 10 and 11 on the same sweep's return; the spans 20–24 and
33–36 from their antecedents; the tail from 42 and 43. On the line under B, the chain `9, 13, …, 45`
is released from the opening's cell 5 through the station 9, and the chain `7, 11, …, 47` is held:
its first edge `3 → 7` lies in the opening, so no intact cell reaches it. Its one 2-bit patch
(the truth at cell 7) reopens all eleven.

## 5. What was held, and why

- **Damage A, cell 3 on every passage** (64 a run, family `ℤ/4`): its antecedent side would be
  `1 → 3` and its consequent side `3 → 3 + δ`; both lie inside the opening (`3 + δ < 8` for
  `δ ∈ {2, 4}`), where the relation was never read. A cell the key's stations never join is held:
  the relation is applied only where it was observed.
- **Damage B on order-2 and the alternation, the whole chain `7, 9, …, 47`** (21 a passage): every
  cell's antecedent and consequent in the chain are themselves erased, and the chain's one link to
  an intact cell, `5 → 7`, lies in the opening. Both sides leave every family `ℤ/4` at every sweep:
  nothing is released and nothing guessed. The cells are not independent: the joint fibre is 4
  (one choice at cell 7 fixes the chain through the bijection `f`), so the residual is 2 bits, not
  `2·21 = 42`.
- **Damage B on the line, the chain `7, 11, …, 47`** (11 a passage), for the same reason; the other
  odd chain is released.

## 6. `n*_machine` against `n*_terrain`

In observations (intact stations; 25 a passage under A, 20 under B), `q` passages plus `j`:

| Terrain, damage | `n*_machine` | `n*_terrain`, the repair's grain (pinned) | `n*_terrain`, the syntactic class (amended) |
|---|---|---|---|
| order-2, A | 75 (3 + 0) | 47 (1 + 22): survivors `ℓ 2 [1 2 3 0]`, `ℓ 4 [2 3 0 1]` | 47 (1 + 22) |
| line, A | 74 (2 + 24) | not reached in 1,600 (weak aliases, §0 amendment) | 74 (2 + 24) |
| alternation, A | 203 (8 + 3) | not reached in 1,600 | 222 (8 + 22) |
| order-2, B | 40 (2 + 0) | 0 (degenerate: the key releases no cell) | 41 (2 + 1) |
| line, B | 161 (8 + 1) | not reached in 1,280 | 177 (8 + 17) |
| alternation, B | 81 (4 + 1) | 0 (degenerate) | 97 (4 + 17) |

- On order-2 under A the machine reads `75 − 47 = 28` observations more than the terrain: its
  menus reach every distance to `47`, past the reference's lags `[1, 40]`, and the distance 43
  (station 43 against cell 0, one edge a passage, a path that is no winding) stays alive until the
  third passage's last station gives it a second, conflicting edge (curve, observation 75). On the
  line under A the two counts coincide (74). On the other three nondegenerate readings the
  machine's pair holds before the reference's survivors stop changing (by 19, 1, 16 and 16
  observations): the reference keeps filling its aliases' maps after the generator is fixed.
- No passage alone locates its pair (0 of 64 on every run): within one passage some long distance
  reads one edge (a path, not a winding of the least survivor), which keeps the class plural. The
  read set's first passages remove it.
- `n*_terrain` here is not THE_TWO_COUNTS' `7` for order-2: there each observation read forty
  drawn request cells, which kill wrong lags at once; here most antecedents are themselves rule
  cells, which every winding of the generator also fits.

## 7. Time and memory

One thread a run (the harness is serial). Each run's projection is its largest development
service time over five measurements on `2_026_100_701` (`development/*_log.txt`,
`development/timing_remeasured.txt`), its deadline `5/4` of it under an outer `timeout`; the peak
resident set is the process's own (`VmHWM`, exact bytes), beside the systemd scope's reading in each
log.

| Run | Projection / deadline (ms) | Measured service time (ms) | Peak resident bytes |
|---|---|---|---|
| order-2, A | 46 / 58 | 44 | 10,207,232 |
| line, A | 46 / 58 | 44 | 10,280,960 |
| alternation, A | 63 / 79 | 57 | 10,448,896 |
| order-2, B | 1,467 / 1,834 | 1,418 | 10,461,184 |
| line, B | 50 / 63 | 44 | 10,436,608 |
| alternation, B | 4,712 / 5,890 | 4,553 | 10,444,800 |

Measured over projected, the six together: `6160/6384 = 385/399`, every run inside its projection.
The B runs' time is the read-only reference at the repair's grain (every lag's 256 completions on
every passage at zero observations, where the degenerate stopping object holds); the A runs,
location, restriction, codec and reference together, take 21 to 38 ms inside the process.

## 8. Owed in #62

1. **The restriction is the joint fibre's projection**: for binary relations on the edges of a
   forest, the fixed point of `F_t ← F_t ∩ R(F_(t−δ)) ∩ R⁻¹(F_(t+δ))` is, at every cell, the set of
   that cell's classes over the joint fibre, and some family empties exactly when the fibre is
   empty (arc consistency is global consistency on an acyclic constraint graph). The owner checks
   it exactly per passage and the brute-force test holds it on 400 drawn passages; the Lean
   statement is owed, as an instance of `Transport/ArtifactRelease.step` and
   `restriction_never_widens`.
2. **The repair codec is a Fold transition**: with `apply` the damage and `residual` the key and the
   patches, `reopen_apply` is `reopen(damage x, key, residual x) = x`; the residuals over one fibre
   are a prefix code, so the longest is at least `⌈log₂ N⌉` (`Transport/Fold.residual_injective_on_fibre`).
3. **The release at width zero** on a certified one-class family is `Foundation/ReceiverRelease.ReleaseLaw.sound`
   at tolerance zero (formal-checked); the join to the repair's class reading is owed.

## 9. Commits and gates

- `7109bc11`: the claim and the pins, before any read. `43788fb9`: the owners of §3, the harness,
  the development receipts and the pin's amendment, before the read. This record's commit: the
  read's receipts (`<terrain>_<damage>{_log.txt, .sections, .curve}`), §4–§9, the atlas row
  `compression.pair-repair`, the operator contract's `repair` (ELEMENTARY_OBJECTS, compression and
  landmarks) and the records README route.
- Gates: `cargo check --workspace --all-targets` clean (7,590 ms; the one pre-existing dead-code
  warning, `ReceivingPhases::with_rank`); `cargo test -p holonics --lib -- --test-threads=8`, 1,016 passed and 0 failed (299,313 ms wall with
  its build, projected at most 495 s from the 250–330 s read at 12 threads, deadline 900 s; the
  systemd scope's peak reads `2G`, rounded by its display); the guard lints (`cargo clippy -p
  holonics --lib -- -D clippy::disallowed_types -D clippy::disallowed_methods -D
  clippy::float_arithmetic`) report nothing in the changed files beyond `result_large_err`, which
  every `CompressionError` owner already carries. No Lean changed (§8 names the
  obligations); no card run (no kernel or card path changed).
