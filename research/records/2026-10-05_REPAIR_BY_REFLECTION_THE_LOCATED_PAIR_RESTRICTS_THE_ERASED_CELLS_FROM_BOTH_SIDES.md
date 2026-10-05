# Repair by reflection: the located pair restricts the erased cells from both sides

**Date.** October 5. **Issues.** #73, #148, #63, #62. **Lanes.** B and C of U6 (THE_REBUILD, "U6's
order from October 5", the paragraph "The task is repair, not continuation"). **Grade.**
[definition; agent-inferred] for the pins of §0, fixed and committed before any read.

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
