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
