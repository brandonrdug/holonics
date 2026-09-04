# SKE2: the cone is founded by joint withdrawal along the excitation, and a per-population support is not a cone

**Date:** 2026-09-03  
**Truth status:** `established-bounded`  
**Evidence:** `implemented-exact`, `source-inspected`, `measured`  
**Campaign:** SKE2 under
[`THE_SOULKILLER_EXCITES_THE_RESIDENT_REALIZATION_AND_RETURNS_THE_RECEIVER_FAMILY_QUOTIENT_AS_CONE_RESTRICTED_ECOLOGIES.md`](../../archive/plans/THE_SOULKILLER_EXCITES_THE_RESIDENT_REALIZATION_AND_RETURNS_THE_RECEIVER_FAMILY_QUOTIENT_AS_CONE_RESTRICTED_ECOLOGIES.md).  
**Receipts:** [`2026-09-03_SKE2_receipts/`](2026-09-03_SKE2_receipts), one exact receipt per
occurrence with every population's cone as a site bitmask.

## The correction

[counterexample; measured] The blueprint's first letter for SKE2 read the cone at a population as
the SKE1 support at that population, verified by withdrawing that population alone. On the
resident operator this is refuted twice. The sealed differential is nonzero at 1,595,187 of the
1,595,392 output sites of the 344 contraction populations for the plain occurrence `7 + 5 =`, so
the "support" is the operator; and withdrawing the whole support of any one population left the
face unchanged for all 54 populations tried (six layers of attention, feed-forward, and per-layer
projections, and the prologue projection). The load is joint: no single population carries the
face, and `IsCone` in `HolonicExcitationFoundedQuotient.lean` is a law over withdrawals of any
population of the ecology's sites, not of one population's sites. The phase is re-founded on the
joint intervention below; the blueprint is corrected in place and this record is the receipt.

## The instrument

[implemented-exact; source-inspected] Sites are the output coordinates of every contraction
population (one row of the cross-section, read at every position): 1,595,392 across the 343
body populations and the tied boundary. A withdrawal zeroes a declared site population at each
contraction's output at every position (`section_withdraw_sites`, a resident mask read through an
offset so the sixteen tiles of the tied boundary read one mask), and the cycle is enacted again
from the earliest touched segment on the retained cross-layer checkpoints through the terminal
boundary; the session's own carriers, checkpoints, and face are untouched
(`operative_intervention.rs::face_under_withdrawals`). A null withdrawal reproduces the emitted
face and the exact terminal row on every occurrence (the replay control), which required the
replay to apply the forward's own successor projection; the SKE1 replay did not, and is corrected.

[implemented-exact] The receiver is the selected face at the terminal position under the
application's own rule (greatest midpoint, first of equals); the engine's reading and the
application's rendering agreed on every occurrence. The excitation is the differential of that
face's own normalized-exponential probability at the last row (`p − [o = selected]`, every earlier
row withdrawn), returned through every reaction by the SKE1 instrument in the dissection deed,
which deposits nothing and reads, at every contraction's output, the support, the greatest
|midpoint| of the forward's own output (the magnitude), and the first-order contribution
`|Σ_positions d · y|` of withdrawing each site.

[implemented-exact] The cone is founded by intervention along that order: every site of every
population is sorted by contribution, and a bisection over the prefix withdrawn jointly finds the
largest prefix whose withdrawal leaves the selected face unchanged. That prefix is the complement;
the suffix is the cone. Every exclusion from the cone is a withdrawal the card returned unchanged,
and the ordering decides only what is tried. Two controls close it: the complement withdrawn as
one population leaves the face; the cone withdrawn as one population changes it. The boundary
site, the last the order admitted, is withdrawn alone as the load-bearing control. The cone is
reported restricted to every population with its exact sites, and a magnitude control exhibits,
per population, the least number of sites any threshold on the forward's output magnitude
misclassifies against the cone.

## The declared family

[definition] Five variants of one algebraic problem, single-digit addition, each entering as one
addressed occurrence through the application's own turn markers (`<bos><|turn>user\n{problem}<turn|>\n<|turn>model\n`,
fourteen addresses) so the receiver is the first face of the answer. No answer is named. The
face the operator emitted on every occurrence is the first digit of the problem restated.

## The deed

[established-bounded; implemented-exact; measured]
`applications/athena-alpha/examples/cone_by_intervention_ske2.rs`, one bounded process per
occurrence (73 to 79 s, of which about 45 s is the cone search of 22 probes and 3 controls, each a
counterfactual forward of 1.2 to 2 s):

| occurrence | face | cone (sites) | complement withdrawn | cone withdrawn | probes | boundary site (alone) |
|---|---|---|---|---|---|---|
| `7 + 5 =` | `7` | 29,588 (1.85 %) | unchanged | changed, ` important` | 22, monotone | layer 20 down-projection #1368, unchanged |
| `9 + 3 =` | `9` | 71,755 (4.50 %) | unchanged | changed, `une` | 22, monotone | layer 12 per-layer projection #155, unchanged |
| `7 + 6 =` | `7` | 1,310,213 (82.12 %) | unchanged | changed, ` 就是` | 22, monotone | layer 15 gate-projection #10174, unchanged |
| `3 + 4 =` | `3` | 345,940 (21.68 %) | unchanged | changed, ` किसके` | 22, monotone | prologue projection #720, unchanged |
| `8 + 8 =` | `8` | 181,063 (11.35 %) | unchanged | changed, `ễ` | 22, monotone | layer 0 down-projection #1104, unchanged |

Every replay control returned the face and the exact row unchanged. Every complement withdrawal
left the selected face and changed the exact row: the exact terminal emission is not carried by
any proper sub-population, which is why the declared receiver is the face. The magnitude control
fails on the cone almost everywhere: on `7 + 5 =` a threshold on the forward's own output
magnitude determines the restriction in 40 of 344 populations, and where the cone is largest
(layers 19 through 22 feed-forward down-projections, 542 to 865 of 2,560 sites each) the least
misclassification of any threshold is 542 to 854 sites; on `3 + 4 =` it determines the
restriction in 4 populations. Two occurrences with the same face, `7 + 5 =` and `7 + 6 =`, have
cones of 29,588 and 1,310,213 sites: the live analogue of the SKE0 control, equal faces and
different cones.

[measured] The cone concentrates: on `7 + 5 =`, 316 of 344 populations carry cone sites, and the
sites lie mostly in the feed-forward projections of layers 15 through 29 (layer 21 alone carries
2,527), with 27 to 80 sites in each of layers 0 through 8.

[counterexample; measured] The blueprint's first letter, kept as `cone_controls` and run on the
first four populations of every occurrence: withdrawing a whole population's support alone
changed the face on the prologue projection for four occurrences and on layer 0's value
projection for all five, but not on layer 0's query or key projections for four of the five. A
per-population support is neither necessary nor sufficient for the face; it is not a cone.

## Verification

[process-audit; measured] Focused card tests: the site withdrawal is exact out of place and reads
a tile's span through an offset; the face rule, the site reading (support, magnitude, first-order
contribution), the magnitude sweep, and the selection's offsets each have a host test. The
session file was split (`operative_terminal.rs`, `operative_scalars.rs`) and returns under the
source-shape limit at 1,411 lines; the gate is red only on `embedding_fiber.rs` as before.
Workspace type-check of every target passed; the engine library returned 2,025 passed, 0 failed,
32 ignored in 82 s; the SKE1 return deed still crosses all 1,271 operations (2.5 s, 343 deposits,
second face ` the`; its second emission digest is now `8cbbcd7875106aad` rather than
`d29765f20de93dad`, because the replay now applies the forward's own successor projection); the
HNA5 three-application matrix returned the same three faces with every release receiver true.
The five receipts were produced twice, before and after a machine restart, on the same binary:
every cone population, boundary site, and probe verdict reproduced exactly.

## Grade

[established-bounded] **SKE2 PASSED at its corrected scope.** For every occurrence of the declared
family both withdrawal controls returned on the card with the verdicts the law requires; a
magnitude ranking is exhibited that does not determine the cone; the cones are reported per
population with their exact supports in the receipts.

[counterexample; source-inspected] What this does not claim: `IsCone` quantifies over every
population disjoint from the cone, and the card verified the complement as one population and the
probed prefixes along one ordering, not every sub-population; the cone is minimal along the
contribution order, not the least cone; the sites are contraction outputs, so normalization
gains, layer scalars, and embedding rows are outside the intervention; the receiver is one face
under the empty history, and no signature over declared histories has been formed (SKE3); no
capability claim follows from the faces, which restate the problem rather than answer it.
