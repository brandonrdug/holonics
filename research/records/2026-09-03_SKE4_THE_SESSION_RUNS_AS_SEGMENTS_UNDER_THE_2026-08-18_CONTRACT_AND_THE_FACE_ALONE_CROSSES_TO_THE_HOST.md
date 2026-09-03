# SKE4, the apparatus obligation: the session runs as segments under the 2026-08-18 contract and the face alone crosses to the host

**Date:** 2026-09-03
**Owner:** `crates/holonic-engine/src/holonic_intelligence/operative_segment.rs`,
`full_operation.rs`, `operative_terminal.rs`, `operative_backward.rs` (the replay),
`operative_intervention.rs` (the face under withdrawal), `operative_residence.rs` (the slot
guard); the deed `applications/athena-alpha/examples/session_census_ske4.rs`.
**Receipts:** `2026-09-03_SKE4_receipts/`.
**Grade:** established-bounded; implemented-exact; measured. This record grades the apparatus
obligation of SKE4 (blueprint §0b and the SKE4 section: the session under the 2026-08-18 contract
as written). It founds no cone, condenses no class, and claims nothing about compression.

## 1. What was measured

One cycle of the resident operator on `7 + 5 =` (14 addresses, 1,275 operations), before and
after the refit, read from the surface's transfer census.

| | per-operation session (baseline) | segment session |
|---|---|---|
| deed launches | 2,363 | 687 |
| synchronizations | 2,363 | 687 |
| section read-outs | 2,363 | 16 |
| section egress | about 2.06 GB | 58,720,256 octets |
| allocations | 9,450 | 4,075 |
| passages (distinct census readings) | 2,363 | 672 |
| cycle | 1,915 ms | 1,412 ms |
| face | `7` | `7` |

The 16 read-outs are the 16 tiles of the terminal face, read once at the declared receiver;
their egress is 14 rows by 262,144 columns by 16 octets. Nothing else crossed. The
`section_read_outs` and `egress_section_octets` of the segment session are zero inside the
body.

[measured] Regressions on the same session: the HNA5 application matrix returned ` Explain`,
` i`, and ` :=` at generation 3,825 (`hna5_application_matrix_segments.json`); the SKE2 cone deed
for occurrence 0 returned the face 236832 (`7`), the cone of 29,588 sites in 1,595,392, the same
22 probes with the same verdicts, 344 populations read, and 43 layers replayed
(`ske2_occurrence_0_segments.json`); the excitation took 3,480 ms against 3,826 ms before.

[measured] Every one of the 1,270 body operations, enacted as a one-operation segment, agrees
exactly (every lower and upper word, every width) with the committed per-operation session
(`per_operation_agreement_with_the_committed_session.json`).

[measured; open] The SKE2 receipt's `face_digest` (a digest over the exact face intervals)
differs from the recorded one (`0f283aeb9a070d8d` against `ecbab1f5f902b9dd`) while the
selected face, its equal population, and every cone reading agree. Inside a multi-operation
segment a consumer is admitted under the a-priori bound of its producer rather than the measured
one, and the enclosures a law returns under a wider admission were not compared word for word
against the committed session at the multi-operation grain. Which law's enclosure differs, and by
how much beyond the observed agreement of the selected face, is not established here.

## 2. What the session now is

[definition] A segment is a run of the ecology's operations sharing at most one use of the single
alignment slot (a contraction's tile, a rebase's gain, a coefficient scale) or one gather (a
lookup). Each segment is one passage: every output section is founded before the capture opens;
every operation is admitted under an a-priori octave bound derived from its inputs' bounds and
its law; the successor projection is a midpoint seal fused into the graph after every operation
whose output can leave the grain (contraction, rebase, GELU, tanh, chronology, contact, both
scales, the product); the graph is launched once and its census read once; the census is the
measured bound of every carrier the segment leaves resident and the projection testimony of
every operation. The terminal is enacted tile by tile, each tile the five terminal operations
in one passage, and only the tiles a successor needs are retained (the emission; the reacted
carrier and the presented carrier when a return or a dissection is declared; the tied
contraction's last row under dissection).

[definition] The a-priori bounds are the laws' own (`resident_law.rs`), with one bound stated
here for the segment: every carrier a segment consumes is a point section, because the fused
seal projects every widening operation's enclosure to its midpoint and the exact operations
(lookup, carry, select, sum) preserve points; on a point section the rebase is bounded by
`sqrt(group)·|g|` since `mean(x²) ≥ x_i²/group`, so the enclosure bound `|x|/sqrt(eps)` of the
law never governs a segment. When an operation's carrier obligation exceeds what the a-priori
bounds admit (the GELU's and tanh's obligations are quadratic in their input's octaves), the
segment closes before it and it is enacted at the head of the next passage on the measured
bounds. That rule, not a fixed schedule, is why the cycle is 672 passages rather than the
roughly 500 the slot rule alone would give.

## 3. What the differential found

[counterexample; measured] The first segment session returned the face `总` for `7 + 5 =`. A
per-operation differential against the committed session located two defects, neither of them
in a law:

1. inside a contraction's segment, a rebase without a gain read the segment's aligned tile as its
   gain (`operative_segment.rs`, the recording of `Material::Rms`): the first divergence was at
   operation 20, the value-norm of the first layer, whose input agreed word for word;
2. the product and the coefficient scale round to the grain and were not sealed, so their
   consumers read one-grain enclosures rather than the committed session's sealed points: the
   first divergence in one-operation segments was at operation 30.

With both corrected the 1,270 body operations agree exactly and the face is `7`.

[counterexample; measured] The first terminal retained all five tiled carriers of every tile
and exhausted the card on 27 rows (`CUDA_ERROR_OUT_OF_MEMORY` at 15.98 GB resident) where the
committed session had not; retaining only what a successor needs returned the 27-row cycle in
2,155 ms.

## 4. What departs and what this does not grade

[definition] `enact_operation`, `project_successor`, `execute_*`, `OperationOutcome`, the
per-operation passages, and the per-operation read-out of every carrier depart from the session.
`advance` remains as a one-operation segment that reads no section; `carrier_intervals` remains
as the declared receiver's copy. The diagnostic read-outs used by the differential were removed
before this record was taken.

[counterexample; source-inspected] The coordinate-grain SKE4 owners
(`operative_condensation.rs`, `operative_extent.rs`, the example `condensation_seal_ske4.rs`) are
withdrawn from the registered tree under §0b; they are kept out of the tree as material for the
re-founded deed and grade nothing.

[counterexample; measured] Process bounds: every deed above ran under 180 s (the longest, the
SKE2 excitation and cone, 44.1 s; the 27-row cycle, 2.2 s). The release build of the
application examples took 3 m 14 s to 3 m 36 s under `MemoryMax=16G` and `-j 6`, above the
contract's 180 s outer limit; the library test build took 1 m 06 s and the tests ran in 82 s
(2,034 passed). One ignored card test, `cuda_refine::tests::factored_moment::
quadratic_moment_front_equals_the_enumerated_boundary_law`, fails (25 launches against 19) on a
path this work did not touch (`git diff HEAD -- crates/holonic-engine/src/cuda_refine
crates/holonic-engine/kernels crates/holonic-engine/build.rs` is empty); it was red at the
branch point 9bba7a9e as well.

This record does not grade compression, condensation, a cone, or a class. It grades the session
as the apparatus the rest of SKE4 runs on.
