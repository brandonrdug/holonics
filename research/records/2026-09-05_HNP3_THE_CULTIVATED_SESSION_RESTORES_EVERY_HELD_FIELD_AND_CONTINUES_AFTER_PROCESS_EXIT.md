# HNP3: the cultivated session survives process exit and continues

**Date:** 2026-09-05 local. **Position:** HNP3 in progress; the checkpoint and public session
owners returned. The structured streaming CLI and its delivery controls remain next.

## Returned owners

[established-bounded; implemented-exact] `operative_rest.rs` and `operative_rest_wire.rs` return
the complete native session chart: operator/incidence metadata, actual U/V codewords and separate
dyadic exponents, current/checkpoint/terminal sections, generation and chronology, previous context,
apertures, pending local differences, numerical reuse and its origins, progress and interruption.
Arrays use a binary integer wire; metadata is an exterior codec and never an interior learning
mechanism. The base coefficients remain an explicit separate dependency.

[established-bounded; implemented-exact] `advance_cycle_retained` leaves the unique native owner
with its caller on both success and refusal. A preflight refusal does not mutate it. A later
failure records the actual installed/returned boundary, retains current and pending material,
and blocks silent replay. Terminal advancement now has the corresponding borrowed implementation.
Dissection apparatus and externally held withdrawal owners refuse checkpointing rather than being
silently discarded. An interrupted mathematical pole remains an obstruction after remount; this
does not claim an automatic repair or rollback of an undefined operation.

[established-bounded; implemented-exact] `holonics-hna::{publication,checkpoint,session}` exposes
`HnaModel`, `HnaSession`, declared occurrences, derived anatomy, `advance`, and `checkpoint`.
One callback retains the same mounted session across requests; it does not reopen a tokenizer or
remount per advance. The operation profile is explicit. The earlier batch/prefix API keeps its
old meaning and does not silently become the observed-passage session.

[definition] This first public session retains the admitted SKE family check. Native definability,
inherited fidelity and useful-task evaluation remain distinct domains. Broader application
admission and useful outputs are not inferred from a saved checkpoint.

## Publication and dependency contract

[established-bounded; implemented-exact] Checkpoints stream to a same-directory temporary file,
sync the file, publish by an atomic no-overwrite link, then sync the directory. Failed writers and
panic/unwind clean only their own temporary file. A destination race preserves the competing
file. Post-publication durability uncertainty is distinguished from failure before publication.
The writer borrows state; failed publication cannot consume the live model.

[definition] The checkpoint carries the base path, byte length, selected class and SHA-256 wire
pin. Base verification returns the same opened file descriptor, rewound for the native decoder.
The source is required to remain immutable while that descriptor is consumed. A verified path
override supports relocation. The checkpoint's own checksum is verified before state decoding.
These protect serialized bytes; neither a filename nor a digest is semantic model identity.
The artifact is dependency-bearing, **not self-contained** and not a standard executable export.

## Actual model and process-separated return

[established-bounded; measured] The actual native SKE body completed three observed-passage
developments and published `.local/artifacts/hnp3/checkpoint-01.hna`: 363,259,185 bytes,
generation 3,825 and factor extent 5,334. It retained nonempty terminal state and its ordinary
open boundary awaiting the next occurrence. A deliberately failed partial writer left the live
owner intact. The original process then advanced once more and saved
`.local/artifacts/hnp3/expected-after-01.hna` at generation 5,100 / factor extent 7,112.

```sh
target/debug/examples/checkpoint_hnp3 write target/ske4/rest.bin \
  .local/artifacts/hnp3/checkpoint-01.hna .local/artifacts/hnp3/expected-after-01.hna

target/debug/examples/checkpoint_hnp3 resume .local/artifacts/hnp3/checkpoint-01.hna \
  .local/artifacts/hnp3/expected-after-01.hna
```

[established-bounded; measured] The second command ran in a fresh process after the first exited.
Every held/rested field compared equal immediately after remount. After its next native
development, the **entire successor rest** compared equal to the reference, including actual
factor arrays, not merely ranks, checksums or selected output coordinates. The write/reference
process returned in 80,769 ms; verification/remount/continuation in 75,723 ms on the standing
RTX 4080 SUPER apparatus. These are one-run whole-process observations, including base I/O.

[established-bounded; measured] The public API was then exercised through `HnaModel` and its
continuing callback. Rejected out-of-family input preserved anatomy/ownership. Both re-saving
the unchanged model and advancing an admitted occurrence then checkpointing produced complete
rests equal to their native references. The resulting artifacts are
`.local/artifacts/hnp3/public-api-01.hna` and `public-api-after-01.hna`.

```sh
target/debug/examples/checkpoint_hnp3 api .local/artifacts/hnp3/checkpoint-01.hna \
  .local/artifacts/hnp3/public-api-after-01.hna .local/artifacts/hnp3/expected-after-01.hna
```

## Relevant controls

[established-bounded; measured] Five CPU wire tests passed: nonempty sections/factors,
pending/interrupted data, one-byte delivery, every prefix truncation, trailing/hostile lengths,
and malformed operator extents/ports. Artifact admission now refuses bad prefix/layer bounds
before slicing and checks the actual primitive port arities before unchecked parameter access.

[established-bounded; measured] A separate CUDA control used a native graph with a terminal
mathematical pole. Its earlier current and local return actually executed. The interrupted owner
retained nonempty carriers and pending morphology without publishing that delta. Wire round-trip
and native remount preserved the entire interrupted state; another advance refused without replay
or mutation. This is a failure-state control, not a learned-model capability fixture.

[established-bounded; measured] The HNA library's 25 tests passed, including publication failure,
panic cleanup, race/no-overwrite and post-publication uncertainty; missing/changed base bytes,
same-descriptor verification and checkpoint integrity/truncation. The HNA/workbench libraries,
binaries and examples type-checked. No Lean source was changed by this persistence work.

## Remaining HNP3 work

[open] Wire the continuing session into the structured streaming CLI; preserve partial input
and output delivery explicitly, exercise backpressure/interruption through that interface, and
document the operator recipes and restart boundaries. The current CLI remains the earlier
batch/prefix route. HNP3 is not closed by the checkpoint alone. HNP4--HNP7 still owe usable
multi-cycle applications, task evaluation, executable target compilation and SSM/diffusion returns.
