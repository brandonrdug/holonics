# One trainable constituted-field HNN

[established-bounded; measured] The public body directly owns its constituted field and local
reaction, generates a complete joint section, and incorporates actual output targets through
the producing D/M. The input task is the joint quarter-turn of three complex coordinates.
The source/target formulas, eight training conditions and four held-out conditions are fixed
in [the public example](../../../crates/holonics-hna/examples/athena_field.rs).
The [construction record](../../records/2026-09-14_THE_CONSTITUTED_FIELD_TRAINS_AND_REOPENS_AS_ONE_HNN_MODEL.md)
gives the operation, applied/reference distinction and actual update law.

```sh
cargo run -p holonics-hna --example athena_field -- /absolute/output-directory
```

[definition] The default is one pass through eight actual model targets, preceded by 21 local
reaction examples. The examples supply data; the normal learner, conditional action, field
scattering and adjoint/material response execute through the library. Training does not see
the four held-out condition pairs. Incidence and point-condition ports are explicitly supplied.
There is no coordinate/token prediction loop and no Lean call in the model.

## Actual return

[established-bounded; measured] On the same four held-out inputs, the sum of exact squared
centre differences is shown below as a compact decimal observer presentation. Full exact
rational centres and enclosure radii are in [return.json](one-pass/return.json).

| Material cut | Squared error sum |
|---|---:|
| Before training | 267.358024691 |
| After 21 local examples | 198.224952123 |
| After eight actual model targets | 26.378035151 |

[established-bounded; measured] This is a 90.134% reduction on this task. The largest
final output radius is 2.82664878171e-08.
The learned outputs are approximate; the task has not reached exact quarter-turn reconstruction.
These held-out outputs are actual model returns (target columns use interleaved real/imaginary
integers; generated columns show complex centres):

| Condition | Target | Generated centre |
|---|---|---|
| [3, 1] | [-1, 3, -3, -1, 2, 4] | -1.418994+2.338239i, -3.227411+0.865259i, 3.203497+4.646405i |
| [-2, 3] | [-3, -2, 2, -3, -5, 1] | -4.393769-1.823759i, 1.900798-2.796516i, -4.620275+2.492970i |
| [1, -3] | [3, 1, -1, 3, 4, -2] | 1.820261-0.410678i, 0.156693+4.856758i, 4.446080-1.976954i |
| [-3, -2] | [2, -3, 3, 2, -1, -5] | -0.005913-3.875791i, 4.425863+2.609364i, -1.266427-4.419949i |

[established-bounded; measured] Preview and commit agree for each generated training section;
one target handle cannot be applied twice. [athena-field.rest](one-pass/athena-field.rest)
contains 39712 bytes. The example drops the live model, reads these serialized bytes,
remounts and returns exactly the same four held-out balls. It checkpoints resolved comparisons;
pending target persistence is not yet part of this field-body codec.

## Cost and representation

[established-bounded; measured] This debug-build return on the Ryzen 9 7900X / RTX 4080 SUPER
uses 236399 microseconds for process/surface/model setup,
79081 microseconds for the 21 local examples, and
80190 microseconds for the eight model targets including mounted data,
preview/commit comparisons and observer inspection. Held-out preview times are recorded
individually in the JSON. These are workload measurements, not power claims.

[established-bounded; measured] Native section accounting reports a peak of
146516 bytes, excluding CUDA context/module allocations.
The complete surface transfer census includes exterior data mounting, verification and rest;
it is not a claim of zero delivery/readout traffic. Arithmetic uses grain 48 and exact wide/
moment carriers. Native tests separately check no numerical host readout during forecast,
conditional contraction and current publication.

## Longer-run failure retained

[established-bounded; measured] An additional 48-target run completed 39 targets, then refused
the next adjoint with a carrier overflow. Its [full failure and producing output](longer-run/training-obstruction.json)
and [isolated process measurement](longer-run/process.json) are retained. This is an incomplete
longer run, not a pass. The first attempted concurrent run hit the apparatus allocation-grain
measurement while another CUDA test was allocating; the isolated rerun above establishes the
actual model failure.

[definition] The corrected conditional contraction is `r=A(h)s+c(h)`: fixed h does not become
an independently uncertain feature. Current publication also retains the cancellation in
`b+(b_next−b)`. The remaining repeated enclosure expansion occurs across the separately restricted
outward/internal balls and their recombination. The next concrete composition is the common
joint source under `S_D diag(A(h),I)` with its affine offset, retaining its joint bound/fibre
through public generation and rest. Increasing a universal training counter or dropping radii
would not repair that relation. A trial at grain 72 also exposed the existing compatibility
graph's 64-bit rational-packet aperture; this is a separate representation boundary.

[project-postulate] The return establishes the first trainable model operation at this declared
scope. Receiver-relative contextual tasks, economical repeated execution, pending continuation
and Athena text/code applications continue under the roadmap. No additional definition-of-
intelligence or global-convergence test is introduced.


## Verification

[established-bounded; measured] [Focused native checks](checks/focused-native.txt) pass five
tests; [normal/source/rest regressions](checks/normal-source-rest.txt) pass 144 tests.
The [direct-condition rest regression](checks/direct-condition-rest.txt) additionally checks
serialization after an explicitly received condition with no invented preimage evidence.
The two enclosure-sum cases occur in both the focused and wider suite.
The earlier uncommitted surrogate assay's [failure](checks/preserved-surrogate-failure.txt)
is retained separately and is not counted as a pass or an acceptance condition for this model.

[established-bounded; measured] The [existing public HNN suite](checks/public-hnn.txt) passes
11 tests on the final shared owners. The excluded pre-existing assay's
[source snapshot](checks/preserved-surrogate-source.rs.txt) remains research evidence, with its
remounted word-aperture refusal recorded above; it is not part of the committed acceptance suite.
