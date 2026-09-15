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

## Completed repeated generation

[established-bounded; measured] The same task now completes all **48 actual model targets**
and reopens the trained model. The [joint-current construction](../../records/2026-09-14_THE_JOINT_FIELD_CURRENT_SURVIVES_REPEATED_GENERATION.md)
repairs the separate-ball recombination in the consuming model. The inputs, target law,
grain 48 and D/M update law are unchanged. The former 39-target failure is retained below.

```sh
cargo run -p holonics-hna --example athena_field -- /absolute/output-directory 48
```

[established-bounded; measured] [Actual outputs](joint-48/return.json) and the
[81,449-byte trained model](joint-48/athena-field.rest) return:

| Material cut | Held-out squared centre error sum |
|---|---:|
| Before training | 267.358024691 |
| After 21 local examples | 198.224952123 |
| After 48 actual model targets | 3.496044848 |

[established-bounded; measured] This is a **98.692% reduction** on the four held-out inputs.
The largest final numerical/source enclosure radius is exactly `1717 / 281474976710656`
(about `6.10001e-12` in an exterior decimal presentation). This bounds arithmetic/source
uncertainty, not prediction accuracy. Reopen reproduces all four complete balls exactly.
The common current radius itself is about `5.83711e-12` after the 48th target.

| Condition | Target, interleaved real/imaginary | Generated complex centre |
|---|---|---|
| [3, 1] | [-1, 3, -3, -1, 2, 4] | -0.721605+3.467054i, -3.466419-0.906958i, 2.560095+4.188024i |
| [-2, 3] | [-3, -2, 2, -3, -5, 1] | -3.533524-1.740298i, 1.805106-3.538275i, -5.278573+1.728418i |
| [1, -3] | [3, 1, -1, 3, 4, -2] | 3.394002+0.780820i, -0.925225+3.274213i, 4.055034-2.468777i |
| [-3, -2] | [2, -3, 3, 2, -1, -5] | 1.799513-3.460473i, 3.346069+1.823372i, -1.637100-5.145582i |

[established-bounded; measured] The isolated warm debug process took **1.088606 seconds**,
with peak process RSS **291,096 KiB**. Inside it, setup took 231,830 microseconds, local
training 84,502 microseconds and 48-target training 582,245 microseconds, including data
mounting, preview/commit and observer checks. Native section accounting peaked at **195,156
bytes**, excluding the CUDA context/module. The serialized model-state rational readings
have maximum reduced numerator/denominator lengths of 106/97 bits; this is a measurement of
those readings, not the maximum intermediate arithmetic width. Full [process measurements](joint-48/process.json)
and the transfer census in the output retain their apparatus scope. First-load CUDA JIT is
excluded from this warm timing and included in the focused-test duration.

[established-bounded; measured] The [repeated one-pass control](joint-one-pass/return.json)
returns exactly the original twelve centres across before/local/target material cuts and
identical error sums. Its final maximum radius is about `1.09779e-12`; its saved model is
39,889 bytes and reopens exactly. The original saved model also remains a compatibility
fixture. The bounds were not reduced by changing the learned centres or discarding source
uncertainty.

## Original one-pass return

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

[historical] The separate outward/internal-ball join diagnosed in the failed run is now
replaced by the common-q affine/scattering action documented above. Fixed-condition contraction
and the cancellation in `b+(b_next-b)` remain in use. The earlier grain-72 trial's compatibility
packet aperture is a separate representation boundary; raising precision was not needed to
complete this 48-target task.

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

[established-bounded; measured] The joint-current increment passes
[five focused native checks](checks/joint-focused-native.txt), including nonzero common
uncertainty, rational conditions, current-only publication/material-only continuity, paired
pullback, corruption refusal and empty-history reopen. The
[expanded native regression suite](checks/joint-native-regressions.txt) passes 165 tests.
[established-bounded; measured] The [public HNN suite](checks/joint-public-hnn.txt) passes
12 tests, including a byte-for-byte legacy model fixture read whose inspected state matches
the originally delivered JSON. The separately preserved field-to-predictor assay remains
excluded at its recorded aperture failure; it is not this public field-model path.
