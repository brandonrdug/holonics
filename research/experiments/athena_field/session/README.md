# Contextual text through the constituted-field session

[established-bounded; measured] The existing field model now runs through the Workbench JSONL
session. It generates complete two-word sections, receives actual target text, learns its D/M,
and saves/reopens outstanding comparisons and undelivered output. This experiment uses three
word symbols (`red`, `blue`, `green`) and an ordered two-word correction context. The operator
and receiving construction are in the [source record](../../../records/2026-09-15_THE_FIELD_MODEL_GENERATES_CONTEXTUAL_TEXT_THROUGH_THE_PUBLIC_SESSION.md).

## Actual text returned

[definition] Context `[before, after]` supplies the observed correction pair. The target examples
replace that word in the complete request. `prepare.py` authors these supervised data openly;
the native session never invokes the target formula. Both output positions are generated in
one reaction/scattering operation and decoded together from one computed joint centre.
The words are unit-basis codec symbols; their ordinals are not amplitudes or native routing IDs.

[established-bounded; measured] After eight passes through 54 distinct development examples
and two additional resumed development comparisons, the 434-target model returns **27/27**
held-out recombination cases, including **6/6 actual edits**. Every diagonal request such as
`red red` is excluded from model updates. This population was used for validation during
iteration; it is not an untouched final benchmark. [All exact currents, bounds and responses](continued/evaluation-events.jsonl)
and the [readable results](results.json) retain that scope.

| Request | Context | Generated response |
|---|---|---|
| red red | red → blue | blue blue |
| red red | red → green | green green |
| red red | blue → green | red red |
| blue blue | blue → red | red red |
| blue blue | blue → green | green green |
| green green | green → red | red red |
| green green | green → blue | blue blue |

[established-bounded; measured] The first pass returned 21/27 overall but **0/6 edits**: it
mostly copied the input. That failure is retained in [the initial output](initial/evaluation-events.jsonl).
The later result follows additional updates from the unchanged development population.
The final largest output enclosure radius is exactly `19767/281474976710656` (about
`7.02265e-11` as an exterior decimal reading). That is arithmetic/source uncertainty; output
quality is measured separately against the supplied target text.

[established-bounded; measured] The same 27 cases also pass as a **committed continuing
sequence** with no material targets supplied, so the field's internal current advances between
responses. The subsequent endpoint preview reopens with exactly the same complete joint/boundary
currents, bounds, selections and text. [Continuing events](continued/committed-events.jsonl) and
[the reopened endpoint](continued/reopen-events.jsonl) retain the comparison.

## Use the actual application

[definition] Build the Workbench and open a fresh declared field, or reopen the
[trained session](continued/trained.session):

```sh
cargo build -p holonics-workbench
target/debug/holonics --format jsonl hna field-session \
  --resume research/experiments/athena_field/session/continued/trained.session \
  --input - --checkpoint /absolute/path/athena-next.session
```

Send one JSON object per line. The fields below are the real shared-stream API:

```json
{"schema":"org.holonics.hna.stream-request.v1","command":{"action":"field-request","request":{"text":"red red","context":["red","blue"],"commit":true,"retain_comparison":true}}}
```

[definition] The response contains generated text, the complete numerical section, receiver
margins and its comparison identifier. Send `observe-field` with that returned identifier,
actual target text and a declared `step_bits` (the experiment uses 1). `release-field-comparison`
explicitly releases an unused comparison. `checkpoint`, `inspect` and `close` use the existing
stream contracts. Checkpoint paths are published atomically without overwriting existing files.
A read-only request supplies `commit:false, retain_comparison:false`.

[definition] `spec.json` declares the alphabet, whole-section extent, context extent, text codec
and grain. It contains no learned answer map. `--source spec.json` creates a fresh field;
`--resume` restores model, codec, comparisons and stream delivery state. The exposure bridge
`FieldSectionRequest::from_exposures` accepts validated visible parts and their explicit prior
parent chain. Source metadata remains exterior; no private conversation was used as gold data
in this published control task.

## Continuation and cost

[established-bounded; measured] Both application runs stopped with a real outstanding response.
A subsequent process consumed its target and saved the updated model. A separate native test
kept two pending responses, updated material through the first, saved, and then applied the
second response's target after reopening. Its field/material state and covector agree exactly
with uninterrupted execution. Another test disconnects the output writer after committed
generation, reopens and drains the same response without repeating the model operation.

[established-bounded; measured] The warm continuation performs 378 actual target updates in
85.691964 seconds including remount, request/response I/O and checkpoint. Its generation median
is 23,174 microseconds (95th percentile 24,918); target-update median is 188,562.5 microseconds
(95th percentile 202,384). These in-process clocks exclude JSONL emission after the operation;
full process time includes it. Peak process RSS is 319,676 KiB. Native section accounting peaks
at 8,311,812 bytes in that continuation, excluding the CUDA context/module. The initial process
took 204.719363 seconds including first-load CUDA compilation. [Process records](continued/process.json)
and the full event measurements are preserved; no power claim is made.

[established-bounded; measured] The saved pending session is 3,824,325 bytes and the resolved
trained session is 2,315,343 bytes. The current dense normal state and operative journal remain
visible costs. This return does not claim economical training of arbitrary-length conversations.
The exact declared context tensor has alphabet-size-to-context-length growth, and the current
section extent is fixed by its source chart. Those are concrete representation/consumer limits
for the next application increment, not reasons to replay this small task or add a new
intelligence/theorem gate.

## Verification

[established-bounded; measured] [168 native regressions](checks/native-regressions.txt),
[16 public/session tests](checks/public-session.txt) and [eight CLI tests](checks/cli.txt) pass.
The [focused native receiving tests](checks/native-receivers.txt) check common-source
identity/reaction cancellation, simultaneous selection from a complex joint ball, nonzero
radius, permutation and ties. Legacy model compatibility remains covered. The separately
preserved old field-to-wave surrogate assay remains outside this field application.
