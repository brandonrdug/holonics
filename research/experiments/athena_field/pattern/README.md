# Partial patterns through the same Athena field session

[established-bounded; measured] The field application now receives partially observed regions,
forms their missing values jointly, and keeps supplied observations fixed at its receiving face.
It returned **45/45 missing values across 39 complete responses**, while preserving **63/63
supplied values**. The same 39 responses passed with each field update committed. This is an
explicit three-symbol pattern-learning population, not a conversation benchmark.
[Exact outputs and measurements](results.json); [mathematical/source record](../../../records/2026-09-15_PARTIAL_FIELDS_FORM_JOINT_PATTERNS_THROUGH_THEIR_RECEIVERS.md).

## Returned patterns

[definition] The exterior development data show complete patterns `[a,b,a]`, with `b` present
in the neighboring context region. Four partial views expose one or two of the pattern's
regions. The native model receives those source currents, activity/observation maps and later
complete targets; it does not execute the target formula in [prepare.py](prepare.py).
Development uses the six pairs with `a != b`, four views each, four passes, plus one resumed
comparison: **24 distinct examples and 97 supplied targets**. The evaluation population was
specified before execution and was not used for parameter updates or a tuning loop.

| Evaluation | Complete responses | Missing values generated | Supplied values retained |
|---|---:|---:|---:|
| Withheld equal-color pairs | 12/12 | 18/18 | 18/18 |
| Independently supplied outer regions | 18/18 | 18/18 | 36/36 |
| Shorter requested output | 9/9 | 9/9 | 9/9 |

[established-bounded; measured] For example, `[red, ?, green]` beside context `[blue]` returns
`red blue green`, although the training patterns have equal outer regions. The supplied
`green` remains a receiving constraint; the middle `blue` is generated. `[?, ?, red]` beside
`[red]` returns `red red red`, generating two missing regions. A two-region request `[green, ?]`
beside `[blue]` returns `green blue`. These are joint section responses, with no next-token loop.

## Use the application

[definition] Open the [trained session](run/trained.session) with the existing Workbench:

```sh
cargo build -p holonics-workbench
target/debug/holonics --format jsonl hna field-session \
  --resume research/experiments/athena_field/pattern/run/trained.session \
  --input - --checkpoint /absolute/path/athena-next.session
```

The actual JSONL request for the first example is:

```json
{"schema":"org.holonics.hna.stream-request.v1","command":{"action":"field-request","request":{"partial":["red",null,"green"],"context":["blue"],"commit":true,"retain_comparison":true}}}
```

[definition] A non-null `partial` region supplies one symbol and holds its coordinates at the
receiver. `null` denotes an active unobserved region with the declared zero latent seed; it does
not assert that the source value is zero. `output_symbols` selects a positive receiving extent
within the saved section capacity, including regions beyond the supplied prefix. Ordinary `text`
requests remain mutable source sections. Context symbols occupy their own incoming regions.
The source spec explicitly selects `"source_chart":"joint-regions"`; omitted source-chart fields
retain the earlier tensor-condition behavior. The saved example has capacity three output
regions, one context region and the alphabet `red`, `blue`, `green`.

[definition] `observe-field` consumes the returned comparison ID and complete target text for
that response's extent. The producing D/M, input, receiver, mask and extent survive subsequent
updates and restart. A contradictory target on fixed coordinates reports its difference; it
cannot change those coordinates through D/M. Raw field output and `received_boundary` are both
returned. Committing advances the raw field; it does not clamp the internal field to the visible
observations. The affine receiver is `y=P given+(I-P)w`.

[definition] Reproduction inputs are [development](development.jsonl), [evaluation](evaluation.jsonl),
[committed evaluation](continuing-evaluation.jsonl) and [endpoint probe](reopen-probe.jsonl).
The recorded process commands in `run/*-process.json` use those files and preserve the real
pending-session boundary. `python3 research/experiments/athena_field/pattern/analyze.py` checks
all stored outputs, separates inferred from supplied coordinates, and verifies exact endpoint
reopening. It does not train a model or supply a native answer.

## Continuation, costs and limits

[established-bounded; measured] The development process stopped with comparison 96 outstanding.
The next process applied its target using the saved producing receiver/material. After the
39 committed evaluation responses, reopening reproduced the endpoint's complete raw/received
currents, bounds, selections and text exactly. The earlier version-1 text checkpoint also
opens and returns its expected `blue blue` edit. [Continuation](run/continuing-events.jsonl),
[reopen](run/reopen-events.jsonl), [legacy compatibility](checks/legacy-result.json).

[established-bounded; measured] The warm debug development process performs 96 targets in
71.768705 seconds, including creation, I/O and pending checkpoint. Generation median is
77,522 microseconds, p95 83,797; target-update median is 641,746.5 microseconds, p95 691,918.
These in-process clocks exclude subsequent JSONL emission. Peak process RSS is 303,872 KiB;
native section accounting peaks at 26,447,972 bytes, excluding CUDA context/module residency.
The resumed evaluation process peaks at 37,028,676 native section bytes while restoring the
producing witness. Pending/trained sessions occupy 11,470,459 / 6,170,290 bytes. The continuing
39-response process takes 6.042063 seconds; endpoint reopening takes 2.614911 seconds.
The largest preview receiving radius is exactly `11749/281474976710656`; enclosure width and
pattern correctness are different measurements. All times and medians are exterior observations.

[established-bounded; source-inspected] The region chart uses 12 incoming complex coordinates,
9 condition coordinates and 129 reaction features. Context currents participate in the actual
incoming field. Activity and observation flags condition its reaction. This replaces categorical
context enumeration for this explicit source chart; it is not an equivalent compression of
every legacy tensor-conditioned model. Dense normal statistics and fixed incidence remain
real costs. At fixed masks and D/M, this single reaction/scattering step is affine in its input.
It supplies useful joint pattern completion here; general content-dependent iterative refinement,
learned geometry and conversation/code competence are not established by these examples.

[established-bounded; measured] The first cold attempt failed during allocator calibration after
CUDA compilation, before any model request. [The failure](setup-obstruction/) is retained.
The mount now retries only an unstable allocation-grain calibration, at most three attempts,
and still requires the original allocation/composition checks. Driver allocation errors and
persistent instability return their failures. Warm execution succeeded; this does not establish
that every future cold-start disturbance is resolved.

## Verification

[established-bounded; measured] [171 native regressions](checks/native-regressions.txt),
[20 public/session regressions](checks/public-session.txt) and
[two calibration tests](checks/allocation-calibration.txt) pass. Native checks cover positive
radius, aliasing, mask/rest compatibility and the masked output covector against the exact
paired adjoint, including nonzero interior contributions. Public checks cover delayed producing
D/M, variable target lengths, and a fully held contradictory target that leaves D/M unchanged.
The existing unrelated field-to-wave surrogate assay remains separately preserved and excluded.
No Lean or Typst source changed in this increment.
