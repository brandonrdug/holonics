# The shared-regions field session runs on complete sources

[established-bounded; measured] The shared-regions chart arrived with prepared inputs and no
executed run. It now has one. A bounded prefix of the [prepared source-reconstruction
material](prepare.py) went through the public Workbench field session: three complete source
observations, then two withheld complete sources generated in one joint section each. The model
**preserved 83,470/83,470 supplied byte positions** and returned **1,096/6,955 withheld bytes**
(**5,705/13,910 withheld nibbles**) at its declared receiving extent. That is above a content-free
rule and far below source reconstruction; the exact counts and both exterior comparators are in
[results.json](results.json). The prepared material is private, so this experiment reports
counts, extents, timings and symbol agreement only; no source or generated text is reproduced.

## What was declared before execution

[definition] `prepare.py` fixes the population at repository revision `19964c20`: three public
documents supply development, one further public document and one prepared private conversation
episode supply validation. Its masks depend on source byte addresses (`i % 13 == phase`), never
on a desired symbol, and it writes no answer map. The declared section capacity is 153,418
nibbles — the largest prepared source — with offsets `[-2,-1,0,1,2]`, sixteen nibble symbols and
grain 48. The caller declares the executed prefix; this run declared **3 of 9** prepared
observations (one epoch over the three development sources, 107,672 bytes, 16,560 free rows) and
**2 of 2** validation requests. The remaining six observations are two further epochs of the same
three sources and were not executed here.

[established-bounded; source-inspected] The model does not grow with that capacity. The local
incidence chart gives 30 field nodes, a 90-coordinate incoming width, one condition coordinate
and 181 reaction features, whatever the source length. One row is prepared per free receiving
position from the declared offsets alone; `D` is fixed and `M` receives every row's contribution
in one update. The [coefficient-shape test](../../../../crates/holonics-hna/src/native/field_session/shared.rs)
holds this independence against a million-symbol declared aperture.

## Measured return

| Measurement | Development process | Validation process |
|---|---:|---:|
| Requests executed | 3 source observations | 2 complete-source requests |
| Free rows | 8,926 / 4,116 / 3,518 | 2,110 / 11,800 |
| In-process median | 196,437,812 µs update | 110,097,454 µs generation |
| In-process p95 | 496,300,609 µs update | 185,913,939 µs generation |
| Process wall | 875.697068913 s | 273.310645830 s |
| Peak process RSS | 375,460 KiB | 856,304 KiB |
| Peak native section octets | 1,222,159,508 | 1,335,639,540 |
| Resident native section octets at rest | 40,355,248 | 40,885,424 |
| Published session | 18,102,949 bytes | 18,102,949 bytes |

[established-bounded; measured] The validation process **resumed the development process's
checkpoint**, so these are two separate processes over one saved model, not one long run. The
session size is a property of the chart, not of the source length: both checkpoints are the same
18,102,949 bytes after a 107,672-byte development pass and after two requests of 13,716 and
76,709 bytes. In-process clocks exclude JSONL emission; wall and RSS are exterior observations of
a debug binary with a warm CUDA cache.

| Withheld source | Bytes | Withheld | Returned correct | Nibbles correct | Supplied preserved | Decodes as UTF-8 |
|---|---:|---:|---:|---:|---:|:--:|
| `docs/CONSTRAINT_MODES_AND_RECEIVER_FACES.md` | 13,716 | 1,055 | 147 | 814/2,110 | 12,661/12,661 | no |
| prepared private conversation/repository episode | 76,709 | 5,900 | 949 | 4,891/11,800 | 70,809/70,809 | no |

[established-bounded; measured] Both requests returned exactly their source extent — 27,432 and
153,418 symbols — with every supplied position preserved and only the withheld positions
generated. Neither output decoded as UTF-8: a wrong nibble can break a multi-byte sequence, and
`decode_error` reports that without discarding the bytes. The largest receiving radii are exactly
`123973745/70368744177664` and `1386618765/140737488355328`; those bound arithmetic and source
uncertainty, not correctness.

[established-bounded; measured] Two exterior comparators over the **same** withheld positions,
computed from the supplied material alone, bound what a content-free rule returns: always
answering the most frequent supplied byte gives 130/1,055 and 700/5,900; copying the preceding
byte gives 15/1,055 and 94/5,900. The model returned 147 and 949. At the nibble level it returned
38.6% and 41.4% against a sixteen-symbol chart. The margin over a constant-byte rule is real and
small. This is a source-reconstruction measurement on one bounded prefix; it establishes neither
conversation competence nor any claim about the private episode's content.

## Reproduce

```sh
cargo build -p holonics-workbench
python3 research/experiments/athena_field/shared/run.py \
  --source .local/evaluations/athena-shared-source-2026-09-15 \
  --output .local/evaluations/athena-shared-baseline-2026-09-20/epoch1 \
  --development 3 --validation 1
python3 research/experiments/athena_field/shared/run.py \
  --source .local/evaluations/athena-shared-source-2026-09-15 \
  --output .local/evaluations/athena-shared-baseline-2026-09-20/validation-full \
  --resume .local/evaluations/athena-shared-baseline-2026-09-20/epoch1/trained.session \
  --development 0 --validation 2
```

[definition] `run.py` declares both prefixes explicitly and refuses to infer either. It writes
every event, checkpoint and derived table under the private output directory at mode 0700/0600,
because the prepared inputs derive from private material, and prints aggregates only. The
underlying process command is the ordinary public one:

```sh
target/debug/holonics --format jsonl hna field-session \
  --source .local/evaluations/athena-shared-source-2026-09-15/spec.json \
  --input - --checkpoint /absolute/path/trained.session
```

[definition] A shared-regions request sends `partial` with one declared symbol or `null` per
position; `null` is an active unobserved position with the zero latent seed, not an observed
zero. `observe-field-source` supplies the complete source and its target in one call.
`field-request` with `retain_comparison` now **retains** that cut instead of refusing it: the
returned `comparison` identifier applies once, in this process or after reopen, through the
ordinary `observe-field` command, and the saved session carries the request-level operands that
re-prepare its producing rows. `commit` remains refused on this chart — a shared-regions request
is a receiving cut at one field state.

## The retained comparison, the cursor and the exposure bridge

[established-bounded; source-inspected] This increment also connects the private conversation
exposure to this same session. `FieldSectionRequest::from_exposures` now builds a **held request
with a free response extent**: it revalidates each frame against its manifest, admits
development-partition, human-authored request material only, and emits
`partial = [request symbols…, null × response extent]` with `output_symbols` set. The caller
declares that aperture (`ExposureAperture`), and it is bounded against the session's own capacity
before it sizes anything. The recorded responding occurrence — the family a frame records as its
own `comparison-request` partner — arrives afterwards as an observed comparison. It is an
observed candidate, never gold.

[established-bounded; measured] `NativeFieldSavedSession` carries an `ExposureCursor` beside the
trained model in a version-3 rest that keeps versions 1 and 2 readable, so the cold source
position and the state that consumed it are published in one atomic file
([conversation data](../../../../docs/CONVERSATION_DATA.md#athena-alpha-causal-exposure)). A
frame is acknowledged only after its complete native use, so an unacknowledged frame's cursor
still names it and a reopened session redelivers it. Two named device tests hold these:
`retained_shared_comparison_applies_once_after_reopen` and
`exposure_cursor_and_trained_state_reopen_together` ([output](checks/device-tests.txt)).
The [driver](../../../../crates/holonics-hna/examples/athena_exposure_field.rs) walks development
frames under a declared frame budget and byte/length aperture, reports its own fixed refusal
labels, counts and timings, and prints no message content — it does not echo a native refusal
string either, because a refusal can quote source material.

[established-bounded; measured] Two bounded processes ran it over the actual 184,572,827-byte
private exposure at a 512-byte request aperture, a 256-symbol free response extent and a
twelve-frame budget ([output](checks/driver-run.txt)). Each peeked and acknowledged all twelve
frames; each admitted **one** human-authored development request (148 and 128 held symbols),
refused **ten** frames as `not-human-authored`, and applied **one** recorded
`comparison-request` partner. Generation took 3,635,913 µs then 3,701,557 µs; the paired update
took 12,585,133 µs then 12,789,747 µs; the processes took 18.595390 s and 20.941806 s, peaking
at 107,427,252 and 107,947,188 native section octets. The second process resumed the first's
checkpoint, continued from its saved cursor at frame 12 and advanced the model to epoch 2.
No frame refused for aperture, context, bridge or native reasons in these two budgets.

```sh
cargo build -p holonics-hna --example athena_exposure_field
target/debug/examples/athena_exposure_field \
  --exposure .local/datasets/athena-alpha-exposure-source-context-2026-09-06.jsonl \
  --spec .local/evaluations/athena-shared-source-2026-09-15/spec.json \
  --checkpoint /absolute/path/athena-exposure.session \
  --frames 64 --request-bytes 4096 --response-symbols 2048
target/debug/examples/athena_exposure_field \
  --resume /absolute/path/athena-exposure.session \
  --checkpoint /absolute/path/athena-exposure-next.session \
  --frames 64 --request-bytes 4096 --response-symbols 2048
```

## Limits

[established-bounded; source-inspected] The driver resolves the request/response pairing within
one process: it never checkpoints while holding a retained comparison it alone can attribute, and
it releases and counts an unattributable one found at reopen. A persisted exterior pairing
journal, so a pair can span a restart, does not exist. A shared-source update applies at the
material current when it arrives; the retained comparison therefore reports both its producing
epoch and the epoch that applied it rather than asserting they are equal. `shared_prior_parent`
still refuses any tool or candidate link, so this driver supplies no preceding context for such
frames and counts them. Dense normal statistics and fixed incidence remain explicit costs: one
development observation over 8,926 free rows took 496 seconds and peaked at 1.22 GB of native
sections. The driver has not been run at a conversational aperture: these two budgets admitted
one request each at 512 bytes, so nothing here measures how the bridge behaves over long
requests or long recorded responses.

[established-bounded; source-inspected] `quality.py` now carries a `shared` family that consumes
[results.json](results.json) in both modes and refuses a withheld-position count that arrives
without its content-free comparators, or a family whose receiving extent or supplied positions
were not preserved. It is a **recorded** receiver only: re-executing this family would read
private material, so a fresh-execution profile stays in this experiment and out of the public
consequence receiver. `assessment.json` still has no programmatic consumer.
