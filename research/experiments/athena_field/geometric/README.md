# Analytic geometric field and bounded real-source experiment


The [campaign correction](../../../records/2026-09-20_THE_GEOMETRIC_FIELD_REFINES_AND_RETURNS_ITS_COMPLETE_PAIRED_CURRENT.md#correction-the-nibble-control-is-not-holonic-encoding)
classifies this as a supplied symbol-basis control. Alphabet size determines its channels;
codec symbols determine site inputs and targets; its receiver selects and packs nibbles. This
path has no Holonic Compression encoder/induced-action/decoder binding. The independent helical
moment adapter is not called here. Recorded byte validity and source reach therefore assess
this control, not the intended Holonic Encoding construction.

This experiment drives the public `NativeFieldSession` through the `GeometricRegions` source
chart. The supplied source is the validated linked-torus boundary construction in
`crates/holonics-hna/examples/support/linked_torus_field.rs`: junctions, oriented arcs, endpoint
derived exact phase transports and one selected mode enter `GeometricFieldSpec`. The compiler
checks those relations through `ExactAnalyticFieldWaveLaw` and groups receiving rows by their
actual incoming degree.

The exterior codec is the supplied hexadecimal UTF-8 nibble alphabet (`0`–`f`). Nibble symbols
select codeword basis coordinates in the declared source/receiver chart. Their site order is an
exterior map into the analytic geometry. Geometry supplies the incidence and phase, while the native field
owns resident current, participation, bilinear reaction, fixed-D reflection, held refinement and
the complete paired return.

Generate a declared source specification with the existing example:

```sh
cargo run -p holonics-hna --example athena_geometric_spec -- \
  154 2 1 /absolute/path/geometric-spec.json
```

The arguments are subdivisions, refinement steps and relaxation bits. The generated JSON records
the source chart, linked-torus junction/arc family, codec and fractional grain. This source has
1,231 unique junctions (`8 × 154 − 1`), two refinement steps and `μ=1/2`. A fresh public
session uses the existing Workbench stream contract:

```sh
cargo build -p holonics-workbench --bin holonics
cargo build -p holonics-hna --example athena_exposure_field
target/debug/holonics --format jsonl hna field-session \
  --source /absolute/path/geometric-spec.json \
  --input - --checkpoint /absolute/path/geometric.session
```

Send `field-request` objects through that stream with `commit:false` for a forecast or with a
free receiving position and `retain_comparison:true` when the producing comparison will be
observed later. Send the returned comparison to `observe-field` with the actual target and the
declared `step_bits`; the process writes the declared checkpoint after the input stream ends. `inspect` remains the existing stream operation.
The source/session implementation is [`native/field_session/geometric.rs`](../../../../crates/holonics-hna/src/native/field_session/geometric.rs), and the consuming word is
[`coupled_wave/body/field/geometric.rs`](../../../../crates/holonics-hna/src/native/coupled_wave/body/field/geometric.rs).

One geometric word has the compiled junction row count, the selected refinement-step count and
the selected condition degree. Each step gathers the query and phased neighbors, forms resident
participation and bilinear features, applies the shared material/reflection cut, scatters the
group result back to the complete row population and applies the held refinement. Reverse
reception traverses those stages in reverse order and returns both the source and condition
covectors. The geometric placement receipt covers the encoded low/high row packet and its row
status, query/neighbor incidence footprints and the mounted cover; it reports derived cover
capacity separately from execution observations and leaves D/M as opaque shared source ports.

The bounded real-source driver is [`run.py`](run.py). It selects an ordered subsequence from a
source exposure stream, preserves the captured event/family/relationship records, and only
rebases the exterior delivery sequence. It then runs split/resume and uninterrupted controls
through the existing `athena_exposure_field` binary. This profile expects one generated request
pending at the split and one observed update after resume; it checks actual acknowledgments and
retained comparisons before comparing checkpoint bytes. The sequences below name the recorded
development episode used by this campaign; a different source needs its own declared sequences:

```sh
python3 research/experiments/athena_field/geometric/run.py development \
  --source /private/source.jsonl \
  --spec /absolute/path/geometric-spec.json \
  --sequences 773 774 775 776 \
  --split 3 \
  --request-bytes 16 \
  --response-symbols 32 \
  --context-bytes 576 \
  --step-bits 8 \
  --output /private/geometric-development
```

An evaluation invocation consumes a declared episode and a completed checkpoint through the same
public session boundary:

```sh
python3 research/experiments/athena_field/geometric/run.py evaluation \
  --episode /private/evaluation-episode/input.json \
  --checkpoint /private/geometric-development/resumed.session \
  --response-symbols 128 \
  --output /private/geometric-evaluation
```

The quality kit remains the existing episode/assessment tooling in
`research/experiments/native_performance_benchmark/{episode,quality}.py`. It consumes the
separate generated result and assessment, preserving source provenance, held coordinates and
receiver scope. It does not turn a non-gold recorded candidate into a target and does not grade
the geometric field as conversationally useful.

The [campaign record](../../../records/2026-09-20_THE_GEOMETRIC_FIELD_REFINES_AND_RETURNS_ITS_COMPLETE_PAIRED_CURRENT.md)
retains the derivation, source scope, hardware defects and final checks. On the declared 1,231-site
two-step source, uninterrupted generation took **3.811 s**, the observed update **4.518 s**,
and the whole process including setup/checkpoint **14.583 s**. Split/resume and uninterrupted
execution produced byte-identical **3,594,009-byte** trained checkpoints. These are individual
observations, not a population latency benchmark or comparison with a different model.

The separate 438-byte held request generated 64 free bytes in **3.721 s**. Those bytes are invalid
UTF-8; only 2/128 free symbol faces are robust. Trained-rest opening and the full process took
**132.209 s**, exposing the remaining validated-rest cost. The actual two-step incoming support
reaches only two free coordinates from the request. Source/participating-receiver organization and
continuing field state therefore remain substantive HNN work under the existing roadmap.

Receive the separate input, historical assessment and new result with:

```sh
python3 research/experiments/native_performance_benchmark/quality.py episode \
  --episode /private/evaluation-episode \
  --generated /private/geometric-evaluation/result.json \
  --output /private/geometric-assessment
```

A supplied judgment in `assessment.json` names `generated_sha256`, its source and evidence;
empty judgments mean review is pending. Native byte/symbol/selection and held-boundary checks
remain distinct from application usefulness. The driver supports `--private-diagnostic PATH`
for a new owner-only native refusal file, which can contain source material; the runner places
these files inside its private output directory. Public reports retain fixed refusal labels.
A diagnostic write failure preserves the retryable source/model cut.
