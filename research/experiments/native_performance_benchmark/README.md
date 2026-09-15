# HNN evaluation kit and native workload benchmark

[project-postulate] Use this existing apparatus for Athena's continuing evaluation. The
[shared methodology](../../../docs/ATHENA_EVALUATION.md) connects source constraints, inferred
relations, generated consequences, held-out application quality, reuse and cost. It incorporates
[the historical review](../../records/2026-09-15_ATHENA_EVALUATION_HISTORY_AND_SHARED_CONSEQUENCE_KIT.md)
without restoring retired drivers or making every profile a release gate.

[definition] `quality.py recorded --output NEW_DIRECTORY` reassesses retained mathematical and
partial-field results. `quality.py run --output NEW_DIRECTORY` calls the same public sessions
and records fresh responses, exact consequence checks and process costs through `benchmark.py`.
The field profile evaluates its existing trained artifact; the mathematical profile uses its
four-observation normal law and exact algebraic constructions. They retain different source
scopes and produce no aggregate intelligence score. The fixed references belong to those
specific profiles; a changed training/data recipe needs its corresponding reference relation.
Protocol errors and quality failures remain in the report; process exit is not a capability grade.

[definition] `episode.py --dataset PATH --request-event ID --repository-ref COMMIT:PATH
--output NEW_DIRECTORY` uses the existing conversation packager to prepare a private source
input and separate historical assessment. Explicit prior `--context-event ID` values can be
included; responses and later material are rejected as context. This is retrospective validation,
not automatic gold labeling or a reconstructed original prompt. The full conversation/repository
application remains the target; these mechanism profiles do not measure it by proxy.

[established-bounded; measured] The [September 15 integrated run](consequences/2026-09-15/result.json)
returns the current mathematical identities and partial-field consequences. Source requests,
responses and stderr remain beside it. Sixteen focused tests cover the shared timing, exact
receivers, failure visibility and private episode separation.

## Workload clocks

`benchmark.py` measures the current public HNN workloads on a declared host using existing
native process receipts, per-request `ExactWork`/cost fields, and resident transfer census values.
It records integer monotonic clocks and exact rational rates; it does not turn the work vector into
a scalar acceptance rule.

The benchmark has three bounded workload apertures:

- one C5/Power construction followed by repeated resident application in one mathematical session;
- repeated `receive-next-symbol` observations in one warm seeded wave session;
- the existing finite `receiver_code_cost` exact information/cross-entropy example, run as fresh
  exterior processes.

Warm sessions contain explicit setup and one warmup request. Steady roundtrip samples exclude
those labels, while a separate end-to-end rate includes process/setup cost. Round trips include
pipe transport, JSON serialization, native work, and requested readout. Cold samples include a
fresh process and native setup. Process receipt time, request cost, resident census, and residual
boundary time remain separate. A completed state update is counted only when the native return
declares `observation_committed: true`; a mathematical apply is a delivered face and does not
claim a continuing state update.

Run from the repository root after building the existing binaries (the recorded run uses
the debug profile):

```sh
cargo build -p holonics-workbench --bin holonics
cargo build -p holonic-engine --example receiver_code_cost
python3 research/experiments/native_performance_benchmark/benchmark.py
python3 -m unittest discover -s research/experiments/native_performance_benchmark -p 'test_*.py'
```

The default aperture is 128 warm operations and 8 fresh-process samples per native workload.
Those are declared measurement sizes, not pass/fail limits. `result.json` contains the hardware
declaration and binary hash, clock resolution, co-load snapshots, exact workload scope, integer
latency distributions, rational faces/second and state-updates/second, code/cross-entropy units,
raw roundtrip samples and reference checks, and source-native census fields. Stall counts remain
null unless an explicit deadline is added.

The raw receiver output is checked with exact `Fraction` arithmetic against an independent
integer C5 power/application reference, including the retained-product readback. Wave checks
require every requested observation to commit; they do not grade generated language. The
129th total wave update includes one unmeasured warmup before the 128 measured observations.
The mathematical inputs repeat a seven-vector family; this is a throughput workload, not
128 independent generalization tests.

Cold/code samples run inside a fresh Unix resource observer. Its `RUSAGE_CHILDREN` return
measures only that child and descendants, avoiding a previous process's cumulative peak.
`child_wall_ns` excludes the observer's interpreter startup; outer wall includes it. CPU
seconds and peak RSS (Linux KiB) are separate from CUDA payload counters. Request-cost clocks
are existing host elapsed receipts, not isolated GPU kernel timings. Wave-native transfer
counters and whole-device peak allocation are not currently exposed by this receipt.

The [shared development conventions](../../../docs/DEVELOPMENT.md#performance-and-information-measurements)
govern comparisons. No energy/bandwidth calibration or optimized-build comparison is claimed.
The [September 13 record](../../records/2026-09-13_GAME_WORLDS_SCOPED_RATES_AND_MOLECULAR_MECHANICS_SHARE_DECLARED_LAWS.md)
summarizes this machine's results and the formal rate/clock laws. `latency.png` plots the retained
raw observations; regenerate it with `python3 research/experiments/native_performance_benchmark/plot.py`
when Matplotlib is available, or use
`uv run --no-project --with matplotlib python research/experiments/native_performance_benchmark/plot.py`.
