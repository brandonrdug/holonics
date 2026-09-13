# Building and developing Holonics

[definition] Use the root Cargo workspace for host Rust code. Device-only targets under
`accelerators/` keep their declared toolchains. Lean and Typst are verification/exposition
apparatus; they are not dependencies that schedule native inference.

## Mathematical implementation and continuation

[project-postulate] Begin each increment from the requested consequence and the mathematical
unknown it exposes. Holonics' breadth supplies candidate constructions: exact preimages and
factorization, group/phase transport, recurrence and modal closure, adjoint/normalization,
boundary/current laws, analytic generators and source-specific physical models. Recover and
compose the relevant existing relations before introducing another runtime cabinet.

[definition] The working chain is

`requested consequence -> situated source and unknown -> reusable construction -> consuming operation -> returned comparison -> next inference or repair`.

This is a dependency account, not a sequence of universal approval stages. Exact construction,
empirical formation, native execution and application inspection may proceed together. The
source, coefficient ring, phase/clock, receiver, admitted future and cost chart state what a
particular construction means. Only the information required by its actual consumers is retained.

[project-postulate] The agent's continuing brief keeps six things visible: the human objective;
the latest corrections; the mathematical relation currently being constructed; the owners and
usable returns already available; the exact consuming map or obstruction; and the next check
whose outcome changes the construction. Carry this brief into a compaction or handoff in prose
or the existing position record. It is not a new public type, manifest or generated registry.
Links replace completed narratives, while the objective and causal reason for the next action
remain explicit. Read unchanged authority once and recover only what a new question requires.

[project-postulate] Progress is the returned mathematical or product consequence. A proof can
unlock a cheaper algorithm; an exact solver can return a coefficient family; a native application
can expose a previously hidden phase; an unsuccessful language reply can identify a wrong source
relation. State that content directly. A changed state, successful round-trip, test count or
larger exposure does not by itself explain the learned relation or establish usefulness.

[project-postulate] Prediction release is output of a generated face. Describe its source,
generator, receiver and requested transformation before discussing lifecycle plumbing. A
read-only forecast can already return output; a comparison handle, body update or later
observation has its own contract. Replace "actual context", "complete release", "sufficient
continuation" or a generic learning/intelligence criterion with the coefficient equation,
operator composition, retained statistic or receiver identity that the task needs. The
[blueprint's concrete cases](plans/THE_ATHENA_ALPHA_CULTIVATES_GENERAL_CONVERSATION_THROUGH_NATIVE_CONTEXTUAL_TRANSPORT.md#generated-faces-reconfiguration-correction-and-continuation)
state chunk reconfiguration, correction and continuation in this form.

[definition] Diagnose prolonged work at its actual consumer. Whole-prefix reevaluation calls
for an economical sufficient continuation. Dense future tuples call for a factor/modal form
when the requested receiver permits it. Early source acknowledgement calls for repairing the
source-to-successor transaction. A wrong conditional law calls for changed source/condition
construction. More state machinery, a generic cache or another theorem count does not resolve
all four. A returned failure should change the hypothesis, representation, owner or next check.

[project-postulate] Consolidate the construction into its mathematical owner and update its
consumers in the same increment. Generic matrix or polynomial inference belongs with the
existing algebra, not inside a fixed example. A public application invokes that owner and
declares its source, output and costs. Preserve compatibility only where there is an actual
consumer, and keep differences in source/ownership or wire semantics when they are material.

[definition] Repository-wide review means following the live roots, subject boundaries and
critical source-to-application maps, then repairing the in-scope contradictions found. Record
the inspected aperture and validation performed. It is not a claim that every theorem, archived
experiment, backend or external model was rerun. A fresh source census or universal validation
gate supplies no substitute for the requested construction.

## Rust and CUDA

The current native engine/HNN build is Linux/CUDA-bound, including generated PTX and CUDA
linkage. A Mac checkout does not yet provide an executable engine backend; see
[hardware and modality boundaries](HARDWARE_AND_MODALITY_BOUNDARIES.md) for the exact dependency
seam and MLX comparison. Repository documentation and exterior data tools are independent of
that native runtime. The current native runtime uses the NVIDIA CUDA driver and toolkit. Make `nvcc` available on
`PATH` (this workstation uses `/opt/cuda/bin`). The kernel builder declares its architecture;
the driver can JIT the admitted PTX on the actual device. Model material is supplied separately.

```sh
export PATH=/opt/cuda/bin:$PATH
cargo check --workspace --lib --bins
cargo build -p holonics-workbench --bin holonics
target/debug/holonics --help
target/debug/holonics hna --help
```

For Rust clients, the local `crates/holonics` package exposes `structure` and `geometry` even
with default features disabled. Default `native` also exposes `engine`, `hna`, `soulkiller`
and `interop`, preserving the existing runtime API. The [Rust framework guide](RUST_FRAMEWORK.md)
states the dependency and implementation boundaries. The facade re-exports its owners.

## Training and inference

```sh
target/debug/holonics hna infer /path/to/supported/model 'Explain holonics briefly.'
target/debug/holonics --format json hna train /path/to/supported/model sequence.json
target/debug/holonics --format json hna run request.json
target/debug/holonics hna inspect /path/to/native.rest
```

The [native guide](NATIVE_HNA.md) gives the current ground-up phase-session recipes. The
commands above use the earlier inherited-operator chart, whose campaign remains paused.
The [Athena guide](ATHENA.md) defines those request and artifact scopes. The current training
command consumes a continuing prefix sequence and returns a run receipt. A checkpoint/export
must not be inferred from that receipt.

## Formal work and papers

```sh
bash tools/lean_check.sh
bash tools/lean_check.sh ElementaryHolonics.RH.CriticalChart
```

[established-bounded; source-inspected] `formal/elementary-holonics/lean-toolchain` and
`lake-manifest.json` pin the formal dependencies. The default `ElementaryHolonics.Framework`
target presents the reusable mathematical subjects;
`ElementaryHolonics` is the complete research umbrella and RH targets may be checked independently.
The package-local `check.sh` forwards here without updating pinned dependencies. `.lake/` caches
remain ignored and retained.
Authored Typst work is under `research/papers/source/`; compile it when editing or using those
papers. It is not a required check for unrelated Rust work.

## Performance and information measurements

[definition] A **face delivery** completes a requested receiver output: a rendered image,
decoded text section, solved coefficient family or another declared face. An **owner update**
completes one admitted successor at its continuing owner. Report the selected operation and
receiver address; these are scoped analogues of frames and ticks. A GPU launch, a symbol,
a source observation and a successor are not interchangeable counts. A forecast can deliver
an output without advancing its body. Equal repeated output still counts as deliveries,
while its information cost depends on the declared conditional code.

[definition] Over an elapsed interval `dt > 0` in a named clock, rates are `N_face/dt` and
`N_update/dt`. Aggregate disjoint serial windows as `sum N / sum dt`; do not average reciprocal
latencies without duration weighting. Concurrent branches require an actual common observation
interval and identified deliveries to avoid double counting. Simulation time per wall time,
device event time, CPU time and end-to-end latency have different units/scopes. Under an affine
clock map `t' = a t + b`, `a > 0`, the same rate becomes `r/a`. A signed clock reversal changes
the sign of an oriented quotient; it does not reverse dissipative dynamics or prove detailed
balance. Nonlinear clocks use their actual finite interval, or `r/f'(t)` locally when defined.

[definition] For the same measured occurrence family, information throughput factors as
`bits/second = occurrences/second * bits/occurrence`. A code reading uses conditional lengths
`sum -log2 q(y_k | conditions_k) / dt`; an expected finite positive-distribution reading is
`r H2(p,q) = r H2(p) + r KL2(p||q)`. An event rate alone is not cross-entropy. Keep alphabet,
conditioning, probability receiver and log base; zero code probability for an observed event
has infinite cost or an explicit missing-code return, not a silently finite replacement.
Exact prime-log code forms remain in `holonic_engine::surprisal`; decimal display is an observer
projection. Code lengths, phase differences, physical joules and coordinate time are separate
quantities until their constitutive map is supplied.

[proved-derived; formal-checked] `Foundation/SituatedInformationRate.lean` proves affine
clock transport, duration-weighted serial composition, measured-information factorization,
expected entropy/KL rate decomposition and the conditional resource ceiling:
`N*w_min <= W <= B*dt` implies `N/dt <= B/w_min`, for positive `dt,w_min`.
Each resource uses its own work/capacity units; jointly applicable ceilings can be intersected.
This is a hardware/workload bound, not a universal computational speed of light.

[project-postulate] Benchmark the useful operation with its substantive output or mathematical
reference. Record source revision, workload/extent, exact precision/bit growth, hardware and
co-load, cold-start conditions, warm-up, repetition count and clock resolution. Retain raw
durations and report total throughput, median and appropriate tail quantiles/maxima; a p99
from only a few observations is an order statistic with little tail evidence. Define a stall
against an explicit application deadline, not an invented universal cutoff.

[project-postulate] Keep compilation, process/context creation, material setup, exterior
construction, resident execution, synchronization/readout and complete delivery boundaries
visible. Do not subtract overlapping durations as if they were serial work. Use existing
receipts and asynchronous device events; do not introduce per-hot-operation host semantic
readback merely to measure. Report payload bytes, allocator/device/process high-water readings,
transfer direction and exact resource work separately. Missing counters are unknown, not zero.
Joules/operation or bits/joule require an energy receiver with sampling interval and baseline;
an SSD label or GPU power limit does not measure either quantity.

[definition] `ExactWork` is the exact arithmetic/resource vector, with its existing product
order and `WorkBudget`; it deliberately carries no elapsed clock. This local type contract
does not prohibit timing statistics, loss objectives or external deadline/resource policies.
Floating-point timing/quantile displays are observer calculations, not device semantic
coefficients. A timeout records an unfinished run at its deadline, not mathematical
infeasibility. Historical "no scalar"/"clock may never select" wording must be read at the
actual erroneous substitution, never as a ban on measuring or optimizing performance.

[established-bounded; measured; computational-witness] The
[native performance benchmark](../research/experiments/native_performance_benchmark/README.md)
applies these conventions to public C5 power/application, committed wave observations and
exact code-cost calculation. It checks actual rational outputs and committed requests, keeps
raw samples and reports process CPU/RSS, payload residency and transfer at their available
scopes. Its explicit workload labels and setup boundaries are the measurement pattern for
further applications; the file is an experiment, not a universal gate or native mechanism.

## Verification cadence

[definition] CUDA controls that measure allocation granularity require an isolated allocation
reading. Run the explicit resident-return controls with `--test-threads=1`; concurrent contexts
can invalidate that calibration before the numerical test starts. This is an observer/apparatus
condition, not a production worker limit or a reason to serialize independent native currents.

```sh
cargo test -p holonics-hna --lib hna
cargo test -p holonics-workbench --lib adapters::hna
cargo test --workspace --lib --bins --tests
cargo check --workspace --examples
```

[definition] The workspace commands above are appropriate for a workspace-wide source move;
ordinary changes use their affected owner tests. Supervise productive compilation and diagnose
an unfinished check before resuming it. Retain successful unaffected checks. The blanket gate,
document/index tools and source-size ledger are archived; do not recreate them or compile every
example/paper after each edit. Review source cohesion and verify behavior directly.

[definition] `CONSTRUCTION_STATE.md` records the current position and
`docs/plans/THE_ROADMAP.md` orders construction. AGENTS.md is the shared agent operating
contract; CLAUDE.md is its pointer. The [repository guide](REPOSITORY.md) explains historical
paths and backup recovery. Keep exact raw runtime evidence in dated research receipts, and
private reproducible working data in `.local/`.
