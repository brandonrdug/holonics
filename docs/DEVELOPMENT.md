# Building and developing Holonics

Read [the machine](THE_MACHINE.md), your harness guide ([Codex](../AGENTS.md),
[Claude](../CLAUDE.md)) and the active state/roadmap. This guide gives the mathematical
implementation method, actual build/measurement commands and shared-workspace practice.

## Mathematical implementation and continuation

[project-postulate] Construct the requested relation through its existing owners and consuming
application. HNN's field, geometry, source/receiver maps and learned material are one machine.
The [Holon](HOLON.md), [model formula](HNN_FORMULA.md), [research routes](../research/records/README.md)
and [native source map](plans/THE_ATHENA_ALPHA_CULTIVATES_GENERAL_CONVERSATION_THROUGH_NATIVE_CONTEXTUAL_TRANSPORT.md#field-session-source-map)
supply concrete starting material. A mathematical result can also be its own requested return.

[definition] An implementation contract names the typed source and target, supplied data,
inferred unknown, hypotheses, generating/constitutive law, receiver and preserved equation.
For `W H=B`, for example, retain the feature/moment convention, prior and targets. For a
geometric contact, retain incidence, frame, material, units and the full variation.

| Change | Equation / evidence at the consumer |
|---|---|
| Source or condition attachment | Identify the actual pre-target carriers/restrictions and any inferred map; keep source and condition correlations in their common parameter family. |
| Serial composition | Retain the joining occurrence/equality and the complete second operation on the first return. Equal endpoint counts do not supply the join. |
| Parallel composition | Establish commutation of full read/write, lineage, obstruction and resource effects; use a checked partition/interchange law for the actual operation. |
| Representation or kernel | State `decode_Y(T_native(encode_X(x)))=T(x)` on its domain, or return the source family and oriented error enclosure. |
| Material update | Use the actual producing operands and chosen update law; include mixed terms when current and material both change. |
| Compression | Construct encoder E, induced action U and decoder D with `E_next T=U E`, `D E=ρ`; preserve the required source fibre, interior and cost. |
| Physical/experimental measurement | Retain the comparands, receiver, units, constitutive/boundary laws and clock. Compare implementations on the same actual input. |

[definition] Separate the case a failure exposes, then repair that operation:

- An existing returned object with no caller needs the actual attachment.
- A carrier unable to express a term needs a lawful rebase, factor or richer supported chart.
- A wrong derivative/material law needs its complete directional residual and corrected equation.
- Resource growth needs its measured factorization, precision or placement change.
- An unproved consequence needs the source statement, attempted derivation and remaining equation.

[established-bounded; source-inspected] Two existing rebases are useful concrete examples.
`exact_resident_section.cu::fibre_rebase_step` content-reduces elimination operands before products,
removing factors that normalization would otherwise divide away afterward. The prospective
family reader in `normal/direct/wave/family/receiver.rs` retains an ordered generating word when
its expanded composite exceeds the carrier. `Foundation/RelationPresentation.lean` states the
receiver equality; the supported factored case and vertical-fibre refusal are part of that law.
These are representation changes with a decoder, not permission to widen an exact word silently.

[definition] Read native wire layouts before interpreting a comparison. A sealed point-valued
carrier can encode the centre **and a nonzero radius** of a represented family. Normalized
sections, bilinear covectors and re-entry use those fields and their grain/denominator. The
Rust declaration, kernel argument order and actual consuming call must agree. Keep constructor
and remount validation on the carrying path, with checked extents before allocation/work.

[project-postulate] Preserve the complete object through a change. A physical receiving Holon can
have motion, material and storage; its derivative includes those terms. A phase/constant has its
normalized constraint, branch/winding and remainder. A generated face can be received before a
unique source is known. The source, law and receiver determine what must be retained.

[project-postulate] Consolidation is part of implementation: reconcile duplicate owners and
update the changed guide, record, source map and issue body together. Create documentation when
it supplies a useful explanation, contract or retrieval route. Existing source and dated evidence
are retained recoverably. Keep current order in the roadmap and current position in the state.

### Orchestrated construction cycles

[definition] The active brief retains the user objective, mathematical unknown, source/receiver,
existing owners, next edit and completion evidence. At a scope transition or context handoff:

1. Recover that brief and the applicable mathematical source already available.
2. Check the proposed edit against the actual consuming equation/call.
3. Construct and integrate the owned changes, using bounded independent workers where useful.
4. Inspect the returned result and record its scope, cost, residual and next unresolved operation.

[project-postulate] The primary owns integration and the mathematical choice. Worker prompts
carry the relevant source context through [WORKER_BRIEF](WORKER_BRIEF.md); judgements are
inspected against source, measurements are reusable receipts. Shared immutable standing and
owned differences preserve one continuing ecology. A helper or test advances its consumer;
its success does not replace an unfinished requested return.

[definition] A handoff carries the purpose as well as mechanics: governing user direction,
current unknown, available relations, actual source/receiver and consumer, meaningful failed
alternatives and next discriminating return. Completed evidence stays linked rather than queued
for replay. A paused timed goal stays paused. A new direct request can revise the operation and
its documentation without requiring another ceremonial approval.

[project-postulate] Repository-wide documentation review follows every relevant root, its entry
points, subject boundaries and source-to-application links. It includes correcting the live
contradictions and organizing the needed research. Use the scope the user requested; document
categories are not automatic exclusions. Verification establishes the inspected/changed relations,
not an unsupported claim that every historical theorem was re-proved.

## Research recovery and derivation

[definition] The [research skill](../.agents/skills/holonics-research/SKILL.md) supplies focused
mathematics, physics and computation routes. [Research reading routes](../research/records/README.md)
connect important records to maintained guides and formal/native owners. Read the source law,
not merely its filename or an agent summary.

[project-postulate] Search both a subject's vocabulary and its operations before an absence
claim, new owner, plan assumption or question that existing machinery can answer:

```sh
.agents/bin/prior-art 'subject|LeanName|rust_name|classical spelling'
rg --files research/records | rg -i 'subject|alternate spelling'
rg -n '<operation>' docs/ARCHITECTURE_MAP.md
```

[definition] The prior-art helper searches current code, documentation, all research roots and archived
source, grouping matching addresses by root. Invalid queries fail instead of producing false
absence receipts. A search receipt records its revision, aperture and terms. Hits identify material
to inspect; they do not prove a composition. Zero hits support only the searched aperture's
absence. Follow the mathematical source, imports and consumers to distinguish an unconnected
call, unsupported representation and unproved claim. A physical question returns its physical/
mathematical consequence rather than being redirected by an application label.

[project-postulate] Interpretations progress through an attempted connecting equation and its
derivation, counterexample or residual. Exact inference and scoped approximations keep their
actual consequences. Source inspection, mathematical proof, runtime evidence and an exterior
plot are different evidence scopes; none is selected merely by the directory containing it.

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

The current field/session recipes start in [NATIVE_HNA](NATIVE_HNA.md) and the
[shared-field experiment](../research/experiments/athena_field/shared/README.md). The prepared
source, manifest, partition, comparison relation and cursor are described in
[CONVERSATION_DATA](CONVERSATION_DATA.md). The public application uses the existing model and
session; a saved source cursor and a learned model are different pieces of the return.

```sh
cargo build -p holonics-workbench --bin holonics
target/debug/holonics --format jsonl hna field-session --source <spec.json> --input -
cargo check -p holonics-hna --example athena_exposure_field
```

The earlier inherited-operator `infer`/`train` interfaces retain their separate artifact scope in
[ATHENA](ATHENA.md). A run receipt is evidence for the operation it reports; persistence or
executable export has its own actual artifact/decoder and consumer.

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
Exact prime-log code forms remain in `holonics::ratio::surprisal`; decimal display is an observer
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
[shared HNN evaluation kit and native performance benchmark](../research/experiments/native_performance_benchmark/README.md)
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

[established-bounded; source-inspected] **What that calibration measures and why concurrency
breaks it.** `holonics_cuda::cuda::measure_allocation_grain_once` reads the free extent, allocates one
word, reads it again, and takes the difference as the legacy `cuMemAlloc` charge grain; it then
frees the word, requires the free extent to close exactly at its starting value, and requires a
probe one word wider than the grain to cost exactly twice. Nothing is declared and no page size is
guessed. The reading it differences, `cuMemGetInfo_v2`, is the free extent of the **whole device**
— not of this context and not of this process — so any other allocation on the card between two
samples enters the difference and the closure check fails with `one-word charge … and restored
free extent … do not close`. The perturbation carries no attribution and cannot be subtracted.
The calibration is therefore serialized process-wide (two of our own calibrations never sample
across each other), a disturbed sample is retried a bounded `ALLOCATION_CALIBRATION_ATTEMPTS`
times with the retry count reported by `holonics_cuda::cuda::allocation_calibration_retries`, and an
exhausted calibration returns **every** attempt's reading, so readings that repeat name an
allocator that does not compose while readings that differ name a busy card. None of that makes
a shared card measurable: run `--include-ignored` device suites with `--test-threads=1` and no
other GPU process, one crate at a time.

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
"Retain successful unaffected checks" means a line in
[`VERIFICATION_RECEIPTS.tsv`](VERIFICATION_RECEIPTS.tsv), not a memory. Parallel workers share
one tree and one `target/`, so they build only their own module scopes; `--all-targets` compiles
every example and belongs to a workspace-wide source move. `target/` had grown to 626 GB by
September 19 and was cleaned; keep models, rests and evidence out of it.

[definition] `CONSTRUCTION_STATE.md` records the current position and
`docs/plans/THE_ROADMAP.md` orders construction. The shared machine and mathematical guides support the harness-specific
AGENTS.md (Codex) and CLAUDE.md (Claude). The [repository guide](REPOSITORY.md) explains historical
paths and backup recovery. Keep exact raw runtime evidence in dated research receipts, and
private reproducible working data in `.local/`.
