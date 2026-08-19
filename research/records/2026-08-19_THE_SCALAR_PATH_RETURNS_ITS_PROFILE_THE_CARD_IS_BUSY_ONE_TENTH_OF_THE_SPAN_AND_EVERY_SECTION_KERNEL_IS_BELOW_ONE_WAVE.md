# The scalar path returns its profile: the card is busy one tenth of the span, and every section kernel is below one wave

**Date:** 2026-08-19
**Kind:** construction return for **Deed H0** of the single-card plan — the physical profile of the
*unchanged* scalar path — with the closure, the timeline, the per-kernel resources and scheduler
states, the transfers, the CPU phases, the semantic receipts, the product-ordered utility receipt,
one attributable classification per load-bearing kernel class and per boundary, what it does not
claim, and the open items it hands to H1.
**Truth status:** `established-bounded` for every measurement (each carries its artifact row and
the command that produced it); the classification rubric is a **declared receiver family** applied
as code; `interpretation` for nothing — no holonic reading is promoted here; **Deed H0 PASSES on
this tree**; no later deed is promoted.
**Authority:** `blueprint/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md`
§3 (the receipts), §4, §8 "Deed H0", §11 (falsifiers); the audit
[THE_WARP_SCHEDULER_DOES_NOT_SCHEDULE_THE_HOLON…](2026-08-19_THE_WARP_SCHEDULER_DOES_NOT_SCHEDULE_THE_HOLON_THE_REDUCTION_IS_A_TYPED_JUNCTION_AND_THE_CARD_OWES_ITS_PRESSURE_FIELD.md);
`CLAUDE.md` §0o.
**Position boundary:** [`CONSTRUCTION_STATE.md`](../../CONSTRUCTION_STATE.md) does not move.
**Driver:** `crates/holonic-engine/examples/the_scalar_path_returns_its_pressure_and_utility.rs`
(site `phoenix/profile.rs`; modes `--receipts` on the card and `--join --telemetry-dir`); the
telemetry deriver `tools/profile_scalar_path.py` (stdlib + sqlite3, reads the Nsight Systems
export). The profiled program is the **committed Station C driver, unchanged**.
**Artifacts:** `output/the_scalar_path_returns_its_pressure_and_utility/` — `source-and-mode.form`,
`causal-fronts.form`, `exact-work.form`, `pressure.form`, `kernel-timeline.tsv` (7,626 rows),
`transfer-timeline.tsv` (4,735), `cpu-api-timeline.tsv` (70,521), `cpu-process.tsv` (32),
`kernel-resources.tsv` (72), `scheduler-states.tsv` (138), `calibration.form`,
`surface-utility.form`, `profile.form`, `pressure-joined.form`. Raw Nsight reports stayed outside
the repository (they are the instrument's files, not the deed's).

---

## 0. Verdict

**The unchanged scalar path is now measurable, and what it measures is the audit's claim in
numbers.** Under Nsight Systems, the committed one-input tower (42 layer graphs + the final graph,
input *"The capital of France is"*, midpoint chart, grain 2^-48, 14 terms) ran 37.68 s against
31.81 s unprofiled (+18.5 %), returned the same future section bit-identically, and showed:

- **43 graph launches, verified exactly** (43 `cuGraphLaunch`, 43 captures, 43 instantiations, 43
  synchronizations; every graph-node kernel carries the correlation id of one of them; 136 kernels
  in graph 0, 138 in graphs 1–23, 122 in 24–41, 8 in the final graph; 5,514 graph-node kernels,
  bit-identical to the driver's own `captured launches 5514`).
- **The card is busy 10.22 % of the kernel span** (1.359 s of kernel-interval union inside 13.30 s
  from first to last kernel) and **4.27 % of the wall**; 18.25 s elapse before the first kernel
  (the container digest, the tokenizer subprocess, context creation, the first source read).
- **The inter-graph CPU gap is 228–281 ms per layer against a 10.8–11.9 ms graph GPU wall — ×23**;
  the 42 gaps sum to 12.46 s = 93.7 % of the span. Inside a gap: 14.3 % CUDA API (`cuCtxSynchronize`
  5.8 % — one per direct mount kernel, 2,112 of them; `cuMemFree` 3.8 %; `cuMemcpyHtoD` 3.4 %),
  14.4 % `read(2)`, 4.1 % `ioctl`, 5.8 % the mount kernels on the card, and ~62 % main-thread CPU
  under no instrumented call. The driver's own phase clocks (apparatus, measure-never-select)
  attribute that to the mount phase: per layer mount 0.17–0.30 s, bind 0.022 s, launch+sync
  0.011 s — the source read, per-region SHA-256, bf16 decode and the serialized mount launches.
- **Graph permission is not measured overlap, measured:** each layer graph permits its whole node
  population (schedule `CoPresent`, 13 of 45 fronts with ≥2 members) and the card carried **at most
  4 or 5 kernels at once**, with ≥2 kernels concurrent for 36–42 % of each graph's wall and 1.4 %
  of the whole span.
- **Every `section_*` launch geometry is below one wave** (waves per card = threads ÷ 80 SMs ×
  1,536 = 0.010–0.417; the one exception is the final graph's tied-boundary contract at 10.7). The
  contraction that carries the layer runs **grid 100 × block 512 = 51,200 threads** for gate/up,
  25 × 512 for o/down/PLE, 3 × 512 for k/v — 0.42, 0.10 and 0.0125 waves — with **42 registers,
  66.7 % theoretical and 28–40 % achieved occupancy, 4.06 active / 0.48 eligible / 0.32 issued warps
  per scheduler cycle, 67 % of cycles with no eligible warp, stall `long_scoreboard` in 10 of 10
  profiled launches, 9 % DRAM and 12 % SM throughput** (Nsight Compute, layer 1's 138 kernels, 40
  replay passes each, counters reached under `sudo`).
- **The inner dimension is serial:** at one fixed output extent (12,800 threads) the contract's
  median duration spans **45×** across its launches — the inner dimensions 256, 2,048 and 10,240
  of the PLE projection, `o_proj` and `down_proj` — K is in no telemetry column and its signature
  is in the durations.
- **Transfers are not the bottleneck and are serialized with compute:** 9.29 GB host→device in
  1,745 copies at 22.4 GB/s (71 % of gen4 ×16 nominal), 3.1 % of the span — and **0 ns of those
  415 ms overlap any kernel**; two copy engines exist and at most one transfer was ever in flight.
- **The mount path serializes:** `bfloat16_align`, `bfloat16_lowest_exponent` and
  `exact_row_absolute_mass` run 704 times each outside any graph, each followed by a
  `cuCtxSynchronize`; `exact_row_absolute_mass` at grid 1–3 × 1,024 sums to 502 ms.
- **Census kernels are 7.7–11 % of every graph's GPU wall** (2,757 launches, median 13.3 µs,
  97.8 % no-eligible, stall `drain`) — below the 30 % bar; they are not the bottleneck, the
  foreman is.

**The pass predicate is met:** one attributable classification per load-bearing kernel class and
per boundary, each citing its rows and carrying its confidence, with the calibration beside it;
**no semantic code changed** — `git diff` of the deed is the new driver, the new example-site
module, the deriver script, and the documents.

## 1. The closure

| face | value |
|---|---|
| commit | `6b2b5e3f3605f54fbdca9b58be16a4c774365bee` |
| program | `the_tower_conducts_layer_by_layer_and_the_future_section_is_plural --text "The capital of France is" --grain 48 --terms 14 --no-source-face --no-interval-control --no-vision-control` (release, built at this commit) |
| input | tokens `[818, 5279, 529, 7001, 563]`, 5 positions; chart `Midpoint`; grain 2^-48; 14 terms |
| source | `model.safetensors` 15,992,595,884 octets, header sha256 `0e2afcbe…`, content sha256 `cfbd3d2f1cd71bd4…`, file identity recorded; implementation `modeling_gemma4.py` sha256 `64ecac47…` (transformers 5.8.1); config sha256 `33b10c02…`; assets declared unused |
| mode | `exact-integer-interval-v2`, kernel content `98dc0e00…`, device `NVIDIA GeForce RTX 4080 SUPER compute_89 sm80 warp32`, apparatus `cpu+device0` |
| device (cuDeviceGetAttribute) | 80 SMs, 1,536 threads/SM, 48 warps/SM, 65,536 registers/SM, 102,400 shared octets/SM (nsys' `TARGET_INFO_GPU` says 101,376 — two apparatus faces, both stated), 24 blocks/SM, clock 2,580 MHz, memory clock 11,501 MHz, 256-bit bus, 2 copy engines |
| profilers | Nsight Systems 2025.1.3 and Nsight Compute 2025.2.1 from `/opt/cuda-12.9/bin`, on driver 595.71.05; counters admin-only (`RmProfilingAdminOnly: 1`), reached under `sudo -A`; `perf_event_paranoid = 2` |
| overhead | walls: cold 33.54 s, warm 31.81 s (baseline), /proc-sampled 32.20 s (+1.2 %), nsys 37.68 s (+18.5 %), ncu 138.74 s (×4.36, 138 kernels × 40 passes); the returned future `7001 " France" [12.721, 12.721]` and `deed launches 43 · captured launches 5514 · synchronizations 43` bit-identical across every run |
| representative layer | layer 1 — sliding species, entry on a carried standing, own K/V — the shape 34 of 42 layers have |

## 2. The semantic half (the receipts the passage already returns)

Layer 1: **45 fronts, 69 members, 13 fronts with ≥2 members, all 45 certified `Interchangeable`**,
graph **139 nodes / 146 edges** (138 kernel nodes + 1 memset), one launch, one sync, the a-priori
octave bound held on all 69 ports. Deed `ExactWork`: additions 471,957,280 · multiplications
474,180,640 · divisions 1,817,940 · entries written 1,743,360 · cumulative bits 81,274,880 · peak
bits 242 · resident entries 204,800 · dependency span 45. Admission: 9 semantic + 27 apparatus
coordinates, 5 bounded (carrier peak octaves 63/63, charged resident octets 297,795,584 of
15,684,665,344 free, scratch 18,432/49,152, grid extent 51,200, source standing 749,844,500 =
admitted) and 31 exhibited as unbounded with what constrains them. Traffic (the `receiver_current`
face): resident lanes 122,880, **service rounds 1 on every front** (occupied lanes 1,280–102,400),
earliest arrival 8, deferred arrivals 8, 7 reconvergent sites, 44 junctions, composite transmission
22/21 and reflection 1/21. **The semantic cover says even the widest front fits the card in one
round; the card measured four or five concurrent kernels. That gap is the deed's headline.**
Per-occurrence `ExactWork` is not reachable through a public accessor (it sits on the private
`LawShape` of `front_passage::Plan`); per-front and per-coupling work are reported instead, and the
accessor is handed to H1.

## 3. The classification, as `profile.form` carries it (rubric declared before measurement; first applicable class decides; secondaries listed)

| object | class | secondary | deciding value | confidence |
|---|---|---|---|---|
| `section_contract` (385) | **UNDER-PARALLEL** | INNER-SERIAL, STALL-BOUND | 384/385 launches below one wave; fixed-extent duration ratio 45.2; no-eligible 67 %, `long_scoreboard` 10/10; DRAM 9 %, SM 12 % | measured |
| `section_rms_rebase` (343) | UNDER-PARALLEL | STALL-BOUND | 343/343 below one wave; no-eligible 65.5 % | measured |
| `section_contact` (42) | UNDER-PARALLEL | STALL-BOUND | 42/42; median 341 µs; no-eligible 93 % | measured |
| `section_gelu_tanh` (84) | UNDER-PARALLEL | — | 84/84; no-eligible 45 % (below the 50 bar) | measured |
| `section_hadamard` (84) · `section_re_entry` (168) · `section_scale` (126) · `section_chronology` (66) · `section_from_bfloat16` (84) · `section_carry` (78) | UNDER-PARALLEL | STALL-BOUND | every launch below one wave; no-eligible 65–94 % | measured |
| `section_census` (2,757) | UNDER-PARALLEL | STALL-BOUND | 2,756/2,757 below one wave; no-eligible 97.8 %, stall `drain` | measured |
| `section_collapse_control` | LAUNCH-LATENCY-BOUND | UNDER-PARALLEL, STALL-BOUND | median 1.4 µs; launch share 0.17 | measured |
| `exact_row_absolute_mass` (704, mount) | UNDER-PARALLEL | — | 703/704 below one wave (grid 1–3) | nsys only |
| `bfloat16_align` · `bfloat16_lowest_exponent` (704 each, mount) | UNCLASSIFIED | — | 319/704 below one wave; the rest 2–5,461 waves | nsys only |
| boundary: inter-layer CPU gap | **CPU-FOREMAN-BOUND** | — | every gap (228–281 ms) ≥ the previous graph's GPU wall (10.8–11.9 ms) | nsys only |
| boundary: source read + mount | CPU-FOREMAN-BOUND | — | 12.6 ms/graph of `cuMemAlloc`+`cuMemcpyHtoD` API alone, plus 2,112 `cuCtxSynchronize` (one per mount kernel) and the uninstrumented CPU the driver clocks put in the mount phase | nsys only |
| boundary: release (`cuMemFree`) | CPU-FOREMAN-BOUND | — | 11.2 ms/graph, 9,416 calls | nsys only |
| boundary: bind/instantiate | UNCLASSIFIED (not a bottleneck) | — | 0.39 ms/graph | nsys only |
| boundary: launch → sync | NOT-APPLICABLE | — | 14.7 ms/graph, a span containing the card's own execution | measured |
| boundary: H2D transfers | **TRANSFER-BOUND (serialized)** | — | 22.4 GB/s = 71 % of nominal (rate rule false), **0 ns of 415 ms concurrent with any kernel** (serialization rule true) | nsys only |
| per graph: census share | UNCLASSIFIED | — | 0.077–0.11 of the graph wall, bar 0.30 | nsys only |

The one amendment made after measurement is stated in the artifact: the class is decided by the
**launch-count majority** of a kernel's geometries, not by its widest launch — the first join took
the widest launch and called the contraction `STALL-BOUND` because the final graph's tied boundary
runs 10.7 waves; one atypical member was deciding the class, and the rule was corrected in code
before the classification was read.

## 4. What was built, and what was not touched

Built: the driver (two modes), `phoenix/profile.rs` (the TSV/form readers and the rubric as code),
`tools/profile_scalar_path.py` (the sqlite export → the five TSVs + the derived timeline
readings). Not touched: anything under `crates/holonic-engine/src`, `soma/`, `kernels/`, or any
committed driver. The deed did not rerun Station D.

## 5. What this deed does not claim

No semantic improvement; no faster kernel; no claim about what H1–H5 will achieve; no holonic
reading of the hardware beyond the plan's firewall (a warp is not a holon, a stall is not a
refusal). Nsight is exterior apparatus: it measured the realization and testifies for nothing
semantic. The nvidia-smi sample is carried labelled COARSE and promoted nowhere. What could not be
measured stays `unknown`: PCIe link counters, per-phase energy, CPU PMU counters, scheduler states
outside layer 1, occupancy for the 39 geometries ncu did not profile.

## 6. Open items handed forward (named, not repaired here)

1. **The apparatus and semantic allocation counts differ**: `cuMemAlloc_v2`/`cuMemFree_v2` 9,416
   each per run against the surface census's 5,894 allocations — the mount path's readout
   allocations, or a per-section pair, are outside the census; H1 names which.
2. **Per-occurrence `ExactWork` needs a public accessor** on `CompiledPassage`/`CompiledPlan`.
3. **`/proc/PID/sched` reports the thread-group leader**; the migration and switch columns are
   the main thread's (539 migrations, 1,513 voluntary and 1,270 involuntary switches over the
   run; 5 threads; 9.74 GB read; RSS 257 MB), not process sums.
4. **The final graph's tied-boundary contract** (5 × 262,144 outputs, 10.7 waves, 163.6 ms, two
   kernels, overlap 0) is the one section kernel above one wave and is H2's second target after the
   layer contractions.
5. `output/` is gitignored: the artifacts are held by the output manifest (hashes), as every
   deed's are.

## 7. The validation epoch and the release reading

`cargo check`/`cargo build --release` of the one new example (agent B); no workspace test; no
rerun of Station C or D; the Station C driver executed five times under the profilers and their
controls (walls in §1). Two agents, dispatched in parallel against a written contract (the TSV
columns, the rubric, the closure, the forbidden actions) and reviewed against the tree: A's
43-graph check, its nsys/ncu agreement on every `waves_per_sm` row (73/73), and B's
per-launch-majority correction were checked by the orchestrator before this record was written.

**The one complete gate**, `bash tools/gates.sh`, 2026-08-19 20:31:19 → 20:33:30 UTC, exit 1,
2 m 11 s — **11 of 12**; the one red was `driver-catalog: DRIFTED — 0 not in the catalog, 0 not in
the tree, 256 rows re-measured`, because the catalog had been regenerated *before* the claim index
in the same ledger pass and its "named in a document" column re-measured differently once the index
named this record. No code, kernel, driver or artifact changed; the catalog was regenerated after the
documents and **the named gates rerun alone at 20:34:17 UTC: `driver-catalog` PASS (256 drivers, 0
uncatalogued), `claim-index` PASS**. The two scopes are reported separately, and the ledger order
— documents, then catalog, then index — is now the one this session uses.

```text
PASS  tests              2517 passed, 0 failed, 19 ignored over 29 result lines; example targets type-checked
PASS  authored-levels    0 failures; 414 authored numeric levels in DRIVERS
PASS  named-paths        0 failures; 2794 tokens
PASS  line-citations     0 failures; 431 citations
PASS  claim-index        current
FAIL  driver-catalog     DRIFTED — 256 rows re-measured (ledger order; rerun alone: PASS)
PASS  output-manifest    recorded 57 drivers, present 57: 0 departed, 0 moved, 0 unrecorded
PASS  closure-manifest   current: 58 return directories, 21 orphans
PASS  boundary-artifacts 3 bound
PASS  typst              10/10
PASS  architecture-lint  clean: 239 files, 21760 inherited occurrences, 0 retired
PASS  document-law       0 failures; 71 absence claims carry command and date
11 passed, 1 failed: driver-catalog   →   driver-catalog, claim-index rerun alone: 2 passed
```

## 8. The station table

| deed | required artifact | grade | decisive evidence | remaining obstruction |
|---|---|---|---|---|
| A–D | (frozen bounded stations) | PASS | their records | none |
| **H0** | calibrated physical profile of the unchanged scalar path | **PASS** | this record; the fourteen artifacts; one classification per load-bearing kernel and boundary | none |
| H1 | typed partition and reduction receipts | open | — | next |
| H2 | real Gemma contraction tiled, exact | open | — | after H1 |
| H3 | reductions, census, receiver-dependent fusion | open | — | after H2 |
| H4 | one streamed resident tower circulation | open | — | after H3 |
| H5 | Station D through shared branches | open | — | after H4 |
| P0–P5 | Phoenix from native morphology to the frozen runtime | open | — | after H5 |
| M0–M3 | mathematics-codec vertical | open | — | after P5 |

Deed H0 passed; proceeding to Deed H1.
