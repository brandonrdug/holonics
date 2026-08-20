# The tower is a streamed circulation, the single graph returns its three cuts, and the transfers cross under the kernels

**Date:** 2026-08-19 (committed 2026-08-20 UTC)
**Kind:** construction return for **Deed H4** of the single-card plan — the whole tower as one
streamed resident circulation with one pre-deed admission and one terminal synchronization of the
conducting current — with the whole-tower single graph attempted and its exact limiting cuts
returned by name, the equality against Station C's committed artifact, the apparatus census against
H0's, the measured overlap, two defects found and repaired by the deed's own falsifiers, and what
it hands H5.
**Truth status:** `established-bounded` for every measurement; `implemented-exact` for the streamed
standing owner and the pooled mount; **Deed H4 PASSES on this tree** — the segmented realization is
the lawful form under the returned cuts, its segment boundary the declared exterior I/O boundary
(the pinned-staging refill), with no CPU semantic choice between segments, asserted structurally
and by census.
**Authority:** the single-card plan §5, §8 "Deed H4", §11; [H0](2026-08-19_THE_SCALAR_PATH_RETURNS_ITS_PROFILE_THE_CARD_IS_BUSY_ONE_TENTH_OF_THE_SPAN_AND_EVERY_SECTION_KERNEL_IS_BELOW_ONE_WAVE.md)
(the foreman decomposition this deed answers), [H3](2026-08-19_THE_CENSUS_DROPS_ITS_ATOMICS_THE_QUOTIENT_FUSES_WHERE_THE_RECEIVER_FACTORS_AND_THE_MOUTH_READS_ITS_MATERIAL.md)
(the fused seal this deed relies on, with the reliance stated).
**Position boundary:** [`CONSTRUCTION_STATE.md`](../../CONSTRUCTION_STATE.md) does not move.
**Owners:** `crates/holonic-engine/src/streamed_standing.rs` (the absent relation, stated: no
standing owner outlived one deed to be *rewritten* for the next — `SlotShape`/`StandingSlot`/
`StagedRegion`/`StreamedCirculation`/`GraphKey`, and it **owns no reader**); the pooled mount
(`embedding_fiber::mount_bfloat16_pooled`, `PooledMount`/`PooledReadout`); pinned/async/event
accessors on `soma/mount` (`cuMemAllocHost_v2`, `cuMemFreeHost`, `cuMemcpyHtoDAsync_v2`,
`cuEventSynchronize`; `PinnedHost`, `Stream::copy_host_to_device_async`, `Event::synchronize`);
`front_passage::{launch_on, predict_pooled_material, factored_seals}`.
**Driver:** `crates/holonic-engine/examples/the_tower_is_one_streamed_circulation.rs` (site
`phoenix/streamed.rs`; deriver `tools/profile_streamed_circulation.py`).
**Artifacts:** `output/the_tower_is_one_streamed_circulation/{receipt.form, census-old-against-new.tsv, profile.tsv, overlap-timeline.tsv}`.

---

## 0. Verdict

**Fifteen of fifteen falsifiers pass.** For the committed Station C closure (*"The capital of
France is"*, midpoint chart, grain 2^-48, 14 terms), the tower runs as **43 segments under one
pre-deed admission and ONE terminal synchronization of the conducting current**, the staging of
layer k+1 reading the container into pinned slots while the card conducts layer k, the copies
crossing asynchronously on their own stream, the mount/align kernels captured into each segment's
graph, the device maps pooled in alternating slots, and **no CPU semantic inspection anywhere in
the loop** — structurally (the circulation owner has no accessor from which a section, census slot
or terminal is reachable) and by census (`section_read_outs 0 → 0`, `egress_section_octets 0 → 0`
across all 43 segments).

**The semantic return is the committed predecessor's, bit for bit:** the plural future section
(`7001 " France" [3580683713715203/281474976710656, 895170928428801/70368744177664]`, 1 not
separated, 262,143 separated), the final normed standing (12,800 coordinates, first difference
`None`), every layer's collapsed population, and the tower's exact work. The reliance on H3's
fusion law is stated: 1,297 of 1,297 quotients fused, and falsifier 7 measures the collapsed
population unchanged. The mode identity differs from the committed one because H3 rewrote the
kernels; the equality target is the semantic faces, which are the receiver's object.

**The whole-tower single graph was attempted and refused, with three cuts returned by name:**
(1) residency — the tower's mounted maps are 37,156,141,916 octets against 16,450,125,824 free, so
the maps must be reused, forcing the replacing copies into the same graph; (2) pinned host
standing — a graph memcpy node's source is fixed at instantiation, so all stored codewords
(9,288,903,168 octets) must be pinned at once against ~21.6 GB available; (3) **the decisive,
circular cut** — the mouth's common exponent is a reduction over the material that the same graph
would produce: it is an argument of `bfloat16_align` and, with the entry octaves and row masses,
decides every a-priori octave bound and hence the admission and the kernel parameters — 2,112
host-held values across the tower, so a single graph needs a measuring pass and a conducting pass,
i.e. reading the source twice. The API attempt is recorded (`cuGraphLaunch` into an open capture →
`CUDA_ERROR_STREAM_CAPTURE_UNSUPPORTED`), and the unbound child-graph/memcpy-node routes named.

**The apparatus census against H0's, and the measured overlap:**

| coordinate | H0 (committed path) | this deed |
|---|---|---|
| conducting-stream synchronizations | 43 | **1** |
| mount `cuCtxSynchronize` | 2,112 | **0** (86 mount-stream syncs — the mouth's own host round trip, the circular cut's standing cost — plus 41 per-slot staging `cuEventSynchronize`) |
| `cuMemAlloc` / `cuMemFree` | 9,416 / 9,416 | **3,105 / 3,105** |
| H2D | 1,745 synchronous, 0 ns overlapping | 704 asynchronous (+179 small sync); **85.1 % of transfer time concurrent with a kernel** (306,125,666 of 359,527,375 ns) |
| regions re-digested per run | 704 | **0** (identity + header once pre-deed; the whole-content digest reused from the committed manifest with its date; `verify_still` after) |
| source occurrences built | 43 | 1 |
| graph kernel nodes | 5,514 | 4,260 (the fused seal) |
| card busy over its span | 10.22 % | **28.6 %** |
| wall | 23.8 s (committed face) | **9.1–10.5 s** (loop 3.1–4.6 s; ~0.8 s is page-locking 1.98 GB, named) |

**The first overlap attempt measured 0 ns and is carried as a lesson:** with the copy issued after
the next staged read, every copy landed after the graph it was meant to overlap — every stream
asynchronous, nothing concurrent. Graph permission is not measured overlap, and neither is stream
asynchrony; the repair was staging two segments ahead with the crossing one ahead (three pinned
slots) and narrowing the staging wait to the slot's own event.

## 1. Two defects found and repaired by the deed's own falsifiers

1. **`read_section` panicked on a fused quotient's own face** — it indexed the section map directly
   instead of resolving the seal alias as `section()` does; found the first time a receiver read
   the final normed standing through a fused seal; repaired with a regression test.
2. **The staged region addressed the file where the region identity addresses the payload** —
   reading the payload-relative offset as absolute mounted the wrong octets, **and the tower
   conducted ten layers on them** before an a-priori bound refused. Wrong material returns numbers.
   Falsifier 0 now compares every staged region word-for-word against the container's own reader,
   and `payload_base()` is public with the distinction stated.

## 2. Graph reuse (§5.4), founded and not faked

`GraphKey` is founded from real faces (mode, source identity, per-segment topology digests, port
extents/carriers, grain/terms, the reduction words verbatim, the receiver boundary) and stated in
the receipt; **reuse is unexercised and says so.** What a second input of the same extent would
need is measured from what stands — no graph update at all, because the pool fixes every weight
address and the refill rewrites entering codewords in place; a different extent needs
`cuGraphExecKernelNodeSetParams`, which `soma/mount` does not bind. Handed to H5, which will
exercise reuse across the dissection's sibling cohort.

## 3. Tests, ledger, epoch

`cargo test -p holonic-engine --lib -- resident_section front_passage streamed circulation` → **49
passed**; `tests/h1_adversary.rs` → 35 green; every example type-checks. The poisoned-lineage
falsifier measured its own boundary honestly: a refusal does not cross a graph boundary (a released
standing carries words, not a census slot), and the circulation does not stop early because
stopping early is the CPU inspection falsifier 2 forbids — the refused terminal returns refused.
Ratchet: the deltas enumerated and dispositioned in the deed's report (the consumer/declared-face
indexes as material relations, the returned populations of the staging/crossing/mounting steps,
refusals owning their evidence; two named excision candidates — the whole-`SlotShape` clone and
`crossed_once` as a parallel vector — carried, not taken); rows changed by hand. The site's
`SLOTS = 3` is named as the honest authored-level candidate (the pipeline depth should derive from
measured refill-versus-conduct extents); it is a driver constant, counted not dispositioned, and
carried here so it is not lost. Station C's driver and artifacts untouched — the independent
predecessor.

## 4. The station table

| deed | grade | decisive evidence |
|---|---|---|
| A–D, H0–H3 | PASS (frozen) | their records |
| **H4** | **PASS** | this record: one admission, one conducting synchronization, bit-equality with the committed artifact, the three cuts named with measurements, 85.1 % transfer overlap against 0, the apparatus census table |
| H5 | open — next | Station D through shared prefixes/cohorts; then the foreman path is deleted from live construction |
| P0–P5, M0–M3 | open | in order |

**The one complete gate**, `bash tools/gates.sh`, 2026-08-20 00:56:40 → 01:01:23 UTC, exit 0 —
**12 of 12**:

```text
PASS  tests              2598 passed, 0 failed, 19 ignored over 30 result lines; example targets type-checked
PASS  authored-levels    0 failures
PASS  named-paths · line-citations · claim-index
PASS  driver-catalog     261 drivers catalogued, 0 uncatalogued
PASS  output-manifest    recorded 61 drivers, present 61
PASS  closure-manifest   current: 62 return directories, 23 orphans
PASS  boundary-artifacts · typst · architecture-lint (242 files, 22,098 inherited) · document-law
12 passed, 0 failed
```

Deed H4 passed; proceeding to Deed H5.
