# The contraction is tiled, the scalar owner referees, and the obstruction is shape-conditional and measured

**Date:** 2026-08-19
**Kind:** construction return for **Deed H2** of the single-card plan — the exact tiled contraction
on the card, refereed by the unchanged scalar owner — with the equality matrix, the ten controls,
the launch-geometry candidate family from measured registers, the H1 receipts realized by the
geometry, the shape-conditional obstruction with its mechanism **measured** by Nsight Compute, four
conflicts between the design study and the tree (the tree governing), and what it hands H3.
**Truth status:** `established-bounded` for every measurement; `implemented-exact` for the nine new
kernel entries and the two laws; **Deed H2 PASSES on this tree** — exact equality everywhere, no
receiver regression, and the §8 obstruction clause honoured: **`section_contract` is not replaced**;
the tiled laws stand beside it as admitted alternatives whose profile is returned.
**Authority:** the single-card plan §4.2–4.4, §8 "Deed H2", §11; the design study (session
scratchpad, 788 lines — its derivations are restated here where load-bearing);
[H0](2026-08-19_THE_SCALAR_PATH_RETURNS_ITS_PROFILE_THE_CARD_IS_BUSY_ONE_TENTH_OF_THE_SPAN_AND_EVERY_SECTION_KERNEL_IS_BELOW_ONE_WAVE.md);
[H1](2026-08-19_THE_PARTITION_IS_TYPED_THE_REDUCTION_IS_A_JUNCTION_AND_THE_ADVERSARY_REFUTED_EIGHT_CLAIMS_BEFORE_THE_DEED_WAS_RECORDED.md).
**Position boundary:** [`CONSTRUCTION_STATE.md`](../../CONSTRUCTION_STATE.md) does not move.
**Owners:** nine kernel entries in `crates/holonic-engine/kernels/exact_resident_section.cu`
(`section_contract_tiled_{r1,r2,r4}_l{8,16,32}` wrappers, `section_contract_partial_*`,
`section_contract_join`; `KERNELS` 16 → 25); the laws and the candidate family in
`resident_law.rs` / `resident_section.rs`; two read-only accessors on `soma/mount`'s `Function`
(`num_regs`, `static_shared_bytes`).
**Driver:** `crates/holonic-engine/examples/the_contraction_is_tiled_and_the_scalar_owner_referees.rs`.
**Artifacts:** `output/the_contraction_is_tiled/` — `receipt.form` (542 lines), `equality.tsv`
(104 rows), `candidate-family.tsv` (1,281), `kernel-registers.tsv`, `nsys-kernel-sum.csv`,
`nsys-kernel-trace.csv`, and `ncu-shapes.tsv` (the C10 faces measured after the run).

---

## 0. Verdict

**The exact contraction is tiled and bit-equal to the scalar owner on the real admitted source, at
every tested shape, token extent, tile geometry, tree order and grain — 104 of 104 equality rows,
words and census both — under three referees** (the scalar kernel, the tiled kernels, and an
independent exact `i128` serial replay in the driver sharing no code with either, run wherever
`T·O·K ≤ 4·10⁷`, 12 of 16 readings, all equal). The one outward rounding sits after the whole K
reduction and nowhere else; the fixed lane tree's reversed control agrees on every value with the
per-node widths exhibited and different; a declared per-node overflow aperture **refuses on the
card** (`REFUSED_CARRIER`) where the scalar owner would wrap outside its admission — a stated
behavioural difference, exhibited by its fixture, never folded into the equality claim.

**And the §8 obstruction clause returned a shape-conditional obstruction, now with its mechanism
measured rather than inferred.** On narrow-output maps the tiled path is what the design predicted:
`q_proj` T=5 runs **5.3× faster** with the eligible warps per scheduler rising **0.53 → 2.10**,
achieved occupancy 33 % → 87 %, SM throughput 63 %; T=1 runs 20× faster. On the widest map the
tiled path is **0.91× — slower**: `gate_proj` T=5 saturates DRAM at **95.1 %** with the L2 hit rate
collapsed **83 % → 7 %** — the tile reduces *entering* traffic by the output-tile factor but streams
the wide map past L2, and at 10,240 output rows the map traffic is the wall — while the scalar
owner at 41 % occupancy rides an 83 % L2 hit. **`section_contract` therefore stands as the owner and
the independent referee; the tiled laws are admitted alternatives whose profile travels with them.**
Replacing the owner is not licensed by this deed and would need the shape-conditional reading to be
carried into any successor's admission (H3/H4 decide nothing here).

## 1. What equality means here, and the gap the material hid

Equality is bit-equality of **both interval endpoints and the census words** (refused, max octave,
max width, width sum, nonzero widths), per output coordinate, scalar against every tiled variant.
At the closure's grain 2⁻⁴⁸ every entering bf16 word places exactly, so `lo == hi` everywhere and
the interval sign rule (`w < 0` selects the opposite endpoints) is never *distinguished* by the
real material — an equality shown only there would be the §8 defect of a check whose material
cannot vary the property. **A fourth row per map at grain 2⁻⁸ closes it**: the same real words
enter as genuine enclosures (q_proj T=5: 12,345 entering coordinates with `lo < hi`, width sum
556,040) and every path is still bit-equal, split-K included; the swapped-sign-rule perturbation
differs there, enacted on the serial referee.

## 2. The controls (each with its perturbation)

C1 equality 104/104 (above) · C2 three further tile shapes bit-identical · C3 a **second tree in
the kernel** (ascending doubling offsets) bit-equal on values with the per-node widths exhibited
and permuted · C4 the four cancellation fixtures including one negative `w` in the tail — the
swapped sign rule differs on every one; the near-carrier fixture admitted at exactly 126 octaves
with peak accumulator 124 · C5 127 octaves refuses in shape by name; a node aperture of 3 refuses
**on the card** (`refused 0x1 = REFUSED_CARRIER`) where the scalar word reads `0x0` · C6 eight
nonmultiple tails (K = 2,559/2,561; O = 2,049; T = 3; K < lanes; K_t = 0; a split whose span does
not divide K) all equal · C7 the K-permutation `π(i) = (97i+13) mod 256` applied to **both** the map
columns and the entering rows (the rows permuted on the card through the standing
`section_permute_columns` law) is bit-equal, and the half-permutation control (map only) **differs**
— the control is not vacuous · C8 the per-entry PTX float baseline: all nine new entries carry
**zero** float tokens; the four standing kernels whose `rcp.approx.f32` is a compiler division seed
are unchanged and not convicted (the design's finding: a module-wide grep would convict four exact
kernels; the control is per-entry) · C9 registers measured three ways in agreement
(`cuFuncGetAttribute`, `ptxas -v`, nsys): tiled 40–64, join 34 with a 224-octet local rank stack, no
spills; the design's `38 + 8·T_t` estimate over-predicts on seven entries and **under-predicts on
one** (`partial_r1_l32`, 48 measured vs 46), so it is not even a one-sided bound — the measured
value re-derives the family · C10 above.

## 3. The candidate family, and what it is not

320 admitted candidates per shape from the device's own attributes and the **measured** registers;
the retained non-dominated set is **12 / 5 / 67 under the coarse / medium / fine declared axis
sets** — the set moves with the axes, which is the point: no "optimal block" exists, the apparatus
receiver retains candidates and the run's candidate is caller-declared and named in the receipt.
The scalar owner's 66.67 % theoretical occupancy reproduces H0's measured value exactly, validating
the resource equation against the tree. The module-wide `DerivedLaunch` minimum did not move (512,
pinned by `section_chronology` at 109 registers — the design derived it, the deed measured it);
every new wrapper carries `__launch_bounds__(512)` and a unit test asserts the invariant. No
opt-in shared memory was needed (widest staging 32,768 of 49,152 octets).

## 4. The H1 receipts realized by the geometry

The driver emits the `TilingReceipt` for the enacted output partition — **cells 2,560 = blocks
launched 2,560**, complete and disjoint by computation, zero non-immutable shared reads,
interchangeable — and the `ReductionReceipt` for one output coordinate's K junction built from the
**128-bit partials read back off the card**: leaf count 8 = the kernel's split factor, words agree
before rounding, span 3, peak node width 110 bits, the adjoint defect zero under the declared
metric with the bare-transpose defect nonzero under `diag(1,3)`.

## 5. Four conflicts with the design study — the tree governed

1. **`k_proj`/`v_proj` are `[512, 2560]`, not 256-wide** (measured from the container header); the
   design's wave figures for them were off by 2×. Split-K remains required and is enacted and equal.
2. **The K-complete lane tree cannot be certified by the H1 junction owner**: its leaves are strided
   index sets and `PartialTerm::inner` is a half-open region. The split-K partials are contiguous
   and are certified; the lane tree is carried by its written word, its depth and the on-card
   reversed control. Carried as a stated boundary (a strided-set partial region is an absent type
   H1 did not found; founding it is licensed only when a deed needs the certification).
3. **A rounding-law mismatch exhibited**: `DirectedRounding::Outward` in the reduction owner is
   away-from-zero per coordinate; the contraction's law is floor-below/ceil-above. Measured at one
   coordinate: kernel and CPU directed replay identical; the owner's outward differs by one grain on
   the positive lower endpoint. The receipt uses the kernel's own law and says so.
4. **A neighbouring law's a-priori bound does not read its material**: `shape_enter`'s bound is
   authored from the scale and grain alone, and a large-exponent bf16 population blows it. The
   driver closes the entering occurrence at the octaves computed from the words themselves;
   **reported, not repaired** — the repair belongs to the owner and is handed to H3 by name.

## 6. C10's faces, measured after the run

`ncu --kernel-name regex:section_contract --set full` under `sudo` on the driver's
`--profile-shapes` mode (12 launches, 40 passes each; the two launches per row agree to <1 %);
artifact `ncu-shapes.tsv`:

| shape | path | eligible/scheduler | achieved occ % | SM % | DRAM % | L1 hit % | L2 hit % | vs scalar |
|---|---|---|---|---|---|---|---|---|
| q_proj T=1 | scalar | 0.494 | 32.6 | 1.8 | 6.6 | 74.2 | 14.5 | 1.00 |
| q_proj T=1 | tiled | 0.417 | 52.5 | 28.8 | **80.3** | 28.2 | 8.3 | **0.050** |
| q_proj T=5 | scalar | 0.532 | 33.3 | 9.9 | 7.2 | 74.1 | 83.0 | 1.00 |
| q_proj T=5 | tiled | **2.099** | **87.3** | **63.0** | 35.3 | 15.6 | 84.2 | **0.190** |
| gate_proj T=5 | scalar | 0.362 | 41.1 | 25.0 | 18.8 | 70.4 | **84.3** | 1.00 |
| gate_proj T=5 | tiled | 0.568 | 98.6 | 34.0 | **95.1** | 29.0 | **7.2** | **1.094** |

The obstruction's mechanism is measured: on the wide map the tiled path converts an L2-riding
latency-bound kernel into a DRAM-saturated one. A later repair candidate (a W-tile staged through
shared memory or an output-tile shape that restores L2 reuse of the map) belongs to a later deed
and is named, not built.

## 7. Tests, ledger, and the epoch

`cargo test -p holonic-engine --lib -- resident_law resident_section contract_tiled` → **27
passed** (6 new, device-exercised); `tests/h1_adversary.rs` stayed green throughout (35);
`cargo check` clean; the driver built and run on the card (the GPU deed, with the full source
mounted map by map); nsys ran unprivileged on the shape profile; ncu under `sudo`, approved. Two
ledger rows changed by hand with the dispositions in the deed's report (trait-signature-inherited
`BTreeMap`/`Vec`, returned plural populations — the family, the retained set, the partials — and
seven clones of which two keep the tiled entailment welded to `Contract`'s and carry a named
reduction not taken because this deed may not modify the `Contract` law). The scalar kernel and the
`Contract` law are untouched at `HEAD`.

## 8. The station table

| deed | grade | decisive evidence |
|---|---|---|
| A–D | PASS (frozen) | their records |
| H0 | PASS | the profile record |
| H1 | PASS | the receipts record |
| **H2** | **PASS** | this record: 104/104 bit-equal under three referees; ten controls; the candidate family from measured registers; the obstruction returned shape-conditionally with measured mechanism; the scalar owner retained |
| H3 | open — next | reductions/census aggregation, receiver-dependent fusion; plus two named hand-offs: `shape_enter`'s authored bound, and the strided-partial certification absence |
| H4–H5, P0–P5, M0–M3 | open | in order |

**The one complete gate**, `bash tools/gates.sh`, 2026-08-19 22:44:52 → 22:49:06 UTC, exit 1 —
**11 of 12**; the one red was `authored-levels: 5 failures`, the four new constants of the deed
(three CUDA attribute selectors and the register-file allocation grain) standing undispositioned in
the registry. Each was dispositioned by hand — the selectors as `ABI` (the integer names a question
the device answers; the same disposition their eleven standing siblings carry) and
`REGISTER_GRAIN_PER_WARP = 256` as `ABI` with its derivation route stated (the CUDA occupancy API
would replace it with the device's own per-function answer once a mount accessor exists) — and the
named gate rerun alone: **`authored-levels` PASS (0 failures)**. The two scopes are reported
separately; nothing in code, kernel, driver or artifact changed between the readings.

```text
PASS  tests              2586 passed, 0 failed, 19 ignored over 30 result lines; example targets type-checked
FAIL  authored-levels    5 failures (four new constants undispositioned; dispositioned by hand; rerun alone: PASS)
PASS  named-paths        0 failures
PASS  line-citations     0 failures; 431 citations
PASS  claim-index        current
PASS  driver-catalog     258 drivers catalogued, 0 uncatalogued
PASS  output-manifest    recorded 59 drivers, present 59
PASS  closure-manifest   current: 60 return directories, 22 orphans
PASS  boundary-artifacts 3 bound
PASS  typst              10/10
PASS  architecture-lint  clean: 241 files, 22030 inherited occurrences, 0 retired
PASS  document-law       0 failures
11 passed, 1 failed: authored-levels   →   authored-levels rerun alone: PASS
```

Deed H2 passed; proceeding to Deed H3.
