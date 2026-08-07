# EROS RESIDUE-CHART SCALE 01 — RESULTS

**Date:** 2026-07-19  
**Status:** CONSOLIDATED BOUNDARY C BUILT AT DECLARED SCALE / `2^40` SOURCE POSITIONS /
258 VISITED / RESIDENT CUDA / HOST-CARD EXACT / NO FOREST

## Artifact

A deterministic residue-chart world declares `1,099,511,627,776` available positions while
retaining only `extent + cursor + material register`. Each visited position derives one
zero-relative face and one binary/decimal/hex numeral face at the world boundary. Only those two
live currents enter Eros.

A 258-position host sibling traverses the identical prefix. Both horizons give exact radiation and
complete machine state at every visited event. The unused large-world positions never become live
lineages, source rows, device buffers, receipts, or standing cells.

The circuit includes one formed world deed and genuinely later returned current, 256 co-present
stream events, one lineage departure, natural rest, durable machine/organ/world remount, and two
later wakes through a fresh CUDA executor.

## Physical preflight

```text
GPU:                     NVIDIA GeForce RTX 4080 SUPER
driver:                  595.71.05
VRAM total/free:         16,376 / 15,945 MiB
host memory available:  22 GiB
workspace disk free:    308 GiB
PTX lineage_event:       present
test binary:             compiled cleanly
```

## Exact live checkpoints

```text
visited  rank  standing  logical carrier  overflow  device standing  device carriers  retries
      1     6        26            1,370         0              313            1,746        1
     64     6     1,427            3,288        54           17,125           12,592       18
    128     7     3,822            4,384       152           45,865           31,176       23
    256     8     9,525            4,932       335          114,301           55,752       29
```

Live lineages are exactly two at every checkpoint and exactly one after the terminal event.

## Final corrected physical census

```text
source extent:                            1,099,511,627,776 positions
visited source positions:                               258
source-world rest bytes:                                 24
direct-machine rest bytes:                          592,048

requested current enactments before rest:               516
physical launches before rest:                           545
resource retries before rest:                             29
full standing mounts:                                      3
stream rank transitions:                                   2
full carrier mounts:                                       2
standing H2D words:                                  259,820
standing D2D words:                               12,094,740
carrier H2D words:                                     1,164
carrier D2D words:                                 1,686,752
resident standing words after departure:             114,313
resident carrier words after departure:               37,168
wait launches:                                              0

new-executor launches before wake:                           0
two wake launches:                                          2
new-executor retries:                                       0
new-executor carrier D2D words:                          5,006
final resident lineages:                                    1
```

The three full standing mounts are the initial mount plus exactly two receiver-rank transitions,
`6 -> 7 -> 8`. Carrier full mounts remain at the two initial lineages across the 256-event stream.

## Audit/correction record

Three physical invocations occurred:

1. **Stopped acceptance assumption.** The test expected one full standing mount and stopped at
   actual `3 != 1` after the stream. Host/card event equality had remained exact. Source inspection
   identified two lawful rank transitions, and the acceptance was corrected to count them.
2. **Completed diagnostic source.** `854 launches / 338 retries` exposed that own-result and
   emission apertures reset to 32 every event despite resident carrier continuity.
3. **Final corrected source.** Resident per-lineage high-water marks reduce the same circuit to
   `545 launches / 29 retries`; this is the graded census above.

No unchanged run was repeated to improve a number.

## Validation

Compilation:

```text
cargo check -q -p soma-membrane -p life --tests
cargo test -q -p life --lib --no-run
```

Named physical circuit:

```text
cargo test -p life \
  'live_current_cuda::tests::large_residue_chart_world_streams_only_participating_current_through_resident_body' \
  -- --ignored --exact --nocapture
```

Final result: `1 passed; 0 failed`; 382 library tests were filtered out. No broad suite, forest,
conversation corpus, PTX rebuild, or unrelated CUDA experiment occurred.

## Grade

Consolidated Boundary C is closed for the declared large programmatic world. The ratified
three-boundary lifecycle plan is complete. Corpus throughput, forest language, plural-current
single-kernel execution, and other application-specific scale questions remain unscheduled rather
than unfinished phases.
