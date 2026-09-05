# HNP4: the terminal receiver reads one row and preserves the complete successor

**Date:** 2026-09-05. **Phase:** HNP4, partial output-cost return.

## Returned boundary

[established-bounded; source-inspected] `NativeEmissionReadout::LastRow` restricts only the
exterior terminal receiver. `advance_cycle_readout_retained` executes the same complete native
operation, retains all terminal rows, applies the same local returns and preserves interruption
semantics. `operative_terminal::read_terminal_row` stitches each resident tile's final row using
`ResidentSurface::read_out_terminal_row` and the existing device-buffer subrange copy. There is
no additional projection buffer or device kernel. The redundant clone of the emitted host vector
also departed. Earlier public methods still request `Complete`.

[established-bounded; source-inspected] `HnaSession::{advance_native_readout,observe_native_readout}`
expose the receiver choice; `HnaTextApplication::step` requests `LastRow` and retains its ordinary
self-occurrence exactly as before. The emission identifies the projection and original row count.
Native rest/wire semantics do not change: the complete resident source is still serialized.
`transfer_census` exposes the existing instrument, not a second state or integrity registry.

## Actual-model return

[established-bounded; measured] On the standing RTX 4080 SUPER, the reference was HNP3's actual
cultivated `.local/artifacts/hnp3/checkpoint-01.hna`, followed by its first declared occurrence.
The new artifact `.local/artifacts/hnp4/readout-01.hna` was compared with the existing
`.local/artifacts/hnp3/expected-after-01.hna`. The projected output matched all 262,144 final-row
intervals, not just a selected address. The **entire decoded native rest was equal**, including
generation 5,100, factor extent 7,112, held field, chronology and numerical reuse state.

[established-bounded; measured] The productive projected cycle took 1,672 ms and transferred 4,194,304 terminal bytes.
Subsequent explicitly fixed-morphology same-word comparisons returned the same complete last-row
interval vector:

| Receiver | Warm-up status | Returned rows | Terminal egress bytes | Cycle ms |
|---|---|---:|---:|---:|
| Complete | First after the productive change | 14 | 58,720,256 | 1,610 |
| Complete | Warm | 14 | 58,720,256 | 285 |
| LastRow | Warm | 1 | 4,194,304 | 233 |
| Complete | Warm | 14 | 58,720,256 | 274 |

[definition] Cycle timing excludes cold model mount, artifact verification, input acquisition,
checkpoint serialization and process startup. These few fixed-occurrence observations are not
an end-to-end text throughput benchmark, a statistical latency distribution, an energy reading
or evidence of useful learning. All full device computation and retained storage remain; this
change specifically removes unnecessary host readback and copying.

## Verification and reproduction

[established-bounded; measured] The CUDA test
`terminal_row_readback_preserves_full_source_without_device_allocation` used non-point signed
intervals in a 3-by-2 source. It returned exactly the final two intervals, counted 32 egress bytes,
added no allocation or deed launch, and recovered the unchanged complete source afterward.
All 34 `holonics-hna` library tests passed. The actual-model control built and ran:

```sh
cargo build -p holonics-hna --example terminal_readout_hnp4
target/debug/examples/terminal_readout_hnp4 \
  .local/artifacts/hnp3/checkpoint-01.hna \
  .local/artifacts/hnp3/expected-after-01.hna \
  .local/artifacts/hnp4/readout-01.hna
```

[definition] Choose a new last path on repetition; publication never overwrites a prior artifact.
The fixed-morphology observations in this instrument answer receiver equivalence and cost only.
The [productive-learning counterexample](2026-09-05_HNP4_NATIVE_TEXT_CONTINUES_BUT_UNCHECKED_ADDITIVE_CULTIVATION_DESTROYS_THE_RETURN.md)
stands. HNP4 is not complete: stable founded development, complete application products, ordinary
later correction and the second genuinely different interaction remain required.
