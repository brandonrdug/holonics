# HIF5 first migration removed Athena from the generic native rest family

**Date:** 2026-08-31
**Truth status:** `implemented-exact` for the breaking neutral rename and schemas;
`established-bounded` with `measured` evidence for the complete affected examples and library
receivers.
**Construction effect:** first admitted HIF5 migration unit; HIF5 remains current.

[implemented-exact; source-inspected] The generic `AthenaNativeRest`, `AthenaNativePassage`,
`AthenaNativeBatchPassage`, `AthenaNativeConsequence`, and `AthenaNativeError` family was removed.
The sole types are now `NativeEcologyRest`, `NativeConductPassage`,
`NativeConductBatchPassage`, `NativeConductConsequence`, and `NativeEcologyError`.

[implemented-exact; source-inspected] Every consumer in `soma/life` migrated in one breaking change.
No compatibility alias, legacy decoder, or dual schema was added. The generic rest and conduct
wires now use `soma-life.native-ecology-rest.v1`,
`soma-life.native-conduct-passage.v1`, and
`soma-life.native-conduct-batch-passage.v1`; historical output files must be rebuilt through the
new owner when later phases require them.

[implemented-exact; source-inspected] The owner comments and refusals now describe native ecology
rather than claiming every generic spool realization is Athena. Product-specific cultivated,
sensory, and application names were not mechanically erased; their migration or deletion requires
owner-by-owner review in the remaining HIF5 work.

[established-bounded; measured] `cargo check -p life --lib --examples` passed after the breaking
migration. The full `life` library returned 491 passed, zero failed, and 15 ignored tests.
Source-shape reports 636 live files, 447 inherited baselines, and zero violations.

[open] Athena still qualifies product-specific cultivation, laboratory, membrane, sensory,
receiver, and application wrappers. HIF5 remains current until every generic owner is neutral,
duplicate rest/generation/cultivation families are dispositioned, and the public-owner/hotspot
review passes.
