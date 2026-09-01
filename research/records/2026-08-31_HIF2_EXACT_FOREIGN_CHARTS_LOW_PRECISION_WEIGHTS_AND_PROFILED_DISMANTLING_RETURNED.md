# HIF2 exact foreign charts, low-precision weights, and profiled dismantling returned

**Date:** 2026-08-31
**Truth status:** `implemented-exact` for the lossless JSON/ONNX charts, packed dtype manifestation,
exact low-precision codewords, and profiled dismantling return; `established-bounded` with
`source-inspected` and `measured` evidence for vendor/config/index runs and package receivers.
**Construction effect:** HIF2 passed; the roadmap frontier advances to HIF3.

## Lossless exterior charts

[implemented-exact; source-inspected] `ForeignConfigurationChart` retains the complete raw JSON
occurrence and every root value span without interpreting vendor fields as native roles. Full JSON
syntax is validated, and duplicate keys are refused recursively through nested objects and arrays
rather than overwritten.

[implemented-exact; source-inspected] `ShardedWeightIndexChart` retains raw index bytes, metadata,
declared total size, exact tensor-to-shard mapping, and declaration order. Reconciliation with
manifested Safetensors containers returns missing shards, missing tensors, refused indexed tensors,
and unindexed manifested tensors as separate populations.

[implemented-exact; source-inspected] `ForeignOnnxChart` reads the ONNX protobuf byte occurrence
without a foreign runtime. It projects IR/model/producer fields, opsets, graph, ordered nodes,
inputs/outputs, initializers, dtype and dimensions, inline or external tensor storage, metadata,
functions, training-information population, device-configuration population, and exact ranges for
every known or unknown protobuf field. Duplicate singular fields, malformed varints, missing
operator sets, repeated declarations, and malformed external tensors refuse by name.

## Exact low-precision intake

[implemented-exact; source-inspected] `ForeignDtype` now manifests the contemporary Safetensors
FP8, FP6, FP4, FNUZ, E8M0, complex, integer, and packed sub-octet vocabulary by bit width. Packed
extent is `ceil(elements * bits / 8)`; sub-octet material is no longer rejected merely because one
element occupies less than one byte. Element-aligned byte reading still refuses a packed request
which lacks a declared bit-slice operation.

[implemented-exact; source-inspected] `decode_low_precision` and
`decode_packed_low_precision` return exact rational values for admitted FP4, FP6, FP8, E8M0, and
sub-byte integer codewords. Infinity and NaN remain explicit nonfinite faces. A supplied richer
source returns its exact rational residual; without a source/quantization law, the stored value is
exact while its source preimage remains `OpenQuantizationLaw`.

[implemented-exact; source-inspected] The former `foreign_map.rs` coverage owner was split into
`foreign_map/coverage.rs`. This reduced the existing hotspot while keeping admission, transport,
and load-bearing coverage as one owner; no source-shape baseline was increased.

## Profiled one-way dismantling

[implemented-exact; source-inspected] `profile_dismantling_return` accepts any neutral
`DismantlingBoundaryReturn` whose productive lane is a `NativeSpoolBundle`. It borrows the intrinsic
profile only from that productive lane. Cold realization testimony and insufficiency remain
separate and cannot enter the profile or native conduct.

[established-bounded; measured] Renaming a hybrid/expert/quantization vendor configuration changed
the exterior chart and moved no byte or field of the native profile. The profile retains the exact
original thread owner by pointer identity.

## Live resource measurements

[established-bounded; source-inspected; measured] The same HIF2 example parsed the supplied live
resources without per-model code:

- GLM-5.3-Flash configuration: 69,416 octets and 13 root fields;
- GLM-5.3-Flash shard index: 8,406,613 octets, 76,108 tensor mappings, 62 shards, and
  328,326,771,576 declared weight octets;
- DeepSeek-V4-Flash configuration: 1,888 octets and 52 root fields;
- DeepSeek inference configuration: 1,162 octets and 38 root fields;
- Qwen3.8-Flash-Next configuration: 4,745 octets and 11 root fields; and
- Qwen3.8-27B configuration: 4,312 octets and 11 root fields.

The example reports source names as exterior and has no callable foreign executor.

## Receivers and boundary

[established-bounded; measured] Seven foreign JSON/ONNX controls, four exact low-precision controls,
packed Safetensors manifestation, configuration-renaming invariance, and productive-lane profiling
passed. The complete `holonic-engine` suite returned 1,998 passed, zero failed, and 32 ignored tests;
`life` and every engine example type-checked. Source-shape reports 634 live files, 447 inherited
baselines, and zero violations.

[open] The neutral package now receives and dismantles foreign material, but the outward inference
cycle remains distributed across recurrence, membrane, radiation, world return, and generated
surface owners. HIF3 owns one packaged circulation and generation boundary.
