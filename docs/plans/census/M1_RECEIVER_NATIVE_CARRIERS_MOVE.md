# M1 receiver and native quotient carriers

Refs #69.

## Packet 1: six canonical carriers

The main `holonics` library owns the receiver/native carriers at `holonics::receiver::native`:

- `InputId`, `ReceiverId`, and `Observation`;
- `NativeStateId`, `NativeTransport`, and `ReceiverFactor`.

Their field shapes, derives, and serde representation are unchanged. `Observation` is an exact
opaque receiver key: ordering supports canonical partition grouping and device-key use, but no
receiver law treats that ordering as magnitude. `NativeStateId` is only the canonical address of a
conduct block. The Rust compression engine still owns source-qualified quotient discovery,
including assignments, source fibres, separating witnesses, and shortest separators. The carriers
do not store or reconstruct those witnesses.

The formal naturality peer is
`formal/elementary-holonics/ElementaryHolonics/Foundation/ReceiverHistoryCompression.lean`.
Its ordered-word theorem states the quotient/generator commuting law. The carriers are representation
types for the finite action and receiver factors; they do not themselves certify that a source
quotient is natural. That certificate remains the engine discovery result.

At carrier-only tip `2a4251c2`, the locked workspace all-target check passed for this six-type move,
including engine, life, HNA, workspace and workbench. The initial checks found and fixed the
compression child's direct import, the workspace crate's missing direct `holonics` dependency, and
two workbench type-import sites before that gate passed. This receipt says nothing about the
separate native-rest owner move below.

## Packet 2: `GeneratorNativeRest`

The validated `GeneratorNativeRest`, `NativeGenerator`, schema constant, errors, and
validation/conduct/decode operations now also belong to `holonics::receiver::native`. The move
preserves schema `holonics.m3.generator-native-rest.v1`, serde field names and order, derives, and
behavior. Its tests move with the implementation. `serde_json` is a runtime dependency of the main
library because reading and writing this rest are main-library operations.

This rest stores only the induced finite action and declared receiver image. Source populations,
quotient assignments, source representatives, reconstruction fibres, shortest separators, foreign
tensors, and source paths remain in the engine's discovery evidence. The engine does not export a
forwarding path for the moved types. Life callers import the main library directly; HNA and
workspace code continue through their existing consumers and direct dependencies.

Import census finds no remaining `generator_native_rest` module paths or engine module declaration.
Rust source parsing and `git diff --check` pass for this packet. The locked main-library
`receiver::native::tests` gate passed both source-detached rest tests: current wire roundtrip and
ordered conduct, plus partial-generator refusal. The locked workspace all-target check passed in
4m24s after stacking on the six-type carrier packet, including engine, CUDA, life, HNA, workspace
and applications. The move changes no CUDA kernel law and makes no card or HNN outcome claim.
