# M1 receiver and native quotient carriers

Refs #69.

This cut gives the main `holonics` library one canonical type identity for the receiver and
source-detached native-action carriers, at `holonics::receiver::native`:

- `InputId`, `ReceiverId`, and `Observation`;
- `NativeStateId`, `NativeTransport`, and `ReceiverFactor`.

Their field shapes, derives, and serde representation are unchanged. `Observation` is an exact
opaque receiver key: ordering supports canonical partition grouping and device-key use, but no
receiver law treats that ordering as magnitude. `NativeStateId` is only the canonical address of a
conduct block. The Rust compression engine still owns source-qualified quotient discovery,
including assignments, source fibres, separating witnesses and shortest separators. This module
does not store or reconstruct those witnesses.

The formal naturality peer is
`formal/elementary-holonics/ElementaryHolonics/Foundation/ReceiverHistoryCompression.lean`.
Its ordered-word theorem states the quotient/generator commuting law. The Rust carriers are
representation types for the finite action and receiver factors; they do not themselves certify
that a source quotient is natural. That certificate remains the engine discovery result.

`GeneratorNativeRest` remains under the engine owner at this commit boundary and moves in the next
owner commit. The source schema and field layout are unaffected by this carrier move.

Import census: all in-repository Rust imports and fully-qualified type references to the six moved
types now use `holonics::receiver::native`; no forwarding exports remain in the engine compression
modules. Rust source parsing was checked with `rustfmt --emit stdout` on each changed Rust file.
The locked `cargo check -j2 --workspace --all-targets` passed on the complete stacked carrier cut,
including engine, life, HNA, workspace and workbench. During review, the first compile exposed an
implicit sibling-module import in `receiver_history_compression/compression.rs`; the next reached
the missing direct `holonics` dependency in `holonics-workspace`; the third reached two workbench
imports outside `crates/`. Those edges were fixed in separate commits before the final passing
gate. The moved carriers preserve their derives, field shape and serde representation; this gate
does not claim a behavioral HNN or CUDA card result.
