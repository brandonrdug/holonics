# AAC4 opaque versioned circulation ABI returned direct and diffusive equality

**Date:** 2026-09-01
**Truth status:** `established-bounded` for the ABI over its declared in-process handle and message
family.
**Evidence:** `implemented-exact`, `source-inspected`, `process-audit`, and `measured`.
**Construction effect:** AAC4 passed; AAC5 becomes the sole current deed.

## Returned boundary

[established-bounded; implemented-exact] The new exterior crate `soma/circulation-abi` builds as
both `rlib` and `cdylib`. Its only C layout is `HolonicsAbiBytes { ptr, len, capacity }`; all
circulation requests and replies are versioned, length-delimited `org.holonics.circulation-abi.v1`
messages. Rust structs, trait objects, morphology internals, filesystem paths, source/model names,
and foreign executors never cross the C boundary.

[established-bounded; implemented-exact] The message family returns open, remount, conduct,
continue, exterior return staging, commit, decline, snapshot, exact diffusion, and close over
opaque `u64` process handles. The handle table owns only session lifetimes. It does not resolve a
model, law, receiver, codec, or semantic route. Invalid handles, malformed schema/message,
configuration refusal, conduct refusal, stale boundary, false successor, nonlater return, commit,
and snapshot failures are distinct dispositions.

[established-bounded; implemented-exact] Consuming commit and decline operations first take an
exact session snapshot. On refusal they remount that predecessor before returning the error, so a
failed ABI mutation cannot lose the continuing ecology. No runtime ecology is cloned for rollback.

[counterexample; implemented-exact] The first diffusion-message control exposed that JSON object
keys cannot faithfully round-trip `NativeStateId`, `EventId`, and `CurrentNodeId` newtypes: JSON
presented them as strings while the derived decoder expected numeric values. The wire was narrowed
to ordered pair populations for every exact map, with duplicate-key refusal. The complete ABI
diffusion reply likewise uses pair populations while retaining the full balance, current,
boundary-transfer certificate, lineage, and reconstruction testimony. No string-to-address
coercion or compatibility decoder was added.

## Receipts

[established-bounded; process-audit] The crate check

```text
timeout 180s cargo check -p holonics-circulation-abi
```

returned exit `0` in 8.56 seconds after the initial serde/import errors were corrected.

[established-bounded; process-audit; measured] The final focused command

```text
timeout 180s cargo test -p holonics-circulation-abi --lib
```

returned exit `0` in 2.90 seconds: three passed, zero failed. The controls establish:

- structural equality between direct Rust and ABI conduct, actual continuation, and exact
  diffusive boundary returns;
- open, return, commit to generation 1, snapshot, close, remount, later conduct, decline, and close;
- invalid-handle refusal after close; and
- allocation, inspection, and exact release of one exported length-delimited FFI response.

## Boundary

[open] The ABI is an exterior apparatus, not an Athena product. AAC5 owns the first independent
application crate, its named product configuration, thin ports/receivers/experiment composition,
and one dynamically cultivated resumable alpha package.
