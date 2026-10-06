# The single-hole response owner is decomposed without dropping its closure

October 6, 2026. Refs #73, #62, #63. Source-only decomposition on base
`0e4f107849c8c3799bf597db1ca0ba0941133b67`; isolated branch
`codex/single-hole-formal-decomposed`. The production/runtime source and other formal owners remain
frozen.

[prepared; compiler and kernel acceptance pending] The previous full-owner request reached the
Lean compiler but exited `124` before emitting any of its thirteen axiom queries. The immutable
receipt is
[`native-validation-single-hole-formal-incomplete-v1`](receipts/pair-output-learning-20261006/native-validation-single-hole-formal-incomplete-v1/VALIDATION.json);
its sealed validation bytes have SHA-256
`8051e44fdba7267eaf14df8d3cf21ce5b5e6986cd8bd86d3af94743b13ceff5a`. The full source submitted
there had SHA-256
`6206a8aca280331d6aaba9726af98e2d644074ddb7d4950f50a086b9940ba83d`.

The retained stdout reports the compiler phase at `17,147,946,185 ns` (`5 × 37 × 92691601`),
exit `124`, with empty stderr and no selector output. The outer receipt records `19,028,357,029 ns`
wall time (`11² × 41 × 137 × 27997`), `9,369,328,000 ns` aggregate CPU
(`2⁷ × 5³ × 251 × 2333`), and a `4,294,967,296`-byte group peak (`2³²`). Memory `max`
increased by 5,138 (`2 × 7 × 367`); `oom` and `oom_kill` stayed zero. These are measurements of
one combined source owner. The full validation JSON, factored measurements, exact stdout/stderr,
failure, provider-provenance and import-preparation receipts are copied into this branch at
[`native-validation-single-hole-formal-incomplete-v1`](receipts/pair-output-learning-20261006/native-validation-single-hole-formal-incomplete-v1/).
They do not identify a declaration-level hot spot, and they do not measure the cost of any new
module. The decomposition tests the hypothesis that bounded owners at actual dependency seams can
complete within the queue's existing measured policy. It claims no compile-cost reduction or
successful elaboration. No deadline or resource limit was raised.

The existing provider-provenance receipt verified 141 current imports and the ordered import
parts; the import-preparation stage sealed 5,027 modules and 30,494 bound paths without launching
the compiler. Those accepted provider pins and their dependency order remain the input. No provider
rebuild is requested. The failure and provider receipts, stdout/stderr, input pins, source hashes,
selector sets, and acceptance order are preserved in the sealed
[queue packet](receipts/pair-output-learning-20261006/single-hole-formal-decomposition-20261006/QUEUE_REQUEST.v1.json)
(SHA-256 `05cf500138bbf5bcd42d86f034468f1f0e72dcd52b9e285c4a39e8ef95c84eea`). The packet prepares
work for the sole queue; it grants no launch authorization and has no invented compile projection. Its
acceptance order retains six owner query blocks, facade selectors 13, the original independent
`SingleHoleResponseAudit` selectors 13, the existing `SourceReceiverReturn` selectors 9, then its
original independent audit selectors 9. Both audit sources and the unchanged dependent importer
bytes are preserved in the receipt; integration acceptance consumes the coordinator-sealed overlay.

## Full owner map

The public module remains `Holonics.HNN.SingleHoleResponse`; its root file is now only the stable
facade. Six narrow modules follow the dependencies already present in the proof:

| Owner module | Preserved declarations and consuming role |
|---|---|
| `SingleHoleResponse.SourceExpansion` | Constructive first-port and distinct-endpoint, edge-indexed bilinear pair expansion; full `ν(card Station)` and per-edge `ν(card Station-offset)` normalization. Owns the four source expansion selectors. It restores the original `open scoped BigOperators` context and imports explicit finite-sum and `LinearMap` owners alongside `Mathlib.Tactic.Abel`. |
| `SingleHoleResponse.LoadedWord` | `SourceResponseShape`, the absolute family `loadedOp T res h (openedAt+t)`, and full-state additive trajectory through that tick-indexed family. Owns `absoluteLoaded_response_add`. |
| `SingleHoleResponse.NormalizedOpening` | Derives fixed anchor plus the same-label response from the constructive normalized source expansion and the retained interior/source-injection opening. Owns `openedState_from_normalized_source`. |
| `SingleHoleResponse.ReceivingResponse` | Consumes the opening split through the linear receiver. Owns `loadedReceiving_response`. |
| `SingleHoleResponse.GrainRelease` | Keeps the explicit grain-face map external, certifies exact maxima, proves finite leader-union soundness, and consumes the existing holding law at tolerance zero. Owns the five leader/release selectors. |
| `SingleHoleResponse.ComposedConsumer` | The end-to-end normalized source → opening → absolute loaded trajectory → receiving map → grain face → singleton leader union → holding-law theorem. Owns `normalizedSource_loadedWord_grain_singleton_release`. |

The theorem declarations, proof bodies and section variable contexts were compared against the
frozen source: the primary's static comparison found 39 declarations before and 39 after, with no
missing, added, or duplicate declaration names and identical comment-stripped,
whitespace-normalized declaration statements and proof bodies. The root facade retains all
thirteen original `#print axioms` commands byte-for-byte and in order. Each component also has its
own complete query block for the queued per-owner check. These are source-preservation checks, not
Lean type checking or kernel receipts.

The public importer `SourceReceiverReturn` is not added to the Lean source tree and remains tied to
its separate base `8ab22667618271eca057fb460f1d062647e5b331`; its immutable receipt snapshot has SHA-256
`294df662d9a7dff20e4540f0fc643e0a00081fbae49d471c4f146dc1c5d9bc53`. The packet retains its nine
existing selector names as a downstream importer acceptance after the coordinator seals the
integration overlay, followed by its original independent audit with source/object/lookup matching.
It does not silently omit or rewrite that consumer.

## Acceptance still pending

The queue packet's fixed order is: compile each of the six owners once in dependency order with its
own full axiom query block; compile the public facade and require all thirteen original selectors;
then compile the sealed `SourceReceiverReturn` importer and require its nine selectors, followed by
its independent nine-query audit with source/object/lookup matching. The sole queue must project each
run from its authorized measurements under the existing caps before launch.
A failure remains incomplete; no larger limit, repeated unchanged full-owner attempt, or source
weakening substitutes for acceptance.

The mathematical boundaries remain those of the original full owner. The shared missing class
fills the first population and every incident ordered pair; each edge retains its own bilinear
kernel and phase/lift map. The actual opened source equation is derived from that expansion, then
the fixed interior and storage-only response share the actual absolute loaded tick family and full
state. The concrete Rust rational populations, station/offset encoder, source injection and actual
`GrainCell` chart still owe their #62 instantiation bridges. A singleton model leader union remains
model constancy for compatible completions at the declared receiver grain, not recovery of erased
truth or a useful untouched-request result.

The computational object is the helical pair interaction. This consumer touches helix, pair,
receiver faces and placement, and tube; cell holonomy and tower thread stay attached. The split
keeps the recorded failure modes in view: it preserves shared-label cross terms and distinct pair
edges, absolute pump time and full state, explicit grain mapping, and the actual receiver release
law. It adds no axiom, `sorry`, `native_decide`, candidate generator, or native source change.

The coordinator integrated this prepared split on the isolated HNN branch as
`29f0ba2b075508e0e03ebd1dcc72a1e962bb44c4`, following the source-return borrow repair. The only
atlas conflict was resolved by replacing this existing owner row and preserving every other row,
including both source-return consumers. The [integration receipt](receipts/pair-output-learning-20261006/single-hole-formal-integration-20261006/INTEGRATION.v1.json)
compares all 39 declarations and all thirteen facade selectors against the unsplit source. The
combined [local source manifest](receipts/pair-output-learning-20261006/single-hole-formal-integration-20261006/LOCAL_SOURCE_CLOSURE.v1.json)
contains 148 modules for the facade and 150 for the downstream source-return consumer: 143 old
provider/consumer files remain byte-identical, only the old facade changed, and six owners were
added. SourceReceiverReturn and both independent audits retain their original bytes.

The authoritative [combined queue request](receipts/pair-output-learning-20261006/single-hole-formal-integration-20261006/QUEUE_REQUEST.v2.json)
seals those inputs and exact candidate commands at the integrated pin. The prepared worker packet
above remains its historical source contract; its whole atlas-file hash does not replace the
integration branch's other owned rows. The sole queue still owns actual toolchain, ordered lookup,
provider/object, cache, fixed measured projection and lease admission. No compiler or native job
was started by either source owner, and no limit was raised.
