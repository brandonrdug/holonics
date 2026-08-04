# R4 continuing-body and returned-event lifecycle receipt

**Truth status:** `established-bounded`.

**Evidence:** `implemented-exact` for the move-only body, unique continuation, pending deed,
typed exterior return, complete staged delta, body-atomic commit/refusal, and native rest/remount;
`computational-witness` for the returned card deed and bounded adversarial interruption family.
Apparatus identity is separately `measured` in
[`provenance/HARDWARE_RECEIPT.txt`](../provenance/HARDWARE_RECEIPT.txt).

**Aperture:** one continuing body with four exact local regions, one outstanding event, one typed
return, one changed region, one rest/remount passage, and a fixed adversarial family covering
second-open, foreign, stale, double-return, capacity-refusal, and four interruption boundaries.
This receipt does not establish an unbounded transaction theorem, concurrent causal current, or
any R5-and-later deed.

## Construction tuple

| Field | R4 standing |
|---|---|
| Source owners | one move-only `body::continuing_body`, its unique `body::linear_continuation`, one move-only `event::live_pending`, and one move-only `event::live_delta`; apparatus owns only allocation, exterior crossing, durable serialized rest, and inspection |
| Port types | owner-minted outbound event and expected-return identities, exact returned payload, staged read/change/incidence/morphology/current/stress/obstruction/resource/lineage testimony, and current-schema native rest record |
| Event occurrence | `open_body` creates the unique pending deed; the typed exterior return crosses back to the resident card; `resume_commit_rest` validates and commits one region; the old owner departs; `remount_body` founds the same successor from native rest |
| Predecessor identity | Git `2c9006df74c5701b4c35ba1dd0d5b5851c86bfc5` and body head `200000000` |
| Local constitutive law | a return must match owner, predecessor event, expected port, and lineage; the law stages every delta field before a single preflighted body commit; success advances head/capability/lineage exactly once and refusal restores the same unique capability without mutation |
| Receiver question | whether the region is unchanged before the valid return, changes exactly once afterward, survives native rest/remount without source replay, and preserves predecessor/capability standing across every declared refusal/interruption boundary |
| Returned consequence | successor head `200000001`, one region morphology changed to `37`, complete delta testimony, exact remount equality, zero source replay, classified invalid returns, and preserved refusal/interruption standing |
| Open alternatives | GPU-resident causal current, concurrent frontier reservation, compositional quiescence, adaptive morphology, learning, exterior mathematical production, and every R5-and-later deed remain absent |

## Ownership, return, and commit

`body::continuing_body`, `body::linear_continuation`, `event::live_pending`, and
`event::live_delta` reject copying. Opening consumes the body's sole continuation into the pending
deed, so a second open cannot acquire another capability. A rejected return consumes that pending
attempt but yields exactly one recovered continuation; no rollback clone exists.

The real exterior passage is a device-to-host outbound occurrence followed by a host-to-device
typed return. The host routes the declared return payload but does not select a semantic phase or
perform the local law. On the card, the law validates owner, predecessor occurrence, expected
return port, and lineage before staging the complete delta. `continuing_body::commit` preflights
predecessor, capability, region, and exact integer capacity before mutating any owned field.
Success publishes the successor once. Refusal returns the same capability and preserves the exact
predecessor.

The committed region reports read support `4`, change support `4`, morphology delta `7`, and
successor morphology `37`. The other three regions remain byte-for-byte unchanged. The returned
rest record carries the successor's regions, head, capability, and lineage. Its integrity fold is
only an apparatus admission check; it is neither semantic identity nor an equality oracle. The
old body allocation and input/pending/delta/rest allocations depart before a freshly allocated
body is mounted from that record. No source material is replayed.

## Adversarial and interruption return

The fixed resident adversarial kernel returns distinct `second_open`, `foreign_return`,
`stale_return`, `double_return`, and `capacity_refusal` states. Capacity refusal preserves both
predecessor and capability. Snapshots at the declared boundaries—after open, after validation,
after staging, and after commit—return predecessor standing for the first three and the complete
successor for the last. No boundary exposes a partial body mutation.

This is a bounded exact construction over the named body and adversarial family. It does not claim
arbitrary-instruction crash consistency or exterior file-system atomicity.

## Returned device artifact

The complete decoded artifact is `build/r4/receipts/R4_BODY_LIFECYCLE_DEED.txt`; its final SHA-256
is `7ec46862a8077b6aea9d61596a597f18f72ae61d84e469f3d94901aaddf6f103`. Its summary is:

```text
truth_status=established-bounded
evidence=implemented-exact,computational-witness
program=r4_open+resume_commit_rest+remount+adversarial.sm_89
device_compute_capability=8.9
kernel_launches=4
launched_threads=4
bytes_to_device=248
bytes_from_device=1296
resident_body_bytes=1032
predecessor_head=200000000
outbound_event=200000000
outbound_expected_return_port=202000001
return_state=0
delta_read_support=4
delta_change_support=4
delta_morphology=7
successor_head=200000001
successor_region_morphology=37
rest_integrity=5691333109040632415
remount_equal=1
source_replays=0
second_open_state=1
foreign_return_state=3
stale_return_state=2
double_return_state=5
capacity_commit_state=4
capacity_predecessor_preserved=1
capacity_capability_restored=1
interruption_predecessor_0=1
interruption_predecessor_1=1
interruption_predecessor_2=1
interruption_successor=1
verification_failures=0
```

## Artifact hashes

Two independent pinned Ninja build directories return identical bytes for the normalized deed
executable, both PTX/cubin pairs, and decoded semantic deed artifact at the same source aperture.

The final graded source aperture SHA-256 is `035caac110258875c9cd3d6e276ccec4b345a69938d72952d4329e2ac728b386`.

| Artifact | SHA-256 |
|---|---|
| normalized body-lifecycle deed executable | `2d5138057a40bbb0a3f9a0a63286308fa211863d4f7c6b6c15a89c68c1ea2d9b` |
| lifecycle PTX | `fe6cea0f31e1f5a7b11821341087a3861c120e53b7e3525ddc61fe7d5c3091fd` |
| lifecycle cubin | `831acf4ba46b81e7d1705294a05a6906a9e50d774eca4f6bccec912f7e344915` |
| adversarial PTX | `c89302c4fc5b874a2aad905aca6c3baf596dc20f20ebbb9671654926d7221bf1` |
| adversarial cubin | `164400d91414801fd18f3e6a5b6808c530fa7102b93d60f488a65c7dd45bcb25` |
| complete decoded body-lifecycle artifact | `7ec46862a8077b6aea9d61596a597f18f72ae61d84e469f3d94901aaddf6f103` |

## Gate returns

- Architecture, owner-DAG, source-size, no-float, no-compatibility, copy-ownership, and build audits
  pass before and after construction.
- Both release build directories pass all 18 CTest gates. The executable, both PTX/cubin pairs,
  and decoded deed artifact are byte-identical.
- The independent verifier checks exact pre/post/remount equality, single-region change, complete
  delta testimony, typed-return classifications, capability recovery, and all declared
  interruption snapshots.
- The four-kernel card deed passes NVIDIA `compute-sanitizer` memcheck and initcheck with zero
  errors.
- Host conformance passes AddressSanitizer and UndefinedBehaviorSanitizer with leak detection
  enabled.
- Clang 22's static analyzer reports no diagnostics over the project-owned deed, conformance,
  verifier, artifact, and included production-law aperture.
- PTX and final SASS scans find no floating type, conversion, arithmetic, comparison, or special
  function instruction in either R4 device artifact.

## Apparatus and resource boundary

The CPU allocates card storage, carries one exact outbound/return crossing, persists the returned
native rest bytes, releases the departed owner, remounts fresh storage, and independently inspects
the bounded witness. It neither applies the constitutive law nor replays a body algorithm. GPU
kernels own open, validation, delta formation, commit/refusal, rest formation, remount, and the
adversarial boundary deed. Transfer sizes, allocation addresses, launch counts, and the rest
integrity fold remain apparatus testimony and do not enter body identity or semantic equality.
