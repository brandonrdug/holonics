# R2 owner-native structure receipt

**Truth status:** `established-bounded`.

**Evidence:** `implemented-exact` for the admitted arena, incidence, traversal, path, and delta
aperture, with `computational-witness` for the ten returned finite complexes. Apparatus identity is
separately `measured` in
[`provenance/HARDWARE_RECEIPT.txt`](../provenance/HARDWARE_RECEIPT.txt).

**Aperture:** per resident complex, at most 16 cells, 48 sparse oriented incidences, and 16
persistent path nodes. Ten complexes cover empty, singular, interval, triangle, disconnected,
three-dimensional, multiplicity, append success/refusal, admission refusal, departure success,
and departure obstruction. This receipt does not establish an unbounded complex theorem or a live
continuing body.

## Construction tuple

| Field | R2 standing |
|---|---|
| Source owners | the admitted `exact` owner composed into one move-only `structure::resident_complex` owner per case; `apparatus` owns only device allocation/crossing |
| Port types | bounded encoded views, admission receipt, support certificate, structural-delta receipt, and complete structure output |
| Event occurrence | owner-local admission in `r2_admit_complex_kernel`, retained device residence, then boundary/traversal/path/delta conduct in `r2_continue_complex_kernel` |
| Predecessor identity | Git `3fcd03fdb2b601f08561eaf71c7d54cc85690eba` plus the exact source aperture below |
| Local constitutive law | typed identity minting, atomic arena reservation, sparse dimension-lowering oriented incidence, exact signed boundary composition, downward receiver traversal, parent-linked persistent paths, and local append/departure delta |
| Receiver question | whether the admitted local complex has exact declared chain boundary, whether traversal returns only caused reachable support, and whether each change or refusal preserves its complete receipt |
| Returned consequence | ten decoded complex receipts, exact boundary testimony, support/path certificates, staged-difference testimony, device-resource testimony, and PTX/cubin/SASS artifacts |
| Open alternatives | source byte/chunk occurrence founding, chart transition/navigation, file-store mounting, and all R3-and-later deeds remain absent |

## Owner-native representation

Distinct typed minters produce occurrence, event, port, region, and lineage identities on the card.
Their serial testimony derives from the declared owner seed and mint chronology, never a pointer,
array address, CUDA lane, path, or digest. The complex owner and its cell/incidence/path arenas
delete copy construction and assignment. The compile-negative ownership gate confirms that a
resident complex cannot be copied.

`bounded_view` is a non-owning, capacity-checked aperture. `arena<T,N>` owns raw aligned device
storage, exposes exact preflight/reservation receipts, and constructs only reserved members. The
application-visible crossing contains encoded cells/incidences and returned receipts, not the
owner's arrays. Cell slots are owner-local navigation coordinates; minted identities remain the
semantic marks.

Each cell retains dimension, occurrence, region, lineage, multiplicity, and sparse outgoing
support. Each incidence retains its higher/lower slots, event, port, lineage, orientation, and
multiplicity. Traversal follows only each reached cell's contiguous outgoing support. It creates
one persistent parent node per newly reached cell and returns a terminal path fold; it never
materializes an all-pairs relation or expanded path forest.

## Returned device artifact

The complete decoded artifact is `build/r2/receipts/R2_STRUCTURE_DEED.txt`; its SHA-256 is
`5b2173050bbcbfc94d2816c39f3379890c323295cb0821cebf1ed98e117e7570`. Its summary is:

```text
truth_status=established-bounded
evidence=implemented-exact,computational-witness
program=r2_admit_complex_kernel+r2_continue_complex_kernel.sm_89
case_aperture=10
device_compute_capability=8.9
kernel_launches=2
launched_threads=256
bytes_to_device=13760
bytes_from_device=2560
resident_structure_bytes=29280
verification_failures=0
```

The tetrahedral case admits 15 cells and 28 sparse incidences. Four oriented faces and one
three-cell produce five exact `boundary(boundary)` checks over 36 composed local terms, all zero.
Its traversal reaches all 15 cells, touches exactly 28 incidences, retains 15 parent nodes, and
returns a four-occurrence terminal path fold. The multiplicity triangle scales edge incidence by
two and face incidence by three; its exact composed coefficients still cancel.

The disconnected case admits 11 cells and 11 incidences. The declared receiver seed reaches only
the seven-cell triangle component, touches its nine incidences, retains seven path nodes, and does
not touch the separate interval's two incidences. Its isolated cell then departs through a
one-cell structural delta. A separate singular case stages one successful isolated-cell append.

The capacity case admits 15 cells, refuses a requested two-cell reservation against capacity 16,
leaves the predecessor/successor standing digest identical, and does not consume another
occurrence identity. A 17-cell first admission is likewise refused before minting. Attempted
departure of an incident vertex returns `departure_blocked` with identical predecessor/successor
standing.

Standing/support/path hashes in this artifact are observer checksums over exact returned
testimony. They are not occurrence identity and establish no equality beyond their named receiver.

## Artifact hashes

Two independent build directories return identical bytes for the structure executable, PTX,
cubin, normalized build manifest, and decoded deed artifact at the same source aperture.

The final graded source aperture SHA-256 is `8731aaabd6ab774f65b39d98bc294453894f405b1e6e9ed3977799c0dfb7e7fb`.

| Artifact | SHA-256 |
|---|---|
| normalized structure-deed executable | `072185d775ed31d3e0d0bb0f6e872faf2a1a249f068619d0ceb83e9cc9250446` |
| structure-deed PTX | `3831f0fd65f5f03cc596440e4fd236eb9fe42602bb6751d555bd272404c74c63` |
| structure-deed cubin | `dd28dff4970c5ff4c20efbfe25df35cddca1fac69a763842e4eba6273b354296` |
| complete decoded structure artifact | `5b2173050bbcbfc94d2816c39f3379890c323295cb0821cebf1ed98e117e7570` |

## Gate returns

- Architecture, owner-DAG, source-size, no-float, no-compatibility, and copy-ownership audits pass
  before and after construction.
- Both release build directories pass all 12 CTest gates and return byte-identical admitted R2
  artifacts and normalized manifests.
- The independent host verifier reproduces admission/refusal state, exact chain composition,
  receiver reachability/order, touched support, persistent parent path, identity chronology,
  predecessor/successor digest, and append/departure receipts for all ten card returns.
- The real two-kernel card deed passes NVIDIA `compute-sanitizer` memcheck and initcheck with zero
  errors. Initcheck initially exposed uninitialized C++ padding in the whole-output transfer; raw
  resident/output allocations are now initialized before placement construction, and the repaired
  transfer passes.
- The callable structure laws and independent verifier pass host AddressSanitizer and
  UndefinedBehaviorSanitizer with leak detection enabled.
- Clang 22's static analyzer reports no diagnostic over the project-owned structure deed,
  conformance, artifact, case, verifier, and included production-law aperture.
- PTX and final SASS scans find no floating type, conversion, arithmetic, comparison, or special
  function instruction in the structure device artifact.

## Apparatus and resource boundary

The host transfers encoded source testimony once and receives the complete bounded receipt once.
The 29,280-byte complex allocation persists on the RTX 4080 SUPER between the admission and
continuation kernels; the host performs no structural replay. Physical byte/thread counts are
apparatus testimony and do not enter identity, incidence, traversal, or delta standing.
