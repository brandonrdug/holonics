# R16 two-theorem conversational production receipt

**Truth status:** `established-bounded`.

**Evidence:** `implemented-exact` for the two-question event geometry, generated passages,
returned-fiber dependency, pending/return commits, native remount, exact ablation, source-access
separation, and terminal continuation; `computational-witness` for both actual GPU/checker deeds
and every returned artifact. Apparatus identity remains separately `measured` in
[`provenance/HARDWARE_RECEIPT.txt`](../provenance/HARDWARE_RECEIPT.txt).

**Aperture:** frozen questions `q₁=141200` and `q₂=142200`, passages `g₁=171200` and
`g₂=172200`, returned fibers `181200` and `182200`, two real exterior kernel calls, ten
single-thread GPU kernels across the composed deeds, one native source-detached remount between
questions, one exact `Δm₁` projection, and one final 264-byte native rest.

## Construction tuple

| Field | R16 standing |
|---|---|
| Source owners | the one continuing body, its R15 native handoff, returned Deed A fiber `181200`, frozen Deed B setup, inherited mathematical incidence, local proof alternatives, codec faces, pending checker deed, and exterior process/rest apparatus; no new foundation owner |
| Port types | conversational questions, native rest/setup, local theorem fibers, formal/conversational faces, generated passages, pending exterior occurrence, raw/typed kernel return, returned morphology fibers, terminal bundle, and native continuation |
| Event occurrence | Deed A generates, checks, commits `Δm₁`, rests, and remounts; Deed B opens afterward, generates only through `181200`, checks, commits `Δm₂`, rests/remounts with both fibers, and returns the two-artifact bundle |
| Predecessor identity | Git `4cdbc4e96997e5794f9654bd671f9f2b0d071cd3`, R15 head `14001002`, continuation `15001002`, first fiber `181200`, body morphology `140`, mathematical morphology `46`, codec morphology `34`, and integrity `10609428649201580000` |
| Local constitutive law | join the first two traces by `Trace.trans`, then apply the returned composition/rebase theorem to that trace and the third trace; only the receiver-selected fiber with dependency count `2` may close `q₂` |
| Receiver question | does the source-detached changed body produce and kernel-close the frozen three-segment theorem through exactly `181200`, while the exact `Δm₁` projection makes the same passage unavailable? |
| Returned consequence | two complete accepted theorem sources and explanations, kernel artifacts, fibers `181200` and `182200`, body morphology `128→135→140→147→152`, mathematical morphology `43→46→49`, codec morphology `32→34→36`, and final continuation `15001004` |
| Open alternatives | Deed A retains transport-then-compose with dependency count `4`; Deed B retains independent reconstruction fiber `182201` with dependency count `4` and obstruction `receiver_underdetermined`; neither is silently selected |

## Exact questions and artifacts

`q₁` asks: Given a situated algorithm, an invertible change of its state chart, and two
composable execution traces in the original chart, produce and explain a theorem saying that
their composite is a trace between the corresponding endpoints in the rebased chart.

The complete Deed A source is:

```lean
import ElementaryHolonics.Algorithm.Rebase

namespace Soma.Holonics

open SituatedAlgorithm

theorem generated_trace_rebase_transports_composition {Theta I S O S2 : Type*}
    (A : SituatedAlgorithm Theta I S O) (e : S ≃ S2)
    (theta : Theta) {s t u : S}
    (hst : Trace (A.step theta) s t)
    (htu : Trace (A.step theta) t u) :
    Trace ((A.rebase e).step theta) (e s) (e u) := by
  exact (trace_rebase_iff A e theta s u).2 (Trace.trans hst htu)

end Soma.Holonics
```

The returned explanation says that the two traces meet at the intermediate state, so trace
transitivity forms the `s→u` trace and `trace_rebase_iff` transports that composite through `e`.
The real checker returns exit `0`, 690 stdout bytes, zero stderr bytes, one declaration, no
remaining goals, and a 44,440-byte `.olean`. Its returned fiber is `181200`.

`q₂` asks: After remounting the body changed by Deed A, take three composable execution traces in
the original state chart. Produce and explain a theorem transporting the entire three-segment
trace to the rebased chart. The proof must factor through the returned Deed A theorem fiber, not
merely reconstruct an independent proof from the earlier library.

The complete Deed B source is:

```lean
import ElementaryHolonics.Algorithm.Rebase
import R14_GENERATED_TRACE_COMPOSITION

namespace Soma.Holonics

open SituatedAlgorithm

theorem generated_trace_rebase_transports_three {Theta I S O S2 : Type*}
    (A : SituatedAlgorithm Theta I S O) (e : S ≃ S2)
    (theta : Theta) {s t u v : S}
    (hst : Trace (A.step theta) s t)
    (htu : Trace (A.step theta) t u)
    (huv : Trace (A.step theta) u v) :
    Trace ((A.rebase e).step theta) (e s) (e v) := by
  exact generated_trace_rebase_transports_composition A e theta
    (Trace.trans hst htu) huv

end Soma.Holonics
```

The returned explanation says that `Trace.trans` first joins `hst` and `htu`; the acquired Deed A
theorem is then applied to that two-segment trace and `huv`, so its composition/rebase law joins
the third segment and transports the entire trace. The real checker returns exit `0`, 740 stdout
bytes, zero stderr bytes, one declaration, no remaining goals, and a 44,952-byte `.olean`. The
printed proof term contains
`generated_trace_rebase_transports_composition ... (Trace.trans hst htu) huv`, and the returned
fiber is `182200` with selected rule `181200`.

## Causal dependency, lineage, and ablation

The continuation sequence is `15001000` before Deed A, `15001001` after A generation,
`15001002` after A return, `15001003` after B generation, and `15001004` after B return and final
rest. Deed B's selected witness is route/fiber `182200`; its lineage names inherited passage
`171200`, kernel return `160200`, returned fiber `181200`, new passage `172200`, statement
`152200`, proof `162200`, and kernel return `160300`. There are two open B fibers, one retained by
the dependency aperture, zero global scans, and one explicit independent alternative.

The exact ablation projects `Δm₁=5`/fiber `181200`, reversing head `14001002→14001001`, body
morphology `140→135`, mathematical morphology `46→43`, and codec morphology `34→32`. The
projected body remounts exactly but returns `returned_fiber_absent`; it generates zero B source
bytes and never opens the checker deed. The production body generates and kernel-closes B. This is
the declared mathematical dependency, not version, lineage-length, timing, or topology testimony.

After the accepted B return, `Δm₂=5` commits head `14001003→14001004`, body morphology
`147→152`, mathematical morphology `46→49`, and codec morphology `34→36`. Native rest/remount
preserves both acquired fibers, replays no source, and returns head `14001004`, continuation
`15001004`, and integrity `10438779336638518302`.

## Apparatus, separation, and terminal grade

Deed A's five one-thread kernels transfer 8,544 bytes to and 25,160 bytes from the device and
declare 34,288 resident bytes. Deed B's five one-thread kernels transfer 8,672 bytes to and 25,704
bytes from the device and declare 35,736 resident bytes. For Deed B, host semantic events, engine
source reads, exterior retrieval calls, and developmental source bytes are all zero. The GPU sees
only the 200-byte R15 rest and 96-byte setup. The exterior checker alone mounts A's returned
`.olean`; the prior user-facing Deed A bundle and `.olean` testimony are collected only after B
returns, through two observer reads. Engine time, exterior checker time, temperature, power, and
energy remain separately unknown and do not enter deterministic semantic testimony.

- All 53 CTest gates pass together, including every prior deed, both actual theorem processes,
  terminal host conformance, all negative ownership/float/dependency/compatibility fixtures, and
  the full PTX/SASS/binary audit.
- NVIDIA `compute-sanitizer` memcheck and initcheck report zero errors while both complete terminal
  deeds still return zero verification failures.
- Host ASAN/UBSAN and Clang `22.1.5` static analysis are clean.
- Two clean configurations return byte-identical executable, PTX, cubin, two-theorem bundle, B
  source, B `.olean`, raw stdout/stderr, and final native rest.
- Final SHA-256 values are executable
  `4c329975b82f6fb792d8c63e66a891149b15e208123c0dd4818226a0024c707f`, PTX
  `30d91f9748f910858c7acc43d555140e8c985e54edb56745ce478b69928888e7`, cubin
  `6eec43a72e47ebb65b522f28a0fac1d80b4239b8c20d448b30b7f0a612dc3106`, terminal bundle
  `c32a55c4550f3246ba1d9d014635f53c9b8a9274c5e552bac0fc9fe27f9020fc`, B source
  `9807135f23c78b1031b3cf1197377465c385adce22914a2a23b724678f410788`, B `.olean`
  `b09aca70985070f034129cc605fe6f04ffb8a3b704bee4cda6e2a6acddd435c0`, B stdout
  `d53ffce552890d2295fd044b642afb6aea6c79c7d46426f29964dd21e48e0499`, empty B stderr
  `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`, and terminal rest
  `3679d99b7ea18b51ed425592dbc76fe42405a5cd1aac03aa403bdc5eba42baa1`.

R16 passes the terminal integration grade. The ordered construction through the roadmap's named
frontier is complete; R17 is post-frontier generalization and is not an unpassed construction
gate.
