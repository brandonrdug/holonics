# R0 architecture receipt

**Truth status:** `established-bounded`.

**Evidence:** `implemented-exact` for the declared R0 build/audit aperture. Contemporary apparatus
identity is separately `measured` in
[`provenance/HARDWARE_RECEIPT.txt`](../provenance/HARDWARE_RECEIPT.txt).

**Aperture:** compile-time C++/CUDA contracts and their source, ownership, build, PTX, and SASS
audits. This receipt establishes no runtime ecology and no exact arithmetic capability.

## Construction tuple

| Field | R0 standing |
|---|---|
| Source owners | `exact`, `structure`, `body`, `event`, `current`, `receiver`, `organ`, `codec`, `apparatus` contract owners |
| Port types | configure, compile-contract, audit, manifest, PTX/cubin, and receipt boundaries |
| Event occurrence | pinned configure/build/audit/test invocation |
| Predecessor identity | Git `28353835afce5ab3701413d95cc9c0c6f62e4536` plus the manifest's exact source aperture |
| Local constitutive law | restricted C++/CUDA type law, owner DAG, move-only ownership law, and zero-allowance source/binary predicates |
| Receiver question | whether lawful host/device contracts compile and named forbidden fixtures are rejected |
| Returned consequence | compiling empty contract body, exact artifact hashes, normalized command manifest, and architecture receipt |
| Open alternatives | R1 carrier behavior, runtime event/current/body behavior, and all later roadmap deeds remain absent |

## Frozen owner DAG

The topological owner order is `exact`, `structure`, `body`, `receiver`, `organ`, `codec`, `event`,
`current`, `apparatus`. The admitted dependencies are:

```text
exact       -> {}
structure   -> {exact}
body        -> {exact, structure}
receiver    -> {exact, structure}
organ       -> {exact, structure}
codec       -> {exact, structure}
event       -> {exact, structure, body, organ}
current     -> {exact, structure, body, event}
apparatus   -> {exact, structure, body, event, current, receiver, organ, codec}
```

`cmake/HolonicArchitecture.cmake` is the executable declaration. The audit rejects undeclared
owners, later-to-earlier violations, cycles, and forbidden includes.

## Returned artifacts

Two independent build directories returned identical bytes for every admitted artifact:

The graded source aperture SHA-256 is
`33198ac22f354da8cc3f694b0255b09db16823b77cae3971a783c1bfd05e951e`.

| Artifact | SHA-256 |
|---|---|
| host contract executable | `07b30de70febc7eb63b546a92cf31af57b85f8564f6cb719d665abaa3a8086ac` |
| normalized CUDA contract object | `640c668f3bf657d8451f0425940a0bc3e69ff46df71c1f06d263f42571bb3e3c` |
| CUDA contract PTX | `573ff1193e65bbe9abf4ebd0d80131ead668bc7682735ac670cce88ccaec5d97` |
| CUDA contract cubin | `071674b9dd5b7d1813e5262e88dc9e6e11cf54915549b6ded796cea4848713c9` |

The normalized build manifest is deposited as `build/r0/receipts/BUILD_MANIFEST.txt` on every
build. It contains the source commit/status, exact source hashes and aggregate, tool hashes,
normalized compile commands, normalized complete Ninja commands, architecture, and artifact
hashes. The generated PTX targets `sm_89`; inspected SASS for `r0_contract_probe` contains `MOV`,
`EXIT`, `BRA`, and `NOP` only.

## Gate returns

- Direct pre-construction inspection found no production C++/CUDA source and no prior build.
- The source/owner audit passes on the admitted production aperture.
- The host C++23 and device C++20 contract fixtures compile under the pinned profiles.
- Copy construction and assignment are deleted for continuation, body, live morphology, pending
  deed, delta, resident world, codec environment, and rest ownership contracts.
- Negative fixtures are rejected for copy, floating carrier, forbidden owner dependency,
  public standard-container ownership, and compatibility route.
- PTX and SASS audits find no floating type or operation in the device contract artifact.
- Both independent build directories pass all seven CTest gates.
- Both normalized build manifests are byte-identical at the graded source aperture.
- A separately compiled host conformance executable passes AddressSanitizer and
  UndefinedBehaviorSanitizer with no diagnostic.

No device runtime deed is admitted in R0, so a `compute-sanitizer` execution is outside this
phase's aperture. The returned device evidence is compilation plus PTX/cubin/SASS inspection; R1
owes the first executed exact device deeds and their device-sanitizer receipts.

## Apparatus boundary

The pinned CUDA executable is `/opt/cuda/bin/nvcc` 13.2.78 with SHA-256
`02afd6a20bd29fae33bf278fa847a4e9711db25afec4a1bf648be81a3b210af0`.
`/usr/local/cuda/bin/nvcc` is separately CUDA 12.9.86 and is not an alternate admitted compiler.
CUDA 13.2 plus GCC 16 rejects NVCC-generated line markers when host `-Wpedantic -Werror` is
forwarded. Public contracts therefore receive the complete GCC warning profile directly; NVCC
receives all remaining host warning/ownership flags and `--Werror=all-warnings`. This bounded
apparatus rule is recorded in `blueprint/CPP_GPU_FOUNDATION.md`.

## Construction-state update protocol

**Truth status:** `project-postulate`.

1. Run the active phase's named artifact, conformance, architecture, no-float, ownership, build,
   and device-binary gates.
2. Inspect the actual returned artifact; diagnostics alone do not pass a deed.
3. Write a bounded receipt with the exact source aperture, predecessor, artifacts, hashes,
   falsifiers, and open alternatives.
4. Update `CONSTRUCTION_STATE.md` only after steps 1–3 pass, recording admitted standing and the
   roadmap's single next deed.
5. Commit and push the coherent phase in bulk. A failed phase leaves construction standing at its
   predecessor and reopens the responsible owner.
