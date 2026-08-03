# C++ and GPU production foundation

**Decision.** The production realization is modern C++ plus CUDA C++; Rust is historical evidence
only. The semantic canon remains language-independent, but no alternative implementation is kept
for compatibility. The GPU is the primary resident workhorse. The CPU is a boundary apparatus for
process startup, durable I/O/rest, driver interaction, narrow exterior codecs, and offline
admission audits—not the hidden owner of language, event selection, or the hot algorithm.

**Contemporary apparatus receipt (`measured`, 2026-08-03).** NVIDIA GeForce RTX 4080 SUPER,
compute capability 8.9, 16,376 MiB reported memory, driver 595.71.05; CUDA 13.2 / NVCC 13.2.78;
GCC 16.1.1 and Clang 22.1.5 are present. These observations seed a pinned build profile; they are
not semantic constants. Exact command testimony is retained in
[`HARDWARE_RECEIPT.txt`](../provenance/HARDWARE_RECEIPT.txt).

## 1. C++ language law

The foundation establishes a small lawful subset before domain construction. The pinned initial
profile is GCC/libstdc++ 16.1.1 with C++23 for the host interface, CUDA 13.2.78 with its C++20
device subset targeting `sm_89`, CMake 4.3.2, and Ninja 1.13.2. Exact executable/library hashes are
in the apparatus receipt.

Initial release flags are:

```text
host:   -std=c++23 -O3 -Wall -Wextra -Wpedantic -Werror -Wconversion
        -Wsign-conversion -Wshadow -fno-exceptions -fno-rtti
        -fno-fast-math -ffp-contract=off -ffile-prefix-map=<source>=.
device: --std=c++20 -O3 --gpu-architecture=sm_89 --fmad=false
        --Werror=all-warnings
        -Xcompiler=<the host warning/ownership flags above except -Wpedantic>
```

The CUDA translation receives no forwarded `-Wpedantic`: with CUDA 13.2 and GCC 16.1.1 that flag
rejects NVCC-generated line markers before project source is graded. Every public contract is also
compiled directly by GCC with the complete host profile, including `-Wpedantic -Werror`; NVCC's
own diagnostics remain errors through `--Werror=all-warnings`. This is a bounded apparatus-profile
rule, not a source-warning allowance.

Debug/conformance builds additionally use host address/undefined-behavior sanitizers and
`compute-sanitizer`; those instruments are not production semantics. Every build deposits a
manifest containing source commit, compiler and dependency hashes, exact command lines,
architecture, generated PTX/cubin/executable SHA-256 values, and the binary no-floating-operation
audit. Build-output hashes remain `open` until the first source exists; the procedure is fixed now.

The language law is:

- the pinned host/device subsets and build receipt above;
- warnings-as-errors, no implicit narrowing, no uninitialized reads, no signed overflow, no
  invalid shifts, no lifetime escape, and no undefined behavior admitted as an optimization;
- exceptions and RTTI disabled in the semantic/device core; failure is a typed result/obstruction;
- live bodies, pending deeds, continuations, resident worlds, and codec environments delete copy
  construction/assignment and expose explicit move-only ownership;
- every resumption requires a unique continuation capability; views are bounded and
  non-resumable;
- RAII owns apparatus resources, while semantic commit remains an explicit event operation rather
  than a destructor side effect;
- standard containers may support the structure owner internally, but cannot appear as
  application-owned standing, global registries, or traversal policy; and
- compilation boundaries mirror owner boundaries, not a large utility layer.

Host validation uses sanitizers, static analysis, deterministic builds, and bounded model/property
fixtures. Device validation uses `compute-sanitizer`, explicit bounds/overflow receipts, decoded
semantic equality, and kernel-specific conformance tests. Tests witness declared finite families;
generic laws require types, proofs, or refinement arguments.

## 2. Bit-pure exact carriers

No floating-point instruction or operation exists in the production semantic/device-core
dependency cone. A floating result may not determine a branch, index, coefficient, topology,
identity, carrier promotion, or integer/bit later committed in a delta, even if the floating value
itself disappears. Source/type checks and PTX/SASS (or equivalent final-binary) audits enforce the
ban. The exact carrier library owns:

- unsigned/signed limb words with specified endianness and overflow behavior;
- fixed tiers such as 128/192/256/384 bits where a bounded receiver proves them sufficient;
- rationals in normalized integer form;
- finite fields, residue rings, exact polynomial and homogeneous/projective values;
- stable owner-minted occurrence identities distinct from addresses and lane indices; and
- explicit promotion/refusal when preflight proves a tier insufficient.

Approximate exterior readings must first become integer/rational bounds with calibration and an
open remainder before crossing a semantic port. Device and host layouts are related through explicit encode/decode maps. Raw pointer equality,
memory address, padding, object representation, worker lane, and hash never establish semantic
identity. Sensor and external approximate values enter only through calibrated bit codecs with an
open quantization/error fiber.

## 3. Owner dependency graph

```text
exact-structure (value/type library; no live standing)
  ├── causal-body
  │     ├── one live incidence-and-current owner
  │     ├── local morphology cells
  │     └── unique continuation capability
  ├── algebraic-receiver
  └── codec-port

causal-body + local-domain-organs
  └── pending-event-and-return

pending-event-and-return + exact-structure
  └── reified-causal-program

reified-causal-program
  ├── cuda-resident-executor       (primary production path)
  ├── bounded-reference-oracle     (admission/lifecycle audit only)
  └── exterior-codec-apparatus
```

No arrow points from a presentation, repository, checker, display, host phase, or application into
causal ownership. A domain organ is mounted at local typed incidence; there is no organ atlas,
scheduler, phase machine, or central candidate collection.

## 4. GPU-resident causal body

After mount, the active structural slabs, local morphology, sparse currents, pending deeds, and
exact carrier populations reside on the card whenever their declared aperture fits. Wide local
work—incidence restriction, projective swing, exact algebraic transport, receiver projection,
field/current propagation, overlap comparison, and local consequence formation—executes there.

The card receives a reified program containing predecessor identity, bounded caused support,
typed ports, exact constitutive operator, expected return shape, and deterministic resource
obligation. It returns a staged semantic delta or explicit obstruction. It does not receive a
semantic tag such as “text,” “proof,” or “graphics,” and it does not delegate the deed back to a
complete host algorithm.

Fronts are founded by caused local incidence. Independent members occupy CUDA grids/blocks/warps
only after an interchange certificate; successive fronts remain causally ordered. Hardware lane
order is not event chronology. Cooperative groups, work queues, CUDA graphs, or persistent kernels
are admissible apparatus techniques only when their queue/closure is owner-local and their
completion order cannot enter semantic standing.

## 5. Host boundary without a foreman

The host may:

- open the process and GPU context;
- transfer an initial native mount and final/rest deltas;
- route a named exterior occurrence through a codec port;
- persist the unique continuation capability in native rest;
- collect bounded observer and telemetry receipts; and
- run an offline reference oracle when admitting or auditing a program family.

The host may not enumerate semantic phases, select candidates, scan the global body for the next
event, run the real algorithm after a kernel, or silently retry on CPU. Device inability is an
obstruction or a caused repartition/residency change in the same body.

## 6. Exact device admission

For a declared program family and common admitted domain:

1. encode the same typed predecessor/current through the apparatus representation map;
2. execute the bounded reference oracle and GPU realization as separate audit branches which do
   not own continuation;
3. decode both results;
4. require exact identity and causal-order equality, plus equality/equivalence required by the
   program for morphology delta, current, boundary return, alternatives, obstruction, lineage,
   and deterministic resource obligations;
5. prove carrier sufficiency or exact promotion/refusal; and
6. admit a versioned kernel/program-family pair.

Only one result can receive the live continuation capability. After admission, production runs on
the GPU and returns local/delta equality receipts. Full oracle replay is a declared lifecycle audit
only. Apparatus-specific capacity, placement, timing, temperature, and energy remain separate
telemetry and may later cause a resource-return event.

## 7. Foundation conformance and first pure-holonics organ

The first code deed is not a language, proof, or rendering application. It is the minimal C++/CUDA
carrier which can:

1. mint typed occurrences and ports;
2. own one move-only body and continuation capability;
3. open a pending deed, accept an exact returned occurrence, stage a local delta, and commit once;
4. carry a sparse caused front through oriented incidence to compositional rest;
5. distinguish occurrence equality, marked-diagram isomorphism, receiver equivalence, presentation
   equality, byte equality, and digest equality;
6. admit and execute the same reified event on the GPU with bit-exact decoded testimony; and
7. persist/remount without source replay or a resumable clone.

Those seven clauses form the application-agnostic foundation conformance slice. The first mounted
pure-holonics grading organ then executes a four-member exact projective swing and preserves its
projective-pair invariant and lineage. Swing is essential to the first production deed but does
not determine the core ABI: another lawful organ can mount through the same ports without changing
foundation types. Neither slice is a toy proof that the machine can compute; each closes a named
production invariant.

## 8. Hard falsifiers

Reject the construction if it introduces floating semantic standing, host-authored phases, a CPU
hot fallback, whole-body cloning, raw-address identity, application-owned standard-container
standing, global queue emptiness as rest, lane order as causality, device telemetry in semantic
equality, or a kernel which merely prepares data for the host to perform the real deed.
