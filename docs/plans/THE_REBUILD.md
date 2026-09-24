# The rebuild

**Status:** active, September 24. This plan replaces the restructure plan, which is in git history
at [`13f8c734`](https://github.com/brandonrdug/holonics/blob/13f8c734/docs/plans/THE_REPOSITORY_RESTRUCTURE.md).
Tracked in #63.

## The line the rebuild serves

[project-postulate] **Compression is intelligence is navigation** (Brandon). The rebuild builds one
line: Holonic Compression and landmark discovery, executed at scale by the HNN and applied to every
target the framework is advanced enough to reach. The Riemann hypothesis, Hodge, complex Euler and
Navier–Stokes, and Birch–Swinnerton-Dyer are such targets. They are not a separate "Millennium"
category: work on them is landmark discovery and compression, stated in the same objects as
everything else.

- **Terrain** is stuff in general: whatever is present for a navigator to meet. That includes
  Holons, their constitutions and modes, and an exterior source.
- A **fractal navigator** is a function with an initial configuration, its own clock and carry, a
  family of restrictions with its scale square, and address words
  ([elementary objects §3](../ELEMENTARY_OBJECTS.md#3-navigator)). The guides called it a
  "generator". That word keeps only its algebraic senses: a generator of a group, the Lie generator
  `ξ` of a helix, a generating function.
- **Holonic Compression** couples a navigator's resonating modes with terrain.
  - Where a navigator's mode meets a terrain mode, it rides that mode at minimal work (resonating,
    RIDE). What it cannot reach, it founds (emanating, FOUND).
  - A compression is a codec pivot that carries its decoder
    ([tablet](../canon/TABLET_THE_COMPRESSION.md)). The navigator and its decoder stand in for the
    material they regenerate, and the decompression is causal: it unfolds over the navigator's clock.
- **Kernel and cokernel** are the two sides of that coupling, dual in the way Holon and coholon are.
  Against a receiver family, a navigator's face map `F` has:
  - a **kernel**: the differences no admitted future receiver distinguishes. Quotienting by it is
    compression, and it is retention. Owners: `Foundation/CausalRelevance` (the relevance kernel),
    `Foundation/ReceiverHistoryCompression` and `Foundation/GeneratorModeQuotient`.
  - a **cokernel**: what the navigator's image does not reach, the residual that is emanated or
    retained as a separator, interior or defect. `Millennium/CokernelCalculus` states this calculus
    once, for the BSD descent and for integral Hodge.
- **Landmarks** are faces where navigator paths converge:
  - lock addresses and fixed points;
  - constraint identities: π and `e` are navigators that carry no error, and `Λ_DN` is another;
  - zeros and primes.

  **Landmark discovery** is locating keys ([keys](../ELEMENTARY_OBJECTS.md#keys-locks-and-navigation)):
  inferring the configurations of navigators by loop closure. It is the same inference the HNN
  performs.
- **Measurement.** A compression is measured against the literal by description plus work
  (`Kt=|p|+log t`; `Foundation/{ReceiverCodeCost,GeneratorInference}`). It states its kernel and its
  cokernel residual. There is no single scalar of progress.

[interpretation] The targets read as instances of the line. Their records grade each claim.
- **RH.**
  - Zeros are landmarks of spectral placement: `RH/FosterTanks` reads the zeros as LC tanks, and
    `ZeroPairLock` gives lock ⇔ `σ=½`.
  - The de Bruijn–Newman heat flow has `Λ_DN≥0` (Rogers–Tao) and is aimed at `Λ_DN=0`.
  - `Computation/ZeroNavigation` states what finite observations can and cannot decide.
- **Hodge.** Cycle production: which harmonic coholon classes actual Holon cycles realize, with the
  obstruction in the cokernel of that realization.
- **Complex Euler and Navier–Stokes.**
  - Velocity is a coholon and vorticity is `du♭`.
  - Relevance acts on the tail.
  - Necks are convergence points, and the singular aeon is A11 of the
    [aeon record](../../research/records/2026-09-24_THE_AEON_EPOCH_AND_CYCLE_STANDARDIZE_THE_PASSAGE_OF_TIME.md).
- **BSD.** The kernel of the descent face is the doubles (`Millennium/FamilyKernel`). The rank counts
  independent navigators. The obstruction lives in a cokernel.

Their Lean in `lean/ElementaryHolonics/{Millennium,RH,Mathematics,Computation}` is the most developed
use of the framework. It is not scheduled behind the HNN: work on a target proceeds alongside any
step. Each reusable law it finds lands in the shared objects (a navigator, a kernel/cokernel
statement, a landmark), not in a problem-named silo.

## Why a reset

[established-bounded; measured] The September 23–24 restructure retired about 60% of the Rust by
reachability. It then showed that most of what remained was also dead or prototype code: after the
merged crate's modules were made private, rustc reported about 3,600 dead items. Pruning a
monolith item by item costs more than rebuilding from what functions.

What was kept:
- the main library, where the Holon core was consolidated on September 22–23;
- the CUDA driver;
- the Lean mathematics;
- the object and mathematics guides;
- the research records.

Everything else is in git history. The lessons of the prototypes are in the
[lessons record](../../research/records/2026-09-24_LESSONS_FROM_THE_WORKBENCH_AND_ATHENA_PROTOTYPES.md).
Time is standardized as aeon, epoch and cycle
([record](../../research/records/2026-09-24_THE_AEON_EPOCH_AND_CYCLE_STANDARDIZE_THE_PASSAGE_OF_TIME.md)).
Work left in worktrees and branches is on `archive/leftovers-2026-09-24`, with its manifest at the
archive root. Brandon's Metal port stays on its own branch, `codex/apple-silicon`.

## Rules of the rebuild

- **Build forward from the elementary objects.** Each new owner states which object and law it
  implements ([operator contract](../ELEMENTARY_OBJECTS.md#operator-contract)), and which part of
  the line it serves: the navigators, terrain, kernel, cokernel and landmarks it touches.
- **Port deliberately.** A law or kernel is ported from history (`13f8c734`) when a step needs it.
  It is read, rewritten against the current objects, and tested by the law it implements. Nothing
  is restored wholesale, and nothing is kept for compatibility.
- **One library for the laws, one backend for the card.** `holonics` builds without CUDA.
  `holonics-cuda` depends on it and realizes its operations. `holonics-apple` follows later from
  Brandon's `codex/apple-silicon` branch.
- **Lean first for new mathematics.** A new law lands with its Lean statement, or names its
  obligation in #62.
- **Tests are written per law** as each owner is built: one fast test per stated law, plus one
  host/device parity check per kernel family.

## Order

1. **The `holonics` operator layout.** Reorganize the existing library into five operator modules:
   - `ratio/`: one per two, with remainder, residue, inversion, lift, jet and rings;
   - `geometry/`: complex, frame, clock, carry, screw, pair and tube charts, winding;
   - `holon/`: law, ports, Dirac, elements, restrictions, deposition, reaction;
   - `navigator/`: initial configuration, clock, carry, restriction family, address words, trace
     faces and the dynamical zeta, lock addresses. Today's `generator` moves here.
   - `receiver/`: roles, receipts, the relevance kernel, standing as the retention quotient,
     release.

   Exact algebra sits privately beside the operators that use it. Retire what no operator needs.
2. **K1: Holarchy, Aeon/Epoch/Cycle, complete interconnection and joint reception** (#72). Lean
   first (the obligations in #62), then `holonics::{holarchy, aeon}`.
3. **Holonic Compression and landmark discovery** (#145).
   - **Lean first.** State a navigator's face map against terrain and a receiver family by its
     kernel and cokernel. Join `CausalRelevance`, `ReceiverHistoryCompression`,
     `GeneratorModeQuotient`, `ReceiverCodeCost`, `GeneratorInference` and `CokernelCalculus`, and
     add the cost split between resonating and emanating.
   - **Then `holonics::compression`.** It carries navigator inference by loop closure, the split
     between resonating and emanating, and a landmark search whose coverage is checked. The
     identity atlas taught the check: a chart on one winding invents identities, and the
     multi-winding family refuses them.
   - **First consumers.** π and `e`, through their partial navigators (`RatioSeriesTransport`,
     `RadixWindowReceiver`), and the existing Lean receivers of the targets.
   - **Port from history as needed.** `receiver_history_compression`, `winding_inertia`,
     `identity_atlas`, `exact_linear::kernel_modes`.
4. **The HNN law in `holonics::hnn`, over aeons.** The HNN is the compression machine at scale:
   - its retention is step 3's kernel quotient;
   - its learning is locating keys;
   - its release is the split between resonating and emanating.

   Its field is chains of parametron rings joined by pair contacts. It has:
   - source moments `m_g = Σ_k Ĝ_g(τ_g(k))⁻¹E_g(u_k)`, with `Ĝ_g` the navigator's transport;
   - the power-neutral reaction (Cayley step);
   - the normal constitution and deposition;
   - loss as the logarithm of the Holon ratio;
   - retention as the future-sufficient quotient at aeon boundaries.

   It is built with a host reference, porting its equations from history's `native_ecology` and
   the prototype body as needed (#73).
5. **The resident HNN in `holonics-cuda::hnn`.** Kernels are ported per law, each with its parity
   check against the host reference.
6. **Targets, physics and extraction.**
   - The targets continue as landmark discovery on the rebuilt library and their Lean.
   - The physics instances are K3–K4 (#74, #75).
   - Equation extraction compresses a foreign realization into navigators and element relations.
7. **Lean.**
   - Curate the `Holonics` foundation versus research, and remove the duplicate theorems the audit
     found.
   - Rename the namespace. Directories named after the prize ("Millennium", "RH") are renamed by
     subject, and generator names become navigator names where they mean the object.
8. **Applications** (a workbench, an Athena application), rebuilt on the library under the lessons
   record's requirements.
