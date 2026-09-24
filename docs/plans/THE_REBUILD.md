# The rebuild

**Status:** active, September 24. This plan replaces the restructure plan, which is in git history
at [`13f8c734`](https://github.com/brandonrdug/holonics/blob/13f8c734/docs/plans/THE_REPOSITORY_RESTRUCTURE.md).
Tracked in #63.

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

## Rules of the rebuild

- **Build forward from the elementary objects.** Each new owner states which object and law it
  implements ([operator contract](../ELEMENTARY_OBJECTS.md#operator-contract)).
- **Port deliberately.** A law or kernel is ported from history (`13f8c734`) when a step needs it.
  It is read, rewritten against the current objects, and tested by the law it implements. Nothing
  is restored wholesale, and nothing is kept for compatibility.
- **One library for the laws, one backend for the card.** `holonics` builds without CUDA.
  `holonics-cuda` depends on it and realizes its operations; `holonics-apple` follows later on
  Brandon's branch.
- **Lean first for new mathematics.** A new law lands with its Lean statement, or names its
  obligation in #62.
- **Tests are written per law** as each owner is built: one fast test per stated law, plus one
  host/device parity check per kernel family.

## Order

1. **The `holonics` operator layout.** Reorganize the existing library into `ratio/` (one per two:
   remainder, residue, inversion, lift, jet, rings), `geometry/` (complex, frame, clock, carry,
   screw, pair and tube charts, winding), `holon/` (law, ports, Dirac, elements, generators,
   restrictions, deposition, reaction) and `receiver/` (roles, receipts, standing, release).
   Exact algebra sits privately beside the operators that use it. Retire what no operator needs.
2. **K1: Holarchy, Aeon/Epoch/Cycle, complete interconnection and joint reception** (#72). Lean
   first (the obligations in #62), then `holonics::{holarchy, aeon}`.
3. **The HNN law in `holonics::hnn`, over aeons.** The field is chains of parametron rings joined
   by pair contacts. It has:
   - source moments `m_g = Σ_k Ĝ_g(τ_g(k))⁻¹E_g(u_k)`;
   - the power-neutral reaction (Cayley step);
   - the normal constitution and deposition;
   - loss as the logarithm of the Holon ratio;
   - retention as the future-sufficient quotient at aeon boundaries.

   It is built with a host reference, porting its equations from history's `native_ecology` and
   the prototype body as needed.
4. **The resident HNN in `holonics-cuda::hnn`.** Kernels are ported per law, each with its parity
   check against the host reference.
5. **Physics instances** (K3–K4) and equation extraction, when their consumers exist.
6. **Lean:** curate the `Holonics` foundation versus research, remove the duplicate theorems the
   audit found, then rename the namespace.
7. **Applications** (a workbench, an Athena application), rebuilt on the library under the
   lessons record's requirements.
