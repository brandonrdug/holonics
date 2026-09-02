# WRD3: the junction counts emissions, and the returned interaction is derived, not typed

**Date:** 2026-09-02
**Truth status:** `established-bounded`
**Evidence:** `measured` (focused Cargo tests on the resident apparatus, commands and dates below)
**Provenance:** Assistant (Claude), under Brandon's direct instruction of 2026-09-02 to deposit and complete the WRD campaign. Assistant derivation and construction, including one correction of the campaign blueprint recorded below.
**Band:** ONE EMISSION IS ONE CROSSING / GAMMA AND T AS INTEGER PAIRS / MATCH HALTS / PARTIAL REFLECTION RE-ENTERS / TERMINUS BY TYPE / THE CONE IS WHAT THE ADMITTED EMISSIONS CARRIED / WITHDRAWAL EXACT

---

## Statement

[definition] `soma/life/src/native_intelligence/route_return.rs` owns `derive_world_return`.
From one conducted `NativeCirculationBoundary`, the cold witness of its lattice, the kernel faces
of its candidate family (`KernelReturnFace { admitted, carried, diagnostic }`, read from
`LeanKernelReturnFamily` by `kernel_return_faces`), a returned occurrence, and the emitting
boundary, it returns one of three dispositions:

- **Matched** (every emission admitted): `ReturnedScaffoldInteraction` with current `(1, 0)` and
  storage `1`; termination `Halt`.
- **Reflected** (some admitted): current `(T, Gamma)` and storage `1 / service rounds`, with the
  pairs from `holonic_structure::CountedCrossing::meet(R, M)` and never divided before the exact
  rational is formed; the contact support is the states of the organs the admitted emissions
  carried (the deposit law adds the route's two ends); the organs carried only by reflected
  emissions re-enter at the smallest occurrence whose referring proof is one of them, else `Open`.
- **Terminus** (nothing admitted): no interaction; `RouteObstruction { carried,
  named_by_diagnostic, next_entering }`.

The result enters `NativeCirculationSession::stage_return` and `commit` unchanged.

[historical] The blueprint's first WRD3 paragraph counted organs as the junction populations and
read transmission from diagnostics. Construction corrected it on 2026-09-02: the unit that crosses
the boundary is an emission, so `R` is the candidate family and `M` the admitted emissions. Under
the organ count an admitted closer that carried no organ would have read as a terminus although
the world had said yes. The Lean owner (`HolonicWorldReturnDeposit.lean`) never fixed the unit
and is unchanged. The blueprint carries the same note.

## Tests

[established-bounded] `cargo test -p life --lib route_return` (2026-09-02, 4 tests, resident
CUDA apparatus) passes on the four-theorem control corpus mounted through WRD1:

- a matched return (one admitted emission carrying `alpha`, `beta`) commits generation 1 with
  storage `1`, current `(1, 0)`, and a cone containing the states of `alpha`, `beta`, `gamma`; the
  commit's causal cone has 3 states; `withdraw_last_commit` restores the predecessor's canonical
  bytes exactly;
- a partial return (2 emissions, 1 admitted) has junction `(2, 1)`, service rounds `2`, storage
  strictly between `0` and `1`, reflected `{beta}`, and opens because `beta` has no in-corpus
  premise to re-enter at;
- an admitted closer carrying no organ beside one reflected emission deposits on the route's two
  ends alone (`alpha`, `gamma`);
- a boundary admitting nothing is a terminus whose obstruction founds the next entering
  occurrence at `gamma`'s premise crossing.

## Boundary

[established-bounded] Threads outside the cone are bit-identical after a commit by the standing
cultivation owner's interchange check, which `stage_return` and `commit` invoke unchanged; this
record adds no second copy of that law.
