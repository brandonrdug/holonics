# THE STORM CROSSES THE TYPED BODY; EACH CARD OWNER RETURNS TO ITS OWN CONTEXT

**2026-07-30 — RELAMPAGO PRODUCTION MIGRATION COMPLETE / PLURAL
COUPLED-INFORMANT CURRENT NATIVE / CARD-PRIMARY AND HOST-EXACT PARITY /
TYPED AND LIVE REST-REMOUNT CLOSED / DURABLE SOURCE MEMBRANE RESTORED**

This record completes ownership migration 6 from
[`HOLONIC_MACHINE_OWNERSHIP.md`](../../../HOLONIC_MACHINE_OWNERSHIP.md).
It supersedes the prior RELAMPAGO record only for application ownership,
execution topology, source/output paths, and current rest receipts. The
earlier experimental conclusions and physical qualifications remain in
force.

## Completion boundary

The work was not complete when `ExactWorldOrgan` and an adapter interface
existed. The production boundary was the real five-episode RELAMPAGO
application:

```text
native GLM/ABI/IGRA occurrence
    -> exact optical prediction
    -> exact atmospheric inverse
    -> typed coupled-informant successor
    -> plural native current crossing
    -> later GLM return and grade
    -> admitted morphology
    -> exact typed + current + organ rest
```

The migrated conductor is now:

```text
src/soma/life/examples/eros_relampago_atmospheric_current.rs
```

The old application conductor is no longer owned by
`crates/holonic-engine/examples`. The exact laws remain in
`holonic-engine`; application composition and live conduct belong to
`life`.

## One typed transaction, not two copied worlds

`CausalWorld<CoupledInformantLaw>` continues to own the complete rational
standing:

- originating GLM prediction and source charts;
- ABI spectral sections and selected scans;
- exact receiver chronology;
- conditional atmospheric vertical fibers;
- every eighteen-coordinate branch;
- predictions, complete grades, obstructions, and admitted morphology.

`LiveCurrentMachine` owns continuing currents and incidence. It does not
receive a serialized copy of that standing.

`ExactCurrentAdapter::present_successor` now borrows the typed source event,
typed predecessor, and complete proposed successor. The
`CoupledInformantCurrentAdapter` forms exact receiver testimony from those
borrowed bodies while the full rational ecology remains with its law. A
crossing refusal discards the complete typed proposal and leaves both
machines unchanged; no observer work remains after typed commit.

`CausalWorld::from_rest` restores the typed standing together with its next
event ordinal. No universal serializer or detached event journal is
introduced.

## Eight persistent organs

The native current owns eight stable receiver organs:

```text
optical  ─┐
spectral ─┼─> prediction
vertical ─┤
chronology┘

prediction ─┐
returned   ──┴─> grade ─> morphology
```

The passages are:

| typed event | currents | directed relations |
|---|---:|---:|
| generate | 5 | 4 |
| grade complete return | 3 | 2 |
| admit graded return | 2 | 1 |

An organ is founded by its first actual typed face. There is no placeholder
source face and no receiver is called into existence before it participates.

Each face is an ordered structural quotient of exact source identifiers and
population counts. A `u64` carrier is represented as a distinct slot tag
plus exact low/high 32-bit words; it is not narrowed to a large scalar or
approximated. These faces are receiver testimony about the typed ecology,
not a replacement for its rational content.

The adapter rests in exactly 40 native words (160 bytes). Its lineage
references are validated against the independently remounted live machine
before recovery.

## Real recurrent run

The production card-primary command is:

```text
cargo run --manifest-path src/soma/Cargo.toml -p life --release \
  --example eros_relampago_atmospheric_current
```

It crossed:

| receipt | exact value |
|---|---:|
| native GLM events before geographic restriction | 923,068 |
| conditioning occurrences | 12,523 |
| held-out occurrences | 21,777 |
| successive held-out episodes | 5 |
| generated coupled relations | 45,731 |
| conditional vertical fibers | 16,817 |
| final positive front | 311 |
| final negative obstruction front | 28 |
| retained together branches | 18,285 |
| retained apart branches | 16,564 |
| continuing native organs | 8 |

The application again retained the established controls:

- every generated relation preceded its own native GLM group return;
- the complete grade preceded admission;
- reversing administrative source delivery while preserving receiver
  chronology returned equal coupled predictions;
- the ecology which received no group returns did not fabricate a forced
  relation; and
- missing, open, conflicted, and obstructed alternatives remained typed.

The exact live standing changed only when a returned passage caused a new
structural section:

| episode | passage | cells before | cells after |
|---:|---|---:|---:|
| 1 | generate | 0 | 0 |
| 1 | grade | 0 | 0 |
| 1 | admit | 0 | 0 |
| 2 | generate | 0 | 1 |
| 2 | grade | 1 | 2 |
| 2 | admit | 2 | 2 |
| 3 | generate | 2 | 11 |
| 3 | grade | 11 | 19 |
| 3 | admit | 19 | 19 |
| 4 | generate | 19 | 35 |
| 4 | grade | 35 | 47 |
| 4 | admit | 47 | 55 |
| 5 | generate | 55 | 78 |
| 5 | grade | 78 | 93 |
| 5 | admit | 93 | 102 |

Rank remained eight. Zero cell growth is a valid crossing receipt: a
continuing carrier can change or return without fabricating another
standing constituent.

## Host/card equality

The normal application path mounts:

- the existing exact optical relation executor on the RTX 4080 SUPER; and
- `CudaLiveCurrentExecutor` for the eight-organ current.

`SOMA_RELAMPAGO_HOST=1` is an explicit exact grading configuration for the
native current, not an implicit fallback. A separate complete host run used
the same typed chronology and source bytes.

The card and host runs were byte-identical for:

- the 31,406,829-byte typed coupled standing;
- the next typed event ordinal;
- the 44,484-byte live-current rest;
- the 160-byte organ rest;
- all 15 live crossing receipts;
- all five coupled-relation populations;
- all five complete coupled grades;
- every vertical-fiber population; and
- every lifted-relation population.

Current authoritative hashes are:

```text
typed standing
ee3ac49a32ca786b0e2909a50eade7f603aa2d2b5f9cb6efff5a3b9b82fcd670

live current
945f5e7a9c145242f1ac1a758067793b61e604972909219389f51510355c403f

eight-organ rest
6fabd45f007baede5f411497bf783548a21d4fe2ddbf0bc04c2f2d5f6e2c2cd3

crossing receipts
a3bd0a5ba7cd747a803e49b5bf0f10eb93a1772e8c502ec03c34cb57c1317768
```

Executor names, filesystem spellings, and wall-clock measurements are
apparatus testimony and are expected to differ. No performance conclusion
is drawn from this parity run.

## The real application exposed two implementation defects

### A debug assertion cannot own a transition

`SparseOrdinalAtlas::try_found` originally performed page insertion inside
`debug_assert!`. Debug builds therefore passed, while optimized builds
compiled the insertion away and advanced the atlas counters without
retaining the body. The first real optimized crossing returned an invalid
event dependency.

Insertion is now unconditional. The assertion examines only its returned
prior value. `holonic-structure` passes the same sparse population tests in
both debug and release profiles.

This was not a defect in ordinal paging or in the current law. It was a
classical implementation mistake which only a production optimized
occurrence exposed.

### Independent CUDA owners must reactivate their contexts

The optical executor and Soma current executor each owned a valid CUDA
context and valid handles. CUDA current-context selection is thread-local.
After optical work made its context current, the current executor attempted
to use a module founded in its own different context and the driver returned
error 400 (`CUDA_ERROR_INVALID_HANDLE`).

The safe `mount::Context` now exposes checked `make_current`. A retained
current executor reactivates its owner context before enactment, physical
settlement, context-sensitive inspection, and field teardown. Its context is
the last field destroyed. The root exact-relation owner independently
follows the same ownership rule. The retained exact aperture executor was
also corrected during the ownership audit: every device trace and teardown
reactivates the context which founded its module and allocations, even
though RELAMPAGO did not invoke that presentation path.

An optimized regression mounts a foreign context between successive
native-current events. Founding, recurrence, return, departure, and later
RIDE remain host-exact. The production RELAMPAGO run demonstrates
coexistence of both independent device owners.

## Source and output ownership correction

The earlier structural record incorrectly stated that cleanup deleted no
dataset. The historical RELAMPAGO sources and receipts had been placed
under Cargo's `target/` tree; `cargo clean` correctly treated that entire
tree as disposable and removed them. Source code and research records were
not lost, but the data and generated receipts were.

That placement was the architectural defect. It is now corrected:

```text
data/relampago-lightning/    immutable acquired source membrane
output/relampago-lightning/  generated experiment testimony
target/                      rebuildable compiler artifacts only
```

`scripts/acquire-relampago-current.sh` reacquires the exact public source
keys:

- 60 NOAA GOES-16 GLM products over 22:50--23:10 UTC;
- ten NOAA GOES-16 ABI products: bands 08/09/10/11/13 at two scans; and
- the NOAA NCEI IGRA `ARM00087344` archive.

The durable manifest receipts are:

```text
GLM key manifest
1e13333316681ee15c0faaef6dbd55139fa587457ec9152c2b3ec0d4726a6c29

ABI key manifest
3ee243ba57ddf3ff01dea516d3a72011a72ffe39627a5ac9f910809436f62bbd

complete source hash table
2fa572bf9d77b4248a8bc301d895ea8fae25395b9f018c1aac242dbd32421338

IGRA archive
34b58f84a0d3556862041b8f5ecc1129907138e566368b781acbf3cf1eb7d4d4
```

The profile's causal source is the stable
NOAA/station/time declaration carried by the archive. Its local storage
path remains acquisition testimony and does not become profile identity.

The current generated authority is:

```text
output/relampago-lightning/coupled-informant-generation/
```

The existing terminal image and video hashes remain:

```text
image  1aead377d6251012f8fd87be1ac6960e5a007b7e78a87ed281b5f80076c0b6eb
video  f0794e8fce48d6a0cb1edd53d8b1382686702c62d1639928795043065e1f95d1
```

They remain downstream receiver testimony, not the completion criterion for
this migration.

## Verification

The following gates pass:

- `cargo test -p holonic-structure`;
- `cargo test -p holonic-structure --release`;
- `cargo test -p holonic-engine world::tests --lib`;
- `cargo test -p holonic-engine --lib` — 212 passed, 2 device tests ignored;
- `cargo test --manifest-path src/soma/Cargo.toml -p life
  coupled_informant_current::tests --lib`;
- `cargo test --manifest-path src/soma/Cargo.toml -p life --lib` — 448
  passed, 9 device tests ignored;
- the optimized foreign-context CUDA lifecycle test;
- the optimized plural coupled-informant CUDA crossing test;
- `cargo check --workspace`; and
- `cargo check --manifest-path src/soma/Cargo.toml --workspace`.

Both complete real RELAMPAGO runs also passed their internal typed
validation, delivery-order control, no-return control, rest/remount check,
and source digest emission.

## Exact boundary after migration

This construction does not claim that the native current quotient replaces
the full rational law. It is the live structural testimony through which
that typed law now conducts.

The eighteen-coordinate coupled-informant successor is still derived by the
exact 24-worker host reference law. The application now uses the card for
the optical relation ecology and for the plural native current crossing; a
future device realization of the complete coupled rational phase law still
owes exact parity with the typed host successor. That is an executor
realization boundary, not a question about whether heterogeneous
conditioning, prediction, return, or recurrent conduct works.

The physical qualification also remains unchanged: GLM group membership is
the grading receiver and the IGRA/ABI height is a conditional thermal
fiber. Independent channel altitude, electric field, or charge-density
testimony did not enter this run.
