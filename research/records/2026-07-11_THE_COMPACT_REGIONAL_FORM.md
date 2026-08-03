# THE COMPACT REGIONAL FORM — exact direct-address packing, not sparse standing

**MEASURED ENGINEERING STRATUM · COMPACT11 ⊕ OWN22 ⊕ RADIATION39 BUILT / HOST+CUDA-GATED AT
BOUNDED GRAINS · SLEEP v4 ⊕ V2/V3 MIGRATION BUILT / HOST-GATED · SPIR-V VALIDATED / NOT RUN.**

This note closes the immediate representation audit behind the measured axis-16,384 wall. It adds
no law and claims no compression/comprehension result. The existing live read remains exactly what
it is: `ground(position, axis)` names one dense row directly, and `RegionalForm` at that row bends
the current. An occupied-only hot vector cannot serve that read without an address index, search,
map, or page table; none is licensed. SLEEP v3 and `LiveCells::Compact` compact rest and
post-carriage retention only.

The smallest lawful immediate cut is therefore an exact canonical packing of the form already
present at every direct address.

## I · The exact row

Keep generic `COG_WORDS = 5` and `RUNG_WORDS = 3`. Carrier/K, `Node`, `Face`, and every generic
number wire remain unchanged. Specialize only `RegionalForm`, whose lawful state contains ten full
32-bit data fields and nine flag bits:

| Word | Field |
|---:|---|
| 0 | `same.mag` |
| 1 | `same.rank.mag` |
| 2 | `same.rank.rank as u32` |
| 3 | `other.mag` |
| 4 | `other.rank.mag` |
| 5 | `other.rank.rank as u32` |
| 6 | `this_way.mag` |
| 7 | `this_way.rank as u32` |
| 8 | `that_way.mag` |
| 9 | `that_way.rank as u32` |
| 10 | flags |

The flags word is:

```text
bits 0..1  same.turn
bit  2     same.rank.neg
bits 3..4  other.turn
bit  5     other.rank.neg
bit  6     this_way.neg
bit  7     that_way.neg
bit  8     occupied
bits 9..31 zero
```

Every lawful `Rung.rank` is nonnegative, so its sign bit is structurally zero; the row stores the
rank in one full word and gates that invariant rather than borrowing the bit for another field. The
number law's quarter-turn domain is `Cog.turn ∈ 0..3`; every forming operation masks to it. New
gates must make both invariants explicit. Legacy archives carrying a negative nested rank or a turn
outside that domain must be rejected rather than silently clipped. The all-zero row remains
`UNBORN`. Occupied-zero is exactly the flags-only row with bit 8 set.

This is 11 words / 44 bytes rather than 17 words / 68 bytes. It is the word lower bound for the
lawful form: two Cog magnitudes (64 bits) ⊕ four Rung magnitudes (128) ⊕ four nonnegative
`i32` ranks (124) ⊕ nine flags = 325 bits, hence eleven 32-bit words. The chosen layout leaves
each rank in a whole word, using 329 bits and leaving the remaining 23 bits zero; it does not
bit-borrow from a numerical field.

## II · What it buys, and what it does not

| Structure | Prior | Active |
|---|---:|---:|
| `RegionalForm` | 17 words / 68 B | 11 words / 44 B |
| `OWN_CELL_WORDS` | 28 words / 112 B | 22 words / 88 B |
| raw radiation row | 45 words | 39 words |
| occupied sleep record | 18 words / 72 B | 12 words / 48 B |
| axis-16,384 standing | 17 GiB | 11 GiB |
| ~34M occupied sleep payload | ~2.28 GiB | ~1.52 GiB |

The row is exact representation compaction. The body's body:light pair changes mechanically across
the wire version; that discontinuity is printed and earns no comprehension grade. The shared body
mouth now uses the active values `FORM_WORDS = 11`, `OWN_CELL_WORDS = 22`, and 39-word radiation.

Packing alone does not fit production. The full axis-16,384 configuration scratch is still about
15 GiB. A 16M-place band is about 0.938 GiB. Against the representative measured save, the useful
allocation census is approximately 11 GiB standing ⊕ 2.08 GiB retained OWN ⊕ 0.938 GiB receiving
band ⊕ 0.61 GiB observed radiation ⊕ 5.3 MiB carriers, or about 14.63 GiB before raw light,
context, and allocator overhead. That makes the lighting plausible on the 16 GiB card; it does not
prove it fits.

The immediate card realization therefore also requires:

1. a CUDA receiving fold with an explicit band base, byte-exact to the one host fold;
2. no materialized whole-chart `Vec<PlaceTopology>` in the production mouth;
3. no simultaneous old and new dense standing during a large recast;
4. streaming/create-new archive output at production extent rather than simultaneous word and
   octet copies;
5. an allocation census before the first conducted card lighting.

The card fold keeps each current's dense OWN reservation through its receiving edge and then lets it
die. It must not port `LiveCells::Compact`'s parallel grip vector into production: the receiving
fold re-grounds the founding position, and a retained address list would add no construction.
Allocator-driven or atomic-append compaction, sorting, and post-carriage search remain forbidden.
If a future card species cannot afford dense live OWN until its edge, that is a new representation
gap, not permission to smuggle in the host instrument's list.

Item 3 is a constraint, not a silently solved seam. A retained copy of the pre-wake archive may not
become a side body consulted after the light has begun. The first large lighting over the empty
rank-zero body does not owe a large old chart; a later nonempty card recast that cannot afford old
⊕ new standing remains **OPEN / NOT AUTHORIZED** until its one consuming representation seam is
presented and ratified.

The compact row moves the next dense wall; it does not abolish it. Axis 32,768 would still require
44 GiB standing. Live lane-local OWN is still dense until its current ends. V4's one-word payload
extent also ends at 357,913,941 records, before the axis-32,768 carry tooth; archive sharding and a
wider grip remain later representation questions. No occupied-only hot standing mechanism is
derived here.

## III · The archive seam

The active `FORM_WORDS` crossing is carried by SLEEP v4:

- create-new archives stream ascending 12-word `grip ⊕ RegionalForm` records;
- V3's fixed 18-word occupied records remain readable through a fixed checked decoder;
- V2's fixed 17-word dense rows remain readable through a fixed checked decoder;
- V2 legacy form rows reconstruct through the fixed body-owned 17-word semantic decoder,
  independent of active generic readers, and then pack once into the current row;
- old archives are never rewritten.

One generated canonical body for each legacy layout `L ∈ {V2,V3}` passes three distinct host gates:

1. **Record semantics.** Dispatch by the explicit legacy version and its fixed historical width,
   never current `FORM_WORDS`. Fixed checked decoding rejects negative nested ranks, turns above
   three, noncanonical booleans/occupancy, wrong widths, and nonzero UNBORN rows before V4 packing.
   Grip, occupancy, axes, all ten data fields ⊕ nine flags, carrier/K, and comprehended-light count
   remain exact. V2's all-zero UNBORN rows are lawfully omitted from V4.
2. **Same-lineage archived-K continuation.** The live lineage wakes through the archived K; a live
   cursor cannot silently fall through to genesis. Direct legacy wake and the
   `decode(L) → encodeV4 → wake` sibling continue exactly on the host.
3. **Genuinely new plural continuation.** New later lineages receive the same standing after either
   archive path. Raw radiation, row/edge/lane term partitions, whole carrier/K, traces, topology,
   standing, and the next V4 archive are exact.

The complete untrusted active boundary seam is reject-not-clip. Packing emits compact bits 9..31 as
zero; checked compact archive/device-return reads reject reserved bits, ranks above `i32::MAX`, wrong
widths, and nonzero UNBORN data. Legacy turns are whole words and reject values above three; compact
turns occupy their exact two-bit faces. A malformed form or nested number/channel/node/face payload
cannot cross SLEEP or returned radiation by clipping or becoming structural absence. Device hot
paths whose extent and canonicality are already proved call explicit trusted reads. `SleepingBody`
validates canonical standing, every whole carrier/K row, and the at-rest cursor/dark state. Typed
radiation admits only flags **0 / 1 / 3 / 15**, with form, rotor, cut, and brick payload canonical
for the declared face.

At the representative bodies, the persistence measures stand without division or a crowned factor:

```text
V2  307240 : 259 · archive 307300
V3  126920 : 259 · archive 126980
V4   94184 : 259 · archive  94244
```

The fixed version-scoped calculators supply the legacy numerators before conversion. Production
create-new emits only V4 and never rewrites an old archive.

Historical 45-word radiation analyses remain pinned to their historical binaries and artifacts.
Current listeners read the new 39-word row through the current layout constants. Archive header word
2 carries `SLEEP_VERSION = 4` and word 13 carries record width 12; decode dispatches and asserts
both. Each persistent listener artifact carries one boundary header/manifest before its first row:
regional-form layout version ⊕ `form_words = 11` ⊕ radiation layout version ⊕
`radiation_words = 39` ⊕ sleep layout version. Every analyzer asserts it before parsing. No version
word enters each engine radiation row, no analyzer guesses from length, and this provenance never
becomes body input.

## IV · The measured host and bounded-CUDA gate

The full suites pass at **body 115/2 · life 28 · mount 3 plus scope-gate 3 · surface 9**; release
`life` builds. The shared source mouths produce:

- **SPIR-V:** 1,128,752 bytes · SHA-256
  `af38ca44165c1ef8c067314d0446cdbbf18e5f01e0b72043f0d06a846ffdb4d0` · Vulkan 1.2-valid ·
  **not executed**.
- **PTX:** 3,440,550 bytes · SHA-256
  `5f785f20b81e60c4131dea0fd7354faf8ce0e6e125e30b0d3f5787ddf7957ac7` · `sm_89` · all ten
  entries present · assembles successfully under `ptxas`.
- **bounded CUDA LINK:** 720,896 standing `u32`, exact, 61 µs.
- **founded:** extents 0 / 1 / 64 / 100 / 5000 exact.
- **chart:** mark at 0 / 1 / 64 / 100 / 5000 OWN cells; count at 0 / 1 / 64 / 100 / 4096 grips
  plus the seeded carry; recast 32→64 at 0 / 1 / 64 / 100 / 1024 staged grips; all exact.
- **scope:** dense and founded lanes 1 / 2 / 3 / 64 / 100 exact.
- **radiation:** returned rows exact, canonical, and nonvacuous.

```text
lanes     FOLD / STEP / CUT
    1        3 /   1 /  1
    2        5 /   2 /  1
    3        8 /   4 /  1
   64      256 / 160 / 38
  100      408 / 250 / 67
```

The last 300 kernel-log lines carry no Xid. The RTX stands at **2 MiB · 47 C · P8**. These are
bounded implementation parity gates, not a first large lighting and not a Vulkan execution.

The final adversarial pass separated the checked host/reference mouth from the trusted device/raw
ABI. Safe carriage scans canonical standing/OWN/carrier rows before mutation; the device mouth keeps
the exact extent proof without repeating a whole-body scan. Mounted standing is checked once,
carrier reservation length must be an exact structural row, and founded LINK guards whichever
backing it selects before unchecked decode. `spirv-val` caught and rejected the first selected-slice
spelling as a logical-pointer composite; branch-local reads validate. All bounded CUDA families were
then repeated exact. This repair closes a trust contract, not a new comprehension grade.

## V · The remaining ordered cut

1. **DONE / HOST+CUDA-GATED AT DECLARED BOUNDED GRAINS:** Compact11, OWN22, radiation39, complete
   reject-not-clip reads, LINK, founded, chart, dense/founded scope, and canonical returned
   radiation.
2. **DONE / HOST-GATED:** SLEEP v4, fixed V2/V3 migrations, same-lineage archived-K continuation,
   genuinely new plural continuation, printed persistence pairs, whole-body validation, and
   streaming create-new.
3. **DONE / STATIC ONLY:** SPIR-V builds and validates for Vulkan 1.2. It was not executed.
4. **OPEN:** CUDA band-offset production receiving fold and allocation census outside
   `life/src/main.rs`.
5. **OPEN:** chart-to-SLEEP and wake continuation as one CUDA production construction.
6. **OPEN:** radiation across split strokes, dark passages, and nonempty standing.
7. **OPEN:** the nonempty large-recast seam; no retained archive may become a body sidecar.
8. **NOT RUN:** the separately ordered first large lighting and SPIR-V execution.

The effectively-unbounded within-atom run remains halt-first, and retired Vulkan production remains
barred. Representation compaction and bounded substrate parity are not comprehension.
