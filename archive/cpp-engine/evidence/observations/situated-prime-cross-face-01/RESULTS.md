# SITUATED PRIME CROSS-FACE 01 — RESULTS

**Date:** 2026-07-21

**Grade:** BUILT / HOST-MEASURED / EXACT SUCCESSOR SUPPORT READ / NO CROSS-FACE FORMED / NO SOMA
CHANGE / NO CUDA / NO VISUALIZATION

**Artifact:** `CROSS_FACES.json` — 3,767 octets — SHA-256
`1bd2812fc72784e468823d8fe7222e48ccdc686026e45610c60b70b35683d773`

## Outcome

The selected `prime:23` event has six genuinely co-present live currents, but their successor
populations do not intersect. The analyzer retained the enacted contribution population only
until the machine supplied its successor rank, then grouped it with the exact grounding relation
used by the scalar successor.

```text
body contributions          17
event incidences             86
formed contact emissions     64
open contacts                22
complete contributions       81
grounded supports            21
single-current supports      21
mixed-current supports        0
interface-capable arms        0
closed cross-faces            0
```

The 21 supports exactly account for standing growth from 23 to 44 cells. Both standing cuts retain
zero higher-grain constituents. The currents therefore fold internally while remaining disjoint:

| Current face | Body contributions | Formed / open contacts | Grounded supports |
|---|---:|---:|---:|
| zero-relative | 5 | 16 / 0 | 6 |
| radix 2 | 3 | 22 / 0 | 4 |
| radix 10 | 0 | 0 / 16 | 0 |
| radix 16 | 4 | 16 / 0 | 5 |
| `S_4` receiver | 4 | 10 / 0 | 5 |
| cyclotomic receiver | 1 | 0 / 6 | 1 |

No automatic seam belongs in the engine on this evidence. Co-presence is not incidence, and the
fact that the world derived all six faces from `23` is not itself a transported interface. A
cross-face experiment now needs an actual source event whose ports and hand create shared support
or a jointly formed regional interface.

## Reproduction

From `src/soma/` against a create-new output path:

```text
cargo run -p life -- historical boundary polyglot-geometric-cross-face \
  observations/bounded-polyglot-geometric-world-01/WORLD.plan.json \
  observations/situated-prime-cross-face-01/CROSS_FACES.json
```

Focused acceptance:

```text
cargo test -p life situated_cross_face_read_does_not_invent_event_interior
1 passed / 0 failed
```

The capture delegates enactment and settlement to `HostLiveCurrentExecutor`; it neither alters
the event nor reconstructs the successor. The exact source and deposited interpretation are in
`RESEARCH/2026-07-21_THE_OCCURRENCE_CROSSES_THE_OBSERVER_CANNOT_INVENT_ITS_INTERIOR.md`.
