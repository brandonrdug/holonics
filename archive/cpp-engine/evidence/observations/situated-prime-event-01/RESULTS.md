# SITUATED PRIME EVENT 01 — RESULTS

**Date:** 2026-07-21
**Grade:** BUILT / HOST-OBSERVED / EVENT-LOCAL SOURCE AND RADIATION WHOLE / NO ENGINE CHANGE /
NO CUDA / NO VISUALIZATION
**Observation:** `OBSERVATION.json` — 629,940 octets — SHA-256
`e3deebd0a62859249d5be8b807649202e30b910c209554576b5f81d1d5bdc554`

## Outcome

The bounded instrument witnesses the actual enacted occurrence `prime:23`, not an integer-derived
observer reconstruction. It retains source chronology ordinal `3`, the six borrowed source path
complexes, their source-declared arithmetic values and odd lifts, the common exact action, each
live lineage before and after crossing, the standing identity on both sides, and every current's
complete consequence, emission, and event-incidence contact.

Candidate `17` is an explicit negative control. It is present in the world-derived zero-relative
prime census, but it has no source-event ordinal and its status is `not_enacted`. No current,
contact, successor, or return is attributed to it.

## The actual `23` cut

The six source currents are:

| Current | Role | Cells | Internal incidences | Ports |
|---:|---|---:|---:|---:|
| 0 | zero-relative | 17 | 16 | 9 |
| 1 | radix 2 | 23 | 22 | 12 |
| 2 | radix 10 | 17 | 16 | 9 |
| 3 | radix 16 | 17 | 16 | 9 |
| 4 | `x^4+x+1` receiver | 11 | 10 | 6 |
| 5 | `Phi_5` receiver | 7 | 6 | 4 |

The world supplies no hand between these currents:

```text
directed relations = 0
regional relations = 0
```

Every internal incidence in every source complex has one immediate returned contact row. The six
current-local emission counts are `[5,3,0,5,4,1]`; their incidence-contact counts are
`[16,22,16,16,10,6]`.

The rank-6 standing surface changes:

```text
before  23 cells  b1376cc9899076d7eaa9b20fc72495eea5e08db186ef4286678fac82836da706
after   44 cells  11659cf9f4c45b0c4289494953772e4a9866feffb846eb5f474f1e7eb54f5839
```

Those extents agree exactly with the complete radiation's before/after fields.

## Corrected return origin

The committed 2026-07-19 report is historical testimony and does not describe the present source.
It recorded the first emissions at `23`; the current host run selects its later-return relation at:

```text
source occurrence       prime:11
source chronology       1
current / role          0 / zero-relative
lineage                 0
emission                0
selected arm            chi_other
originates at prime:23  false
```

The `23` witness therefore points to that exact earlier origin. It does not relabel one of its own
18 emissions as the world-selected return.

## Reproduction and focused acceptance

From `src/soma/` against a create-new output path:

```text
cargo run -p life -- historical boundary polyglot-geometric-observe \
  observations/bounded-polyglot-geometric-world-01/WORLD.plan.json \
  observations/situated-prime-event-01/OBSERVATION.json
```

The focused causal assertion passes:

```text
cargo test -p life situated_prime_event_is_source_bounded_and_origin_addressed
1 passed / 0 failed
```

The run is host-only. No observer or receipt enters Soma, no cross-current relation is inferred,
and no visualization was built.
