# M2 geometry carry and pair-resonance curation

This bounded source cut follows the M2 Ratio exponential-kernel cut at `42eb1693`. Verification is
pending coordination with the root; no Lake builds were run for this cut.

## Declaration ownership

`Transport/HelicalPairInteraction.lean` now owns
`Soma.Holonics.Transport.HelicalPairInteraction.phaseTransport_add_carried_period`, next to the
other `phaseTransport` group laws. It concerns transported material under a carried period and
uses `phaseTransport_add`, so the declaration belongs with that operation.

`Geometry/PhaseCarry.lean` retains its natural/integer phase, winding and carry laws, the ZMod
counterexample, odometer, and independent group-power theorem `zpow_add_mul_carry`. It no longer
imports or opens `Transport.HelicalPairInteraction`.

`Geometry/PairResonance.lean` no longer imports `Millennium/Farey`. Its
`neighbours_iff_unimodular` theorem depends only on the integer determinant chart, not on a
declaration from Farey. It remains in the elementary Geometry owner. The broader Farey address
theory and all declarations in `Millennium/Farey` remain unchanged. No forwarding aliases were
introduced; the moved phase-transport theorem has no source callers beyond its former declaration.

Direct source importers on this stack:

| Owner | Direct importers after this cut |
|---|---|
| `Geometry.PhaseCarry` | `Framework.Geometry`, `Holon.Generator`, and the `ElementaryHolonics` umbrella |
| `Geometry.PairResonance` | `Framework.Geometry` and the `ElementaryHolonics` umbrella |
| `Transport.HelicalPairInteraction` | `Framework.Objects`, `Framework.Dynamics`, `Transport.GeneratorTraceFaces`, `RH.ZeroPairLock`, `Geometry.PairResonance`, and the `ElementaryHolonics` umbrella |
| `Millennium.Farey` | the `ElementaryHolonics` umbrella |

## Source import closure

Counts follow project `import ElementaryHolonics.*` lines, include the root itself, and exclude
Mathlib and Lake jobs. The before graph is the `42eb1693` source; after reflects this cut.

| Source root | Before modules / lines / Millennium | After modules / lines / Millennium | Effect |
|---|---:|---:|---|
| `Geometry.PhaseCarry` | 15 / 3,471 / 7 | 1 / 184 / 0 | Removes its sole HelicalPairInteraction edge and the resulting local closure. |
| `Geometry.PairResonance` | 17 / 3,654 / 9 | 15 / 3,399 / 7 | Removes the unused Farey edge and `Millennium.Towers` beneath it. |
| `Holon.Generator` | 35 / 8,845 / 17 | 30 / 7,336 / 16 | Loses five modules and the Snell research path formerly reached through PhaseCarry. |
| `Framework.Geometry` | 61 / 16,800 / 17 | 59 / 16,524 / 15 | PairResonance loses only the Farey/Towers branch here; Helical remains reachable through PairResonance. |
| `Framework` | 476 / 172,742 / 279 | 474 / 172,466 / 277 | Same two-module Farey/Towers reduction; independent research edges remain. |
| `ElementaryHolonics` umbrella | 1,390 / 485,126 / 987 | 1,390 / 485,122 / 987 | No net change: the umbrella imports both Farey and Towers directly. |

These are source graph counts only. They do not predict Lake jobs or claim a research-free facade.
`Framework.Geometry` still imports `Millennium.HolonicComposition` and `Millennium.Rigidity`,
among other research paths. `PairResonance` still needs HelicalPairInteraction for its two
contact-power `lock_*` declarations; this cut does not move or alter those laws.

## Focused Lake gates (pending)

Run from `formal/elementary-holonics`:

```sh
lake build ElementaryHolonics.Transport.HelicalPairInteraction
lake build ElementaryHolonics.Geometry.PhaseCarry
lake build ElementaryHolonics.Geometry.PairResonance
lake build ElementaryHolonics.Holon.Generator
lake build ElementaryHolonics.Framework.Geometry
lake build ElementaryHolonics.Framework
lake build ElementaryHolonics
```

These gates cover the new theorem owner, the reduced carry owner, the direct Geometry importers,
and the affected subject/public facades. Build results and logs are to be recorded after the
coordinated gate run.
