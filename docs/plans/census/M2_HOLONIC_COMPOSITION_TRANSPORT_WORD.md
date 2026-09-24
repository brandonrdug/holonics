# M2 group-valued TransportWord owner

This bounded owner move follows the verified M2 receiver extraction at `c512d37f` (PR #130). The cut was rebased onto that exact source before verification.

## Declaration ownership

`Foundation/TransportWord.lean` now owns the generic order-blindness result and the
permutation-valued word transport family formerly declared in `Millennium/HolonicComposition.lean`:

- `chronology_discard_iff_commuting`
- `additiveTranslation`, `additiveTranslation_apply`, `additiveTranslation_mul`
- `parallelTransport`, its nil/additive/append/reversal laws, `identityLoop_holonomy`,
  `serialLoop_holonomy`, `rebasedHolonomy`, and `changeOfBasepoint_holonomy`

These declarations now live in `Soma.Holonics.Foundation.TransportWord`. The owner imports only
Mathlib; it does not import Lineage or ComparisonCell. The order-blindness statement uses the
generic `OrderBlind` law already in this source owner. The definitions and proofs are actual moves:
the old declarations were removed from HolonicComposition, with no aliases or duplicate proofs.

`Millennium/HolonicComposition.lean` directly imports the new owner and retains its Swing and
realization research, connection comparison, finite noncommuting controls, and receiver-insufficiency
examples. Its existing eight direct Research consumers remain present. The consumers that also use
group-valued word actions import the core owner explicitly: `HolonicCurvedArcEinstein`,
`HolonicDiscreteMaxwellOperator`, `HolonicFourForceSectorCarrier`, `HolonicConnectionCurvature`,
and `HolonicPolygonGyroWinding`. Other current users continue to obtain their needs through their
existing owners.

Direct importers of `Foundation.TransportWord` after this packet are `Foundation.HigherDifferenceTransport`,
`Foundation.ReceiverHistoryCompression`, `Framework.Core`, `Millennium.Chronology`,
`Millennium.HolonicComposition`, `Millennium.HolonicConnectionCurvature`,
`Millennium.HolonicCurvedArcEinstein`, `Millennium.HolonicDiscreteMaxwellOperator`,
`Millennium.HolonicFourForceSectorCarrier`, `Millennium.HolonicPolygonGyroWinding`,
`Physics.ConformationResponse`, and `Transport.ReceiverPotential`.

The eight direct Research importers of `Millennium.HolonicComposition` remain:
`HolonicAlternatingGeometry`, `HolonicCurvedArcEinstein`, `HolonicDiscreteMaxwellOperator`,
`HolonicClockedPantographicSwing`, `HolonicFourForceSectorCarrier`, `HolonicUnknotting`,
`HolonicSlingTransport`, and `HolonicTorusParametronRealization`. All eight retain their current
Research import and source-specific consumers. The group-word callers also import the core owner
directly; indirect callers updated here are named above.

## Source import closure

Counts follow project `import ElementaryHolonics.*` lines, include the root itself, and exclude
Mathlib and Lake jobs. The before graph was measured at predecessor source `eb0f76b7`; after reflects this packet. The receiver-extraction rebase does not alter these owner-edge counts.

| Source root | Before modules / lines / Millennium | After modules / lines / Millennium | Effect |
|---|---:|---:|---|
| `Foundation.TransportWord` | 1 / 146 / 0 | 1 / 235 / 0 | Adds the group-valued action owners without any project dependency. |
| `Millennium.HolonicComposition` | 17 / 3,882 / 9 | 17 / 3,898 / 9 | No source-closure module change; the generic declarations remain in its imported Foundation closure. |
| `Framework.Geometry` | 51 / 14,127 / 10 | 51 / 14,143 / 10 | No Research edge is cut yet: this is the declaration-owner packet; the facade still imports HolonicComposition. |
| `Framework` | 474 / 172,461 / 277 | 474 / 172,483 / 277 | Existing overlapping Research closure is unchanged. |
| `ElementaryHolonics` umbrella | 1,390 / 485,117 / 987 | 1,390 / 485,143 / 987 | No local module or Millennium count change. |

The follow-up facade cut can remove `Framework.Geometry → Millennium.HolonicComposition` after the
remaining generic addressed-occurrence declarations have core owners. Connection and route-return
laws now live in `Foundation.ConnectionLineage`; see
[M2_CONNECTION_LINEAGE](M2_CONNECTION_LINEAGE.md). The Geometry facade direct import has been removed,
while eight direct Research imports remain for concrete composition examples.
This packet alone does not claim a smaller public-root closure.

## Focused Lake gates (verified)

Run from `formal/elementary-holonics`:

```sh
lake build ElementaryHolonics.Foundation.TransportWord ElementaryHolonics.Millennium.HolonicComposition ElementaryHolonics.Millennium.HolonicCurvedArcEinstein ElementaryHolonics.Millennium.HolonicDiscreteMaxwellOperator ElementaryHolonics.Millennium.HolonicFourForceSectorCarrier ElementaryHolonics.Millennium.HolonicConnectionCurvature ElementaryHolonics.Millennium.HolonicPolygonGyroWinding ElementaryHolonics.Framework.Geometry ElementaryHolonics.Framework
```

The combined command passed, building 9,199 Lake jobs. It covers the core owner, the Research
composition owner, all five changed direct group-word consumers, and the Geometry and public
Framework facades. The remaining direct Research importers and the umbrella were not separately
requested or claimed in this packet. The final build log is `/tmp/m2-transport-word-build.log`; it
contains no `sorry` or build error. The changed Lean source files also contain no `sorry`/`sorryAx`.
The existing `propext`, `Classical.choice`, and `Quot.sound` axiom reports are standard imported
proof machinery; no new axiom was introduced by the moved declarations.
