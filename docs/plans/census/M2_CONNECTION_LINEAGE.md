# M2 addressed connection lineage owner

This packet follows the M2 `Foundation.TransportWord` extraction at `1237c8e3`. It moves the generic connection laws that consume a complete `AddressedPassage` occurrence and its retained route comparison into an elementary Foundation owner. The data and hypotheses stay explicit: connections map each occurrence to a permutation (an invertible fibre action); receiver changes may be noninvertible, but route descent is stated only with both route-intertwining equations and uses injectivity/surjectivity only for the corresponding flatness conclusions.

## Declarations moved

`Foundation/ConnectionLineage.lean`, under `Soma.Holonics.Foundation.ConnectionLineage`, now owns the former generic block in `Millennium/HolonicComposition.lean`:

- `AddressedConnection`, `connectionTransport`, `joinedConnectionTransport` and serial-composition law;
- `rebaseTransport`, its application, multiplication and inverse laws;
- `routeComparisonReturn` and its flatness criterion;
- `AddressedConnectionComparison` and its occurrence, route transport and returned-curvature readings;
- rebase naturality of a route return;
- `RouteScalePassage`, including inverse naturality, returned-curvature naturality, injective fine-flatness, surjective coarse-flatness and bijective equivalence;
- the two-route commutator return and its equivalence with commuting directions.

The owner imports only `Foundation.Lineage`, `Foundation.ComparisonCell`, and Mathlib permutation algebra. These are declaration moves with direct imports and no forwarding aliases. The `AddressedPassage.ComparisonCell` for genuinely noninvertible route comparison remains the typed receiver defect: it is not promoted to a permutation connection. A coarse receiver can erase a route defect; this is why the naturality hypotheses and the injective/surjective conclusions remain separate.

## Research and facade callers

`Millennium/HolonicComposition.lean` now imports the owner and retains its concrete Swing realization, occurrence-word examples, finite noncommuting and collapsing-receiver controls, and later receiver-history examples. The owner checks the preservation of the ordered route return while the finite controls stay in Research.

The three Research modules that consume the moved declarations import the owner directly: `HolonicClockedPantographicSwing`, `HolonicCurvedArcEinstein`, and `HolonicFourForceSectorCarrier`. `HolonicConnectionCurvature` documentation now points to the new owner. The `Framework.Geometry → Millennium.HolonicComposition` direct import was removed; its other elementary imports suffice. This records one removed direct facade edge, without claiming that no other transitive Research path reaches HolonicComposition.

Eight direct Research imports of `Millennium.HolonicComposition` remain: `HolonicAlternatingGeometry`, `HolonicClockedPantographicSwing`, `HolonicCurvedArcEinstein`, `HolonicDiscreteMaxwellOperator`, `HolonicFourForceSectorCarrier`, `HolonicSlingTransport`, `HolonicTorusParametronRealization`, and `HolonicUnknotting`. They are not all removed by this packet: their concrete proofs still consume Swing/realization/occurrence or finite instance constructions. A follow-up facade cut needs to classify and move any remaining reusable declaration separately; this packet does not retitle those research results as Holonic laws.

## Focused gates

The verified Lake targets were `Foundation.ConnectionLineage`, `Millennium.HolonicComposition`, `Millennium.HolonicClockedPantographicSwing`, `Millennium.HolonicFourForceSectorCarrier`, `Millennium.HolonicCurvedArcEinstein`, `Framework.Geometry`, and `Framework`. They built successfully after the source edits; the final combined gate rebuilt 9,197 jobs from the isolated cached project build. The Research owner audit names resolve through the new declaration namespace. No `sorry` or new axiom was introduced. Existing uses of standard imported proof axioms remain unchanged.

The focused build log is `/tmp/m2-lineage-final-build.log`; the isolated `HolonicComposition` refresh is `/tmp/m2-lineage-comp.log`.
