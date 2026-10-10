# Publication note

These are the receipts of `lean/HolonicsResearch/Zeta/ModularScatteringPairedTail.lean` and its atlas
row `rh.modular-scattering-paired-tail` (Refs #62 #63). The published source is exactly `0f6a8e47`
(tree `a012d8ac`), merged onto main.

| Packet | Pin | Result and scope |
|---|---|---|
| [composed-tail-0f6a](composed-tail-0f6a-native-v1/HANDOFF.md) | `0f6a8e47` | Fresh owner and fresh importer PASS. Each ran 34 axiom queries, and every one names only `propext`, `Classical.choice` and `Quot.sound` ([summary](composed-tail-0f6a-native-v1/VALIDATION_SUMMARY.json)). |

**Kept with this work.**
- **The first validation attempt failed before elaboration**
  ([its raw compiler diagnostic, projected](composed-tail-0f6a-native-v1/PREDECESSOR_COMPILER.stdout);
  [the failure's receipt](composed-tail-0f6a-native-v1/PREDECESSOR_ENVIRONMENT_FAILURE.json)).
  The run's object directory had no `HolonicsResearch/Zeta/ModularScatteringResidual.olean`,
  because that module is newer than the shared Lean build. The queue corrected the environment;
  the source did not change.
- **A review objection at line 205 was resolved against the pinned Mathlib.** In this pin,
  `add_le_add_right` is the additive form of `mul_le_mul_right : b ≤ c → a * b ≤ a * c`, so it gives
  the step the calc needs. The proposed replacement would not have compiled. No source repair was
  made.
- **Scope.** The run checks the fresh owner and the importer, not the whole `HolonicsResearch`
  aggregate. Native charged peaks exceeded the reservation but stayed below the unchanged ceiling,
  and the metadata peak reached its accounting cap.
- **The mathematics bounds a magnitude, not a sign, and says nothing about RH.** The paired bound is
  not uniformly better than the separate one, so both are kept with their minimum.

**Projection.** `HANDOFF.md` is the queue's own file, byte for byte.
`PREDECESSOR_ENVIRONMENT_FAILURE.json` and `PREDECESSOR_COMPILER.stdout` replace host prefixes by the placeholders in
[`ORIGINALS.json`](composed-tail-0f6a-native-v1/ORIGINALS.json). `VALIDATION_SUMMARY.json` is the
queue's validation with argv, environment, paths and identifiers dropped. Every original is pinned by
size and SHA-256 and stays in local custody.
