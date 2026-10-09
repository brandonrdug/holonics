# HelicalRepair: targeted kernel and import acceptance

Source `5efbb1cc0c2735b676206bc1daf15a0cfe532907`, tree `0f824a10c52bb89f329943f59e8fe31b9ec9a892`.

The complete submitted module compiled with exit zero. All 56 exact declaration axiom selectors matched and used only `propext`, `Classical.choice` and `Quot.sound` (or no axioms). The added research import at line 298 was consumed by a narrow private importer: all eight exact selectors passed against the newly accepted source-matched provider object. Every pre/post import metadata check remained unchanged. No source repair was needed.

| Stage | Wall ns | Fixed projection ns | Aggregate CPU ns | Group peak B | Child peak RSS KiB |
|---|---:|---:|---:|---:|---:|
| module-prep | 8688968644 | 17000000000 | 6576092000 | 808501248 | 323296 |
| module-compile | 12559016470 | 21132554884 | 7033358000 | 4122607616 | 3289672 |
| import-prep | 10728050484 | 17000000000 | 7885647000 | 845557760 | 323320 |
| import-compile | 10598571635 | 21132554884 | 4895614000 | 4439425024 | 3330860 |

Actual compiler wall: module 10534647580 ns; import consumer 8224600457 ns.

Preparation remained separate under the existing 17,000,000,000 ns CPU/wall and 4,294,967,296 B group ceiling. Each compiler used one CPU, the unchanged 17-second child and 17,000,000 us aggregate CPU cap, existing 21,132,554,884 ns complete wrapper ceiling and authorized 8,589,934,592 B group maximum. The module preparation sealed every consumed source and ordered object part: 4,523 modules and 27,656 bound paths. Same-source parsed-header reuse did not substitute for the current complete ordered seal. Every stage has final acceptance, owned cleanup and a matching quiescent shared-lease release.

Accepted mathematics: exact unreduced carried support for independent nonempty factors at admitted positions, product and bounded-increment interval cardinality bounds, and the equality of finite coordinate suprema with family diameter. Constancy/zero statements retain the explicit reflexive and separating-distance hypotheses. The terminal carry is included through its declared coordinate level.

Scope excludes fit-constrained/pruned support exactness, damaged-channel truth coverage, construction of an actual receiver quotient, diameter-attaining witnesses, machine work/memory/overflow realization and the general partner law. Neither the full HolonicsResearch root nor a broad Lean/Rust/HNN/GPU run was performed. The default Framework closure is unchanged.

[Machine-readable validation](VALIDATION.json). Whole native module output: [stdout](admission/compiler.stdout), [stderr](admission/compiler.stderr). Whole import output: [stdout](admission/import-smoke/compiler.stdout), [stderr](admission/import-smoke/compiler.stderr). Frozen original source, appended query-only compiler source, accepted objects, complete import seals, raw diagnostics, controls and time/memory/release receipts are preserved here.

No scientific source was edited. These receipt files are local and uncommitted for the parent’s source-pinned review/publication ownership.
