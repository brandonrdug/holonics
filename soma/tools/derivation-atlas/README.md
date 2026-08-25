# soma-derivation-atlas

An exterior analyzer for the Lean derivation atlas.

Lean remains the authority for parsing, elaboration, proof terms, and kernel checking. The Lean
executable `derivation_atlas` exports a versioned JSON bundle containing:

- the elaborated `Expr` DAG;
- current-file declaration types and theorem/definition bodies;
- source-linked term occurrences;
- before/after proof-state events from Lean's `InfoTree`.

The Rust tool validates the bundle's exact population and previously-interned-child invariant,
then emits receiver-facing summaries of recurring expression faces, goal targets, theorem-body
roots, and elaborator events. `extract` also writes a companion manifest binding the source and
bundle SHA-256 identities.

From the repository root:

```text
cargo run -p soma-derivation-atlas -- extract \
  --project soma/formal/elementary-holonics \
  --source ElementaryHolonics/Geometry/Telescoping.lean \
  --out /tmp/telescoping-atlas.json

cargo run -p soma-derivation-atlas -- inspect \
  --bundle /tmp/telescoping-atlas.json

cargo run -p soma-derivation-atlas -- corpus \
  --bundle /tmp/telescoping-atlas.json \
  --bundle /tmp/cross-ratio-atlas.json
```

Names, source ranges, syntax, and elaborator labels are exterior lineage. They do not route the
analysis or become semantic categories. Domain-specific algebraic, arithmetic, and geometric
views should be derived from the exact bundle as separate receivers.
