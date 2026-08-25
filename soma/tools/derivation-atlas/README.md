# soma-derivation-atlas

An exterior analyzer for the Lean derivation atlas.

Lean remains the authority for parsing, elaboration, proof terms, and kernel checking. The Lean
executable `derivation_atlas` exports a versioned JSON bundle containing:

- the elaborated `Expr` DAG;
- exact multiplicity-weighted expression-use edges, including root uses and child fanout;
- current-file declaration types and theorem/definition bodies;
- source-linked term occurrences;
- before/after proof-state events from Lean's `InfoTree`.

The Rust tool validates the bundle's exact population and previously-interned-child invariant,
then emits receiver-facing summaries of recurring expression faces, goal targets, theorem-body
roots, elaborator events, literal integers, multiplication-factor candidates, and algebraic figure
heads. It also returns exact operation-to-operation argument transitions and structural recurrence
towers. A recurrence tower removes the partial application nodes introduced by Lean's curried
encoding, counts complete nested occurrences of one operation, and takes successive finite
differences of that order profile. These are derived receivers over the elaborated expression DAG:
they do not identify syntactic nesting with semantic recursion or a mathematical derivative.
`extract` also writes a companion manifest binding the source and bundle SHA-256 identities.

The derived factor and figure rows are candidates with exact graph witnesses. They do not claim
commutativity, associativity, definitional equality, or a geometric interpretation unless a later
receiver proves that relation.

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

For the category-like reading, complete operation heads are objects and the reported weighted
argument transitions are generating arrows. Composable transition words can be analyzed by later
receivers; the current report stops at exact one-step arrows and same-head nesting so it does not
silently promote a quotient cycle into a theorem about the source declaration.
