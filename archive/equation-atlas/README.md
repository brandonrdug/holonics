# Exterior equation atlas

> Archived 2026-09-04: superseded by Provenance under Brandon's direct instruction. The data
> remain historical research input, not a maintained navigation system. Its validator is
> [archived with the old tooling](../tooling/README.md); do not regenerate this atlas.

**Truth status:** `definition`. This directory is a curated, machine-readable research chart. It is
not the runtime topology, a parser, an AST, a CAS, a solver, a theorem checker, or evidence that
Eros recovered mathematics.

## Files

- `manifest.json` binds the schema, counts, byte extents, and SHA-256 digests.
- `schema.json` defines the storage contract.
- `equations.jsonl` stores one formulation occurrence per line.
- `relations.jsonl` stores a directed, graded multigraph over those occurrences.

Each equation is stored with its display, hypotheses, carrier, units, receiver, collapsed fibre,
source, and explicit boundary. All numerical expressions are strings. An identifier names this
catalog occurrence; it does not assert that the occurrence is the intrinsic identity of the
mathematics.

Each relation is similarly scoped by hypotheses and a receiver. A relation tagged `interpretation`
is a research correspondence, not an equality. A relation tagged `conditional` is a proposed use
whose named hypotheses remain load-bearing. `open` records a missing join rather than an invitation
to infer one.

The reusable mathematical object library remains
[`research/papers/source/mathematics/`](../../research/papers/source/mathematics). That library owns declared
definitions, lemmas, theorems, corollaries, and proofs. This directory supplies exterior material
which the future mathematics codec may mount, differentiate, and compare. Merely consulting it is
reference access, not training or native conduct.

## Graph boundary

The graph records researched relations. It does not instruct the engine to apply them. A future
native relation must still be returned through the standing incidence, formulation-span, typed
operation, chain, receiver-compression, and reconstruction-fibre owners:

```text
formulation occurrence
  -> source incidence
  -> plural typed operation complex
  -> transport / front
  -> receiver consequence
  -> residual / shortest separator
  -> ReconstructionFiber
```

Do not add a semantic edge without a truth grade, hypotheses, receiver, boundary, and source. Do not
collapse duplicate displays from distinct source occurrences. Do not store a float as a semantic
coefficient.

## Validation

The JSON Lines files can be checked without interpreting their mathematics:

```sh
jq -c . research/equation-atlas/equations.jsonl >/dev/null
jq -c . research/equation-atlas/relations.jsonl >/dev/null
```

Schema validation is an exterior file-format audit. It cannot establish that an equation, proof, or
relation is mathematically true.
