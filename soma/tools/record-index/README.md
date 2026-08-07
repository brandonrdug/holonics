# Soma record index

`soma-record-index` is a standard-library-only inventory tool for the laboratory record. It reads
the existing canon, research, observation records, correspondence, ledger headings, and Rust source
tree, then writes a separate set of deterministic navigation indexes.

The generated indexes are **non-authoritative maps**. They never replace or amend `FORMULA.md`,
`LEDGER.md`, research documents, observation records, or commune letters. Canonical IDs come from
the append-only `allocations.tsv` ledger. Formula handles and paths are mutable discovery aliases,
so a mechanical move updates an alias without renumbering the allocated identity. The generator
stops when a source is unallocated or an allocation no longer resolves. Content SHA-256 values are
recorded separately and never used as identities.

From `src/soma`:

```text
cargo run -p soma-record-index -- generate --out target/record-index
cargo run -p soma-record-index -- check --out target/record-index
```

Use `--root <laboratory-root>` when running outside the laboratory tree. The writer refuses output
inside authoritative record directories and refuses to overwrite any file it did not generate.
