# Holonics symbolic mathematics notebook

This is a personal mathematical research surface. It is not an engine phase, a construction
receipt, or a source of standing for the holonics repository.

The notebook assumes familiarity with ordinary linear-algebra computation. It does not use
arbitrary numerical substitutions as a default route to understanding. Its primary object is a
family of coupled symbolic relations and the geometry of the fibers, strata, transports, and
obstructions those relations define.

The first unit is **The geometry inside a characteristic receiver**. It studies the symbolic map

```text
Mat₂(K) → A²,      M ↦ (tr(M), det(M))
```

by unfolding named operations into the entries `a,b,c,d`, changing coordinates, locating the
discriminant strata, describing whole receiver fibers, and deriving the infinitesimal directions
caused by conjugation.

It is deliberately adjacent to R33 without stating the closed commutator trace law under active
source separation.

## Surfaces

- `book/main.typ` renders the open symbolic workbench.
- `book/solutions.typ` renders the derivation companion.
- `book/figures/` contains native vector construction diagrams tied to the symbolic relations.
- `lean/U001Trace.lean` checks the same relations as general polynomial identities.
- `attempts/sheet.typ` renders a blank symbolic algebra canvas for handwriting.
- `ledger/questions.typ` records unresolved relations without forcing them into exercise answers.

## Build and check

From the repository root:

```sh
./notebook/check.sh
```

This produces:

- `notebook/build/notebook.pdf`, the open workbench;
- `notebook/build/notebook-solutions.pdf`, the derivation companion;
- `notebook/build/notebook.png`, a first-page preview; and
- `notebook/build/attempt-sheet.pdf`, a reusable symbolic algebra canvas.

The command also checks `notebook/lean/U001Trace.lean` through the repository's pinned
`formal/elementary-holonics` Lean/Mathlib environment without modifying that package.

## Figure grammar

The diagrams are not screenshots or decorative surfaces. Each one distinguishes:

- the source chart or reference incidence;
- the coordinate or algorithmic transport;
- the resulting receiver fiber or stratum;
- auxiliary and tangent directions; and
- what the visible construction forgets.

The current sources are `characteristic-map.svg`, `quadric-fibers.svg`, and
`fiber-transport.svg`. They can be edited independently of the prose while remaining vector-native
inside the Typst render.

## Suggested motion through a unit

This is not a required sequence. It records the mathematical motion the artifact was built to
support:

1. Expand every named receiver into its coupled variables.
2. Search for a change of coordinates that exposes the relation's geometry.
3. Hold a receiver fixed and describe the whole source fiber.
4. Vary one coupling symbolically and solve for the locus where the qualitative case changes.
5. Find transformations tangent to or acting inside the fiber.
6. Ask which parts are intrinsic and which depend on the chosen chart.
7. Use Lean to check a general identity, not a list of evaluated instances.
8. Change the formal statement or coordinate map and observe which proof obligation changes.

Handwritten pages may be stored as `attempts/U001/U001-A01.pdf`. Only the object, coordinate map,
derived relation, and unresolved question need to be transferred into the searchable Typst record.
