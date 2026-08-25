# Elementary holonics — Lean trust boundary

This package is the kernel-checked companion to the first dependency spine in
`src/soma/PAPERS/synopsis/`.

[definition] The maintained surface of the Millennium work, including external dependencies,
project-specific formal compositions, conditional bridges, and exact open fibres, is
[`MILLENNIUM_FORMAL_CATALOG.md`](MILLENNIUM_FORMAL_CATALOG.md).  `ElementaryHolonics.lean` remains
the complete Lean import face.

It presently checks:

- typed relations, identity, and associative composition;
- receiver equivalence and exact factorization through a declared compression;
- the separation of occurrence identity, carrier equality, and receiver-face
  equality, including a checked counterexample to the converse implication;
- ordered transition traces and derived extensional semantics;
- invertible state rebase as conjugacy, including semantic invariance;
- finite telescoping, closed-cycle exact-potential cancellation, and the finite geometric
  remainder;
- exact numerator--denominator Swing transport under affine change, with the
  scalar cross-ratio retained only as a derived quotient receiver;
- the actual Mathlib `RiemannHypothesis` proposition; and
- route/programme interfaces which force both equivalence arrows and keep the source obligation
  explicit.

It does **not** prove RH. It does not encode RH as integer square root, an inhabited `OPEN` type, or
a finite zero list. It does not claim that every Typst derivation is formalized.

Lean's `ℝ` and `ℂ` are exact mathematical structures. Classical mathematics and Mathlib are
permitted; assumptions are inspected rather than prohibited by slogan.

The old `src/labyrinth/mathematics/lean/` and `src/shrine/holon-math/` trees are historical/toy
unless a result is independently rederived into this package. The separate
`src/soma/formal/rh-source-transport/` package remains an honest finite conditional theorem and a
counterexample-guided rejected route at its claimed scope.

Run:

```sh
./check.sh
```

The checker reuses the repository's pinned Lean 4.27/Mathlib environment when present.
