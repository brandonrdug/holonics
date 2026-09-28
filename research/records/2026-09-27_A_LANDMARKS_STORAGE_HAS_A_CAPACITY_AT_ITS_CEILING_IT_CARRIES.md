# A landmark's storage has a capacity: at its ceiling it carries

**Date:** 2026-09-27. **Status:** [historical] declared before measurement and measured September 27
(commits `3de9d7c4` to `13267fbc`, #73); moved here verbatim the same day from THE_REBUILD's former
Decision 39 when the Decisions log dissolved into its owners ([unity audit](2026-09-27_THE_HOLARCHY_AND_ITS_AEONS_ARE_THE_TOP_THE_DECISIONS_DISSOLVE_INTO_THEIR_OWNERS_AND_LEARNING_IS_PROTOTYPED_WHERE_A_HOLARCHY_MADE_THE_TERRAIN.md), #63).

The law stands in `hnn::landmark`'s module doc ("A landmark's storage has a capacity"; Lean
`HNN/LandmarkCapacity`), and the resident tree takes the carry. The text keeps its original
numbering: "Decision N" resolves through THE_REBUILD's [Decisions index](../../docs/plans/THE_REBUILD.md#the-decisions-index).

## The declaration and the measurement (the former Decision 39)

[agent-inferred; declared before measurement] Decisions 28–37 read a landmark's counts as
exchangeable: its KT face weighs the node's first arrival as much as its latest. A landmark is a
storage on its own clock: its arrivals are its epochs (the flux through its section), and a storage
has a capacity. Decision 38's measurement located where the rings do not yet earn bits: they tick on
the cell clock, while text varies along its contexts. This decision places the dissipation on the
landmark's own clock instead. Refs #73.

- **The law.** Each node keeps its two counts `n_0, n_1` as before, carried as half-unit masses
  `2n_c + 1`. When a deposit brings `n_0 + n_1` to the ceiling `L = 2^c`, both counts carry:
  `n_c ← ⌈n_c/2⌉`. The shift is the register's carry, the helix's winding at its capacity, and a
  reached symbol keeps a count. The face is KT's on the carried counts. `c = ∞` is Decision 28's
  node.
- **Why it is lawful.** The tree weighting normalizes for any node law that emits a normalized face
  from what reached the node (`path_face_normalized`). The mixture over pruned trees and its
  dominance hold for any sequential node law. A chain's nodes route the same arrivals, so they
  carry the same register, and Decision 37's compaction is unchanged.
- **The family and its charge.** The development cells of the wide cut, at Decision 37's `D = 48`,
  choose `c ∈ {∞, 5, 7, 9, 11}`, charged `⌈log₂ 5⌉ = 3` bits. That is five passages of about
  25 s each, stated in advance. Then comes one held-out passage for the chosen law. If development
  keeps `c = ∞`, the law is recorded as rejected.
- **Consumers.** The owner is `hnn::landmark` (`Law`, its deposit and faces, both oracles). If the
  law is adopted, the receiving path and the card take it in the same step (Decision 25).
- **Lean.** The stop mixture, its Kraft form and dominance, and `compacted_is_decision_28` are
  generalized to a node law whose state is a function of the arrivals reaching the node. The
  capped register is an instance; KT is the case `c = ∞`.

**Measured (September 27).** Lean `HNN/LandmarkCapacity` gives the capped register:
- its face is positive and normalized;
- `c = ∞` is KT (`cap_unbounded_is_kt`);
- the carry only lowers counts.

`capped_tree_laws` gives the compacted capped tree with a complete prequential code. The stop
mixture, its Kraft form and dominance are now stated once, for any node weight
(`LandmarkTree.own_mixture_over_trees`, `own_kraft_and_dominance`). `compacted_is_decision_28` is
the KT case of `compacted_node_law`. In Rust the carry acts in the one `Law` right after the deposit
that brings the total to `L`, so the next face reads the carried counts. The development cells at
`D = 48` read (bits, each `+ ε`; each passage about 20 s):

| `c` | development code | against `c = ∞` |
|---|---|---|
| ∞ | `1801940 + 12/16` | Decision 37, reproduced exactly |
| 5 | `1950535 + 3/16` | `+148594 + 7/16` |
| 7 | `1827589 + 1/16` | `+25648 + 5/16` |
| 9 | `1804070 + 6/16` | `+2129 + 9/16` |
| 11 | `1801600 + 13/16` | `−340 + 1/16` |

- **The choice.** The development cells choose `c = 11`, `L = 2048`, at `−337 + 1/16 + ε` charged.
  It lies at the family's edge: the code falls as the ceiling rises. Under Decision 35's rule, a
  larger ceiling is re-swept only when the scale could change the choice, at a cost stated in
  advance. This campaign's held-out passage is spent.
- **Held out** (one passage, at `c = 11`). The tree reads `258018 + 5/16 + ε`, `1 + 15/16 + ε` a
  cell. Charged, it is below Decision 37's tree by `−180 + 1/16 + ε` and below PPM-2 by
  `−137575 + 12/16 + ε`.
- **What it located.** Dissipation on the landmark's own clock earns bits, but few:
  `−340 + 1/16 + ε` over 917504 cells. Only a ceiling of thousands of arrivals helps, and a low
  ceiling costs heavily. At these contexts the terrain is close to stationary, and the bits are in
  the depth (Decision 37), not in recency. **Adopted** for the tree at scale. The resident tree
  takes the carry, and the parity tests check it (Decision 25). The HNN's receiving path keeps its
  standing-cut declaration (`D = 4`, no ceiling), which its own development chose; the full HNN at
  scale is not yet measured.
