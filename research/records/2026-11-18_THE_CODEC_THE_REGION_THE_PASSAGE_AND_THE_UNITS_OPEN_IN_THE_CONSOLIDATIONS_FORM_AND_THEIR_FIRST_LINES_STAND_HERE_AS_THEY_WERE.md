# The codec, the region, the passage and the units open in the consolidation's form, and their first lines stand here as they were

November 18, 2026, 22:43 UTC. Refs #603 (C7). This record is a move, not a derivation. Four modules of `crates/engine` kept their own
first lines when the seventeen modules cut from `field.rs` took the form of
[THE_CONSOLIDATION §5](../../docs/plans/THE_CONSOLIDATION.md#5-the-engines-cut-by-object) on November 15: `codec`, `region`, `passage`
and `units`. From this date each opens in that form: its object; its equations in the present tense at their declared widths; its kind
of computation and its index; the kernels that realize it; its Lean owner; its atlas rows; its records. The first lines each one held
until now stand below word for word, as they were at
[`13d4ba48`](https://github.com/brandonrdug/holonics/tree/13d4ba48/crates/engine/src), because a header holds nothing dated and three of
these held the date of a move and one the reasons of October 23.

The change is to comments alone. No item, no statement and no printed line of the four modules changed, and no kernel was touched, so
no digest moved and parity is not in question.

## What each header now states, and where it was read

- **`codec.rs`**, the boundary chart. The class of a used unit (its index, one more past the void), the alphabet, the round trip
  `decode(encode x) = x`, and the extension at a crossing that keeps every class where it stood: read from `Codec::with`,
  `Codec::extended`, `Codec::encode` and `Codec::decode`. It has no atlas row of its own; `hnn.founded-units` owns the units it reads.
  The sentence that the table of classes stands until the symbol's word replaces it is kept, without its date, because
  [THE_ENGINE](../../docs/THE_ENGINE.md)'s table of guards cites it there.
- **`region.rs`**, a region's support and its ports. A site's three conditions (known, carried as a face, open), the definite sites, a
  state's weight `m/K` in the joint code, a port's three readings (through its coupling, at its boundary, on its letters off the void),
  the echo a carried site's read leaves out, and the known stream: read from `Region`, `Region::weight`, `port_reading`,
  `boundary_reading`, `letters_reading`, `Echo` and `Constitution::admit_region`. The atlas rows are the two whose live owners stand in
  this module alone (`tower.field-joint-code`, `tower.field-opening-boundary`) and seven that name its items beside owners in other
  modules. The echo's Lean owner is `HNN/SynchronousTwoCycle`.
- **`passage.rs`**, the passage's cut and a pass's place. A stretch's two draws, the cut at a piece's end, its one keyed state (a mask, the
  writer's, the frontier's), its own state at a crossing of its octaves, and the cut's order over the slices: read from `lengths_of`,
  `cut_of`, `frontier_cut_of`, `state_of`, `own_state_of`, `frontier_state_of` and `Cut::next`. Five atlas rows have their live owners here.
- **`units.rs`**, units founded by their code length. Its block of equations stood in the present tense already and is kept line for
  line. The proposal's order, the enclosure and the lattice bound are stated after it without their dates. Its Lean owner is
  `Compression/Landmark/Context/Merge` (`merge_cost_mass_iff`, `segmentation_code_le`), and its atlas row is `hnn.founded-units`. Its
  derivation is [the record of October 23](2026-10-23_UNITS_FOUNDED_BY_CODE_LENGTH_CARRY_THE_TOWER_ABOVE_THE_BYTE_AND_THE_PASSAGE_CREDIT_DOES_NOT_PAY.md).

Five comments beside them named an owner that left the tree, and name the tree now:

| Where | It named | It names |
|---|---|---|
| `crates/engine/src/field/moment.rs`, first lines | `crates/holonics-cuda/kernels/field_moment.cuh` | `crates/engine-cuda/kernels/field_moment.cuh` |
| `crates/engine/src/region.rs`, `OwnedRegion::window` and `OwnedRegion::letters` | `holonics::hnn::tower::field::Port::window`, `…::Port::letters` | `Port::window`, `Port::letters` |
| `crates/engine/src/passage.rs`, `PieceBytes` | a link to `SliceFile`, which this crate does not hold | `SliceFile` in `athena::store` |
| `crates/engine/Cargo.toml` | `crates/holonics` as the library that imports the engine and forwards a feature | the card crate and the commands, which depend on it |
| `crates/engine-cuda/Cargo.toml` | `crates/holonics` and `crates/holonics-cuda`, and the profile example | the engine alone, `hnn/profile.rs` and `athena`'s features |

Left as they stand: the kernels' own headers (`kernels/field.cu`, `kernels/field_moment.cuh`), because a kernel's comment changes its
digest and goes with a parity read (C5 and C7 of the plan). The build script hashes the kernel sources and itself, and neither was
touched.

<a id="card"></a>
## The card's modules

Nine modules of `crates/engine-cuda/src/hnn` opened on one line that told the move that made them. Each now names its object, the host
module whose first lines state its equations, kind and owners, and [THE_ENGINE §3](../../docs/THE_ENGINE.md#3-the-pipeline), which lists
each kernel beside the phase it serves and the card module that launches it. The table was read against the code on this date: the
109 kernels it names, one by one or by a stem, are launched from the modules it gives; the contact's entries are given as the range
`field_contact_l3` to `field_contact_l20`; and the profile's ten (`field_series_check`, `field_yard_*`) are named with the readings,
outside the table. `hnn/card.rs` and `hnn/field.rs` kept their own first lines, which state their objects. The lines as they were:

| Module | Its first line until November 18 |
|---|---|
| `hnn/adjoint.rs` | `//! The card realization's adjoint (C5 of #603: cut from `hnn/field.rs` by object, each item's text as it stood but for its visibility).` |
| `hnn/carry.rs` | `//! The card realization's carry (C5 of #603: cut from `hnn/field.rs` by object, each item's text as it stood but for its visibility).` |
| `hnn/clock.rs` | `//! The card realization's clock (C5 of #603: cut from `hnn/field.rs` by object, each item's text as it stood but for its visibility).` |
| `hnn/contact.rs` | `//! The card realization's contact (C5 of #603: cut from `hnn/field.rs` by object, each item's text as it stood but for its visibility).` |
| `hnn/level.rs` | `//! The card realization's level (C5 of #603: cut from `hnn/field.rs` by object, each item's text as it stood but for its visibility).` |
| `hnn/moment.rs` | `//! The card realization's moment (C5 of #603: cut from `hnn/field.rs` by object, each item's text as it stood but for its visibility).` |
| `hnn/profile.rs` | `//! The card realization's profile (C5 of #603: cut from `hnn/field.rs` by object, each item's text as it stood but for its visibility).` |
| `hnn/resident.rs` | `//! The card realization's resident (C5 of #603: cut from `hnn/field.rs` by object, each item's text as it stood but for its visibility).` |
| `hnn/mod.rs` | `//! The card and the field's resident realization, moved from `holonics_cuda::hnn` by C3 of #603.` |

<a id="codec"></a>
## `codec.rs`, its first lines until November 18

[The file at `13d4ba48`](https://github.com/brandonrdug/holonics/blob/13d4ba48/crates/engine/src/codec.rs).

```text
//! **The boundary chart** (`Codec`): a passage's units read as the classes a region's sites carry, and back. Moved from the store line's
//! harness (`complete_language/field_train.rs`) by C4 of the consolidation (#603), each item's text as it stood but for its visibility.
//!
//! [definition; Brandon, November 12] The table of classes stands until the symbol's word replaces it: a symbol is its key on a few coprime
//! rings, located by the machine, never a class index with free rows (CLAUDE.md, Method, "A symbol is a word"). Its replacement is a law
//! build of the engine's line (THE_CONSOLIDATION §11), not a move.
```

<a id="region"></a>
## `region.rs`, its first lines until November 18

[The file at `13d4ba48`](https://github.com/brandonrdug/holonics/blob/13d4ba48/crates/engine/src/region.rs).

```text
//! **A region the trainer owns** (`OwnedRegion`): its classes, its open places, its domain and its port, and the views the field reads of it.
//! Moved from the store line's harness (`complete_language/field_train.rs`) by C4 of #603, each item's text as it stood but for its visibility.
```

<a id="passage"></a>
## `passage.rs`, its first lines until November 18

[The file at `13d4ba48`](https://github.com/brandonrdug/holonics/blob/13d4ba48/crates/engine/src/passage.rs).

```text
//! **The passage's cut and a pass's place**: the problems of a passage of records, the masks a stretch is read with, the store's slices and
//! pieces, the draws of a stretch's context and run, its one keyed state, and the cut that interleaves the slices by their quotas, the pass's
//! place carried in the learner's state (`StorePass`). Moved from the store line's harness (`complete_language/field_train.rs` and
//! `store_train.rs`) by C4 of #603, each item's text as it stood but for its visibility. A slice reads its bytes through [`PieceBytes`]; the
//! store's file is the harness's source.
```

<a id="units"></a>
## `units.rs`, its first lines until November 18

[The file at `13d4ba48`](https://github.com/brandonrdug/holonics/blob/13d4ba48/crates/engine/src/units.rs). The owner it names, `receiver::population::merge`, was the October library's and left the
tree with C8c; the law's Lean statement stands (`Compression/Landmark/Context/Merge.merge_cost_mass_iff`).

````text
//! **Units founded by their code length: adjacent units merge when the whole code falls** (#405,
//! #404).
//!
//! [definition; agent-inferred, October 23] Why it is built. The moment tower read GSM8K at the
//! codec's byte classes and its releases spell letter by letter: after three passes over all 6,726
//! problems it codes 2.3 bits a byte and its continuations of a question are strings of misspelt
//! fragments. A unit above the byte lets the tower release a founded piece of the passage whole,
//! and lets each of its modes span several times the text a byte-clocked mode spans. The units are
//! the passage's own: they are founded from the passage by the merge law of
//! `receiver::population::merge` (Lean `Compression/Landmark/Context/Merge.merge_cost_mass_iff`):
//! **a merge is accepted exactly when it lowers the complete code**, the description of the units
//! plus the code of the passage read in them. Frequency only proposes; the price accepts.
//!
//! ```text
//! units      V = {bytes} ∪ {z_i = (a_i, b_i)},  D(z_i) = D(a_i) D(b_i)        founded in order
//! receiver   order-one KT over units:  W(z) = ∏_s KT(n_s·),
//!            −log₂ KT(n_s·) = L(2n_s + A) − L(A) − Σ_c (L(2n_sc + 1) − L(1)),  L(k) = log₂ Γ(k/2)
//! table      L(k + 2) = L(k) + log₂ k − 1    (the recurrence of Γ, on the code grain)
//! describe   a founded unit names its ordered pair of the A units standing: 2 log₂ A bits, and one
//!            bit for "another unit" (the founding list is a prefix code)
//! merge      (a, b) → z over the occurrences taken left to right without overlap; accepted iff
//!            Δ = ΔW + growth(A → A + 1) + 2 log₂ A + 1 < −(the table's enclosure)
//! parse      a passage is read by replaying the founded merges in order (decode(parse(x)) = x)
//! ```
//!
//! [definition; agent-inferred] **Why order one.** Under an order-zero receiver every frequent
//! co-occurrence pays, and the units grow toward every repeated word. Under order one a pair pays
//! only by what the unit before it does not already predict, and each new unit raises the
//! alphabet every context pays for (`growth`), so the founding reaches its own equilibrium: it
//! ends when no proposed pair lowers the complete code. The receiver that reads the units (the
//! tower) is richer than order one, so this price is a declared, cheaper receiver's, recorded as
//! such.
//!
//! [definition; agent-inferred] **The parse is one path of the segmentation lattice.** A passage
//! is read in the units by replaying the founded merges; its code under any receiver bounds from
//! above the code of the lattice of all parses (Lean `segmentation_code_le`), so a reading in
//! bits a byte is honest, never better than the lattice. The lattice read is owed (#410).
//!
//! [definition; agent-inferred] **Proposal and acceptance.** Pairs are proposed in the order of
//! their adjacent count; each is priced exactly and accepted or refused. A refused pair is priced
//! again when its count changes. The founding ends when every pair standing has been refused at
//! its count. The code's grain is `2^(−32)` bits; the table's enclosure is one grain a recurrence
//! step it spans, and a merge whose price lies inside its enclosure is refused and counted as
//! undecided.
//!
//! [definition] The computational object is the helical pair interaction, read here as the
//! passage's adjacent pairs and the units they found. Of the winding guide's six general objects
//! this owner touches the **pair** (each merge prices one adjacent pair), **faces and placement**
//! (the order-one faces the price reads) and the **tower thread** (a unit restricts to its two
//! constituents and decodes to its bytes); the helix, the cell holonomy and the tube stay attached
//! through the tower that reads the units. Nothing here is text-specific: the founding reads any
//! passage of byte classes (an acoustic or motor code's classes alike).
````
