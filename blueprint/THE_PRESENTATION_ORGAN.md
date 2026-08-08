# The presentation organ

**Genre:** blueprint contract (`canon/THE_DOCUMENT_LAW.md` §1.3). It states a contract the roadmap
composes. **It schedules nothing.** `blueprint/THE_ROADMAP.md` remains the single active roadmap and
the only file that says what is open.

**Truth status:** `project-postulate`. **Provenance:** Brandon, 2026-08-08 — *"I want to effectively
establish our workbench for all of the same advanced mathematics graphical rendering features, but
adapted rigorously to holonics."*

---

## The gap this closes, measured before it was written

The roadmap's active-line table carries one row still marked `open`:

| piece | what it is in the line | state |
|---|---|---|
| **atlas reader** | what lets any of it be read back rather than emitted into a directory nothing opens | open |

Measured in this tree 2026-08-08, the gap is **not** what that sentence implies, and the correction
is the reason this contract exists:

- **A reader already exists.** `crates/holonic-engine/examples/derivation_atlas_reader.rs`, 268
  lines, reads deposited Lean artifacts back and computes their invariants. Its own docline states
  the problem it was built for: *"**Nothing has ever read them back.** Every artifact this project
  emits goes into a directory that no organ opens."*
- **A vector codec already exists — three times, in three examples, by copy.**
  `crates/holonic-engine/examples/generative_transport_prediction.rs:207`,
  `crates/holonic-engine/examples/inverse_transport_reconstruction.rs:281`, and
  `soma/life/examples/eros_synchronized_grid_ecology.rs:1357` each hand-write an `<svg>` preamble
  into a `String` with `writeln!`. There is no SVG dependency in the workspace and **no library
  crate under `crates/` or `soma/` contains the token `svg`.**

So the defect is not *no reader*. It is **no owner**. Three applications own a codec, which
`blueprint/CONTAMINATION_BANS.md` convicts by name:

> | Application-owned graph/queue/registry/codec atlas | Duplicates standing and makes the application a hidden world. | Put missing reusable structure in its responsible owner; applications only compose ports. |

And the duplicated code carries a second, worse defect. Both engine emitters **author their layout
as literal coordinates**:

```rust
// generative_transport_prediction.rs:211
let positions = [(120_i64, 135_i64), (355, 80), (610, 155), (375, 325)];
```

```rust
// inverse_transport_reconstruction.rs:282-287
let positions = (0..EXTENT).map(|ordinal| { … (70 + 95 * parameter, 60 + 11 * parameter * parameter) })
```

A hand-placed constant is not a receiver's chart of anything. It is decoration that cannot be
falsified, and it is exactly what `canon/04_GEOMETRY_NAVIGATION_AND_WEAVE.md` forbids when it says a
projection *"cannot mint source cells."* The palette is fused in beside it as hex literals
(`"#174f52"`, `"#7a355f"`), so colour and geometry cannot be varied independently — which makes the
one falsifier that matters for a display gauge, *permute the palette and confirm nothing structural
moves*, impossible to run.

---

## What Wolfram Mathematica contributes, and where it is refused

Compared against **Version 15.0** (released 2026-06-16) from primary documentation. The corpus has
never compared itself to a computer-algebra system before; this follows the house template set by
`research/records/2026-07-17_THE_DUALITY_IS_THE_SITUATED_TRANSITION_THE_NET_HAS_NO_OUTSIDE.md` —
name the structural resonance, then name the non-equivalence.

| Faculty | What Wolfram does | Verdict |
|---|---|---|
| Symbolic graphics language | A picture **is** an expression; image and primitive list are two display forms of one object | **adopt** |
| Mesh regions | Index-indirected cells; topology and geometry separately addressable | **adopt, harden** |
| 3D projection | Camera as scene property in bounding-box-scaled coordinates | **adopt, reassign ownership** |
| `StandardForm` vs `TraditionalForm` | The invertible form and the pretty form, distinguished | **adopt the distinction** |
| Adaptive sampling | `PlotPoints`, then subdivide at most `MaxRecursion` times | **refuse** |
| `ColorFunction` scaling | Arguments rescaled to `[0,1]` against the data's own extremes | **refuse** |
| Machine-precision plotting path | `WorkingPrecision -> MachinePrecision` is `Plot`'s documented default | **refuse** |
| `Exclusions` | Heuristic discontinuity detection | **invert** |
| `Manipulate`/`Dynamic` | Bidirectional: editing the display assigns the variable | **defer** |

**The central refusal.** Wolfram's symbolic layer is exact, and its plotting path is documented as
leaving that exactness at the sampling boundary. Its own reference pages concede the consequence in
one sentence repeated across every sampler — of `Plot`: *"Since only a finite number of sample
points are used, it is possible for Plot to miss features"*, with the identical disclaimer on
`ContourPlot`, `Plot3D`, `ParametricPlot` and `RegionPlot`. A missed feature leaves **no trace in
the output**. The figure therefore asserts a smoothness it never established, and no reader can
tell the difference between a curve that is smooth and a curve whose interesting part fell between
two samples.

That is not a defect of Wolfram's engineering — it is honest, documented, and the right trade for
its receiver family. It is inadmissible *here*, because this repository's whole discipline is that
an unresolved thing stays open rather than being quietly resolved. `crates/holonic-engine/src/exact_value.rs`
already says so in its opening lines: *"A decimal approximation is never a member of this carrier.
Values which cannot yet be ordered from their exact certificates return `Open` rather than falling
through to an epsilon comparison."*

**The inversion, and it is the organ's whole content.** Mathematica *samples and hopes*. This body
can *count and know*, because `IntegerPolynomial::distinct_root_count` (`exact_value.rs:164`)
returns the exact number of distinct real roots in a rational interval from a Sturm sequence, with
no float anywhere. So a cell does not get subdivided until it looks smooth; it gets **certified**:

```text
Wolfram:   sample the cell, subdivide up to MaxRecursion, emit whatever was found
Holonic:   count the features in the cell exactly.
           count == 0  ->  the cell is certified featureless, and the segment is exact
           count == 1  ->  isolate it, deposit it as a located feature
           count >  1  ->  subdivide, with the count as the termination certificate
           undecided   ->  RETURN THE OBSTRUCTION. Never a smooth-looking lie.
```

A sampler that can miss a feature is replaced by one that can **say how many it has not yet
separated**. That is the same move `gluing.rs` already made for receiver sections, and the same
move `exact_value.rs` already made for ordering.

---

## The contract

Per `AGENTS.md` construction grade, before code: the owners composed, the ports, the event, the
local law, the receiver question, the returned consequence, and the grade.

**Source owners composed.** No new mathematics. Every one of these exists and is measured:

- `relational_geometry::exact::{Rat, RatVec2, format_rat}` — the exact rational carrier, a
  `BigRational` alias, with `format_rat` the **only** textual presentation and no rational-to-decimal
  conversion anywhere in any library crate.
- `holonic_engine::exact_value::{IntegerPolynomial, ExactInterval, AlgebraicRoot, ExactOrdering}` —
  Sturm root counting and certified isolation.
- `relational_geometry::projection` — receiver-owned exact projection.
- `holonic_engine::rebase_invariants::{rebase_invariants, PivotRule}` — the integer invariants the
  reader reports.

**Port types.** One inbound: a receiver-supplied exact question (a polynomial and a rational window).
One outbound: a `PresentationFace` carrying exact coordinates, located features, **and its
obstruction population**. The codec is a separate outbound port that consumes a `PresentationFace`
and returns octets.

**The event.** A receiver asks for a face of an exact object over a declared window. The organ
returns the face, the certificate, and every cell it could not decide.

**Local constitutive law.** Sampling is certified, never adaptive-until-it-looks-right. The rule is
stated above and implemented exactly.

**Receiver question.** *Can this body present its own exact mathematics without any point in the
pipeline silently substituting an approximation for a refusal?*

**Returned consequence.** A figure whose every drawn coordinate is an exact rational, whose feature
population is Sturm-certified, and whose undecided cells are carried in the artifact rather than
smoothed away.

**Grade.** `established-bounded` on return, tagged `implemented-exact`, bounded to the declared
receiver family — integer-polynomial curves over rational windows. Not a general plotting system,
and it may not be described as one.

---

## The three falsifiers, declared before construction

Per `CLAUDE.md` §8, a law that returns zero proves nothing about itself, and a receipt that could
not have come out otherwise carries no evidence. Each falsifier below must be capable of failing.

1. **The obstruction falsifier.** Present a curve with a feature narrower than the initial cell
   width. Mathematica's documented behaviour is to miss it silently. This organ must **return it as
   an obstruction or locate it** — and a run that returns an empty obstruction population on a
   deliberately unresolvable input has failed. Control: a curve with no features in the window must
   return an empty obstruction population, or the law is obstructing everything and means nothing.
2. **The gauge falsifier.** Permute the palette and re-render. Every exact coordinate, every located
   feature, and every invariant must be **byte-identical**. If any structural byte moves, colour has
   become a carrier of a distinction and the receiver-face law is violated.
3. **The non-creation falsifier.** Every coordinate in the emitted face must be traceable to an
   exact source value. No literal layout constant may appear in the owner. Control: the count of
   emitted marks must equal the count of source features — a projection that emits more marks than
   the source has structure has minted geometry.

---

## What this contract does not license

- It does not schedule work. `blueprint/THE_ROADMAP.md` schedules work.
- It does not claim a general plotting system, a Mathematica replacement, or a CAS. The declared
  aperture is integer-polynomial curves over rational windows, and an organ used past its declared
  aperture is a defect even when it appears to return (`CLAUDE.md` §8).
- It does not make the display an input. Nothing rendered re-enters the construction.
- It does not retire the three example SVG writers by deleting them silently; superseded
  implementation is deleted only after its replacement's evidence is committed (`AGENTS.md`).
