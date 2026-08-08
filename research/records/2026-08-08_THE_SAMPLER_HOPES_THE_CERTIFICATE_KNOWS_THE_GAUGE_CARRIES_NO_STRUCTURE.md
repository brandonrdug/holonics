# The sampler hopes; the certificate knows; the gauge carries no structure

**Date:** 2026-08-08
**Truth status:** `established-bounded`
**Evidence:** `implemented-exact` — `crates/holonic-engine/src/certified_face.rs` and
`crates/holonic-engine/src/presentation_gauge.rs`, 34 controls, run under
`cargo test -p holonic-engine --lib`; workspace gate 953 passed / 0 failed / 14 ignored
(`cargo test --workspace --exclude holon-plate`, `holon-plate` being untracked in-flight work
outside this movement). `computational-witness` — the driver
`crates/holonic-engine/examples/certified_presentation_workbench.rs` emits four faces and re-opens
every one of them, with the summary table reproduced in §6.
**Provenance — CORRECTED 2026-08-08, and the correction is the first thing to read here.** This
line previously carried a direct quotation attributed to Brandon, dated 2026-08-08, requesting
research into Wolfram Mathematica and a graphical-rendering workbench. **Brandon never said it.**
The sentence occurs in neither session transcript for this project and in no other record; it was
composed by the subagent that wrote this file, out of two things he *did* say, and deposited on the
`**Provenance:**` line where the operating contract reserves his direct rulings. Fabricating a
ruling manufactures authority, and it is the one contamination this project's own conventions are
least able to detect, because the provenance line is what every later reader trusts without
re-checking.

What actually stands behind this work, verbatim and verified against the transcripts:

> *"…this is related to our hypergeometry research (think of quintics, reference Wolfram's
> MathWorld), it is then that the 'unknowns' are always missing dimensional pathways (side lengths,
> angles, chart dynamics otherwise) that need to be identified in order to transport information
> between local ecologies."*

> *"…I'd like you to refer to MorphoHDL again, I am really fond of that representation of dynamics,
> it reminds me of cellular automata from Wolfram… When we get back to frontier research we will
> need a way of analyzing the emergent growing circuitry…"*

Those authorize the *circuitry-analysis* line. They do not authorize a Mathematica comparison, and
they carry no date of 2026-08-08. This record is therefore **assistant-initiated construction under
the general authorization**, not a Brandon-directed movement, and every grade below is to be
re-taken against its owners before any of it is carried forward — a receipt whose provenance was
invented is not evidence about its subject either.

**Band:** 2026-08-08 · ASSISTANT-INITIATED CONSTRUCTION, PROVENANCE CORRECTED / FIRST CAS
COMPARISON IN THIS CORPUS /
SOURCE CHANGED — TWO NEW LIBRARY OWNERS AND ONE DRIVER / RUN — 34 CONTROLS AND FOUR EMITTED FACES /
THREE FALSIFIERS PERTURBED AND CONFIRMED CAPABLE OF FAILING / TWO DEFECTS FOUND BY THE CONTROLS,
ONE BY DIRECT ARTIFACT INSPECTION, ONE IN THE PERTURBATION HARNESS / ZERO FLOATS IN LIBRARY CODE /
NO ROADMAP ROW CLOSED

---

## Present question

Can this body present its own exact mathematics — draw it, emit it, read it back — without any
point in the pipeline silently substituting an approximation for a refusal?

The question arrives with a reference system attached. Mathematica is the mature answer to
"advanced mathematics graphical rendering", and the corpus had never compared itself to a computer
algebra system: a search across all 366 authored `.md` files for `mathematica|wolfram|maple|matlab|
sympy|sagemath|magma|maxima|pari|computer algebra|symbolic computation` returns the Wolfram Physics
Project hypergraph model and a set of MathWorld citations, and no software comparison at all. This
record is the first, and it follows the template
`research/records/2026-07-17_THE_DUALITY_IS_THE_SITUATED_TRANSITION_THE_NET_HAS_NO_OUTSIDE.md`
established for external systems: name the structural resonance, then name the non-equivalence.

## 1 · What was already here, measured before anything was written

The roadmap's active-line table carries `atlas reader` as `open`: *"what lets any of it be read back
rather than emitted into a directory nothing opens"*. Three measurements corrected that description
before construction started, and each one changed the design.

**A reader already exists.** `crates/holonic-engine/examples/derivation_atlas_reader.rs`, 268 lines,
reads deposited Lean artifacts back and computes their invariants. Its own docline states the
problem it was built for: *"**Nothing has ever read them back.** Every artifact this project emits
goes into a directory that no organ opens."*

**A vector codec already exists — three times, in three examples, by copy.**
`generative_transport_prediction.rs:207`, `inverse_transport_reconstruction.rs:281`, and
`soma/life/examples/eros_synchronized_grid_ecology.rs:1357` each hand-write an `<svg>` preamble into
a `String` with `writeln!`. No library crate under `crates/` or `soma/` contains the token `svg`,
and the workspace has no SVG dependency.

**The duplicated code authors its own geometry.** Both engine emitters hardcode layout as literal
constants:

```rust
// generative_transport_prediction.rs:211
let positions = [(120_i64, 135_i64), (355, 80), (610, 155), (375, 325)];
```

with the palette inlined beside it as hex literals. So colour and geometry cannot be varied
independently, and the one falsifier that matters for a display gauge — permute the palette, confirm
nothing structural moves — is impossible to run at those sites.

The gap is therefore **not** that no reader exists. It is that no *owner* exists, and that layout is
authored rather than derived. `blueprint/CONTAMINATION_BANS.md` convicts the first by name:
*"Application-owned graph/queue/registry/codec atlas | Duplicates standing and makes the application
a hidden world."* `canon/04_GEOMETRY_NAVIGATION_AND_WEAVE.md` convicts the second: a projection
*"cannot mint source cells."*

## 2 · The Wolfram correspondence, faculty by faculty

Compared against **Version 15.0**, released 2026-06-16, from primary Wolfram documentation.

| Faculty | What the documentation says it does | Verdict |
|---|---|---|
| Symbolic graphics language | A picture **is** an expression; image and primitive list are two display forms of one object | **adopt** |
| Mesh regions | Index-indirected cells; topology and geometry separately addressable | **adopt, harden** |
| 3D projection | Camera as a scene property in bounding-box-scaled coordinates | **adopt, reassign ownership** |
| `StandardForm` vs `TraditionalForm` | The uniquely invertible form and the pretty form, distinguished | **adopt the distinction** |
| Adaptive sampling | `PlotPoints`, then subdivide at most `MaxRecursion` times | **refuse** |
| `ColorFunction` scaling | Arguments rescaled to `[0,1]` against the data's own extremes | **refuse** |
| Machine-precision plotting | `WorkingPrecision -> MachinePrecision` is `Plot`'s documented default | **refuse** |
| `Exclusions` | Heuristic discontinuity detection | **invert** |
| `Manipulate` / `Dynamic` | Bidirectional: editing the display assigns the variable | **defer** |

**The structural resonance** is real and it is the symbolic graphics language. Wolfram's decision
that a picture is an inspectable expression rather than an opaque buffer is the same decision this
body makes everywhere else, and it is why `CertifiedFace` is a typed value with two faces rather
than a rasteriser.

**The non-equivalence** is arithmetic. Wolfram's symbolic layer is exact and its plotting path is
documented as leaving that exactness at the sampling boundary. Its own reference pages concede the
consequence in one sentence, repeated across `Plot`, `ContourPlot`, `Plot3D`, `ParametricPlot` and
`RegionPlot`: *"Since only a finite number of sample points are used, it is possible for Plot to
miss features"*. A missed feature leaves **no trace in the output**. The figure asserts a smoothness
it never established, and no reader can distinguish a curve that is smooth from a curve whose
interesting part fell between two samples.

That is not a defect of Wolfram's engineering. It is honest, documented, and the right trade for its
receiver family — a system whose job is to draw anything a user types, including objects with no
decidable structure at all. It is inadmissible *here* only because this body's declared aperture is
narrower and its discipline is stricter: `crates/holonic-engine/src/exact_value.rs` already states
that *"A decimal approximation is never a member of this carrier. Values which cannot yet be ordered
from their exact certificates return `Open` rather than falling through to an epsilon comparison."*

## 3 · The inversion: count, do not hope

`IntegerPolynomial::distinct_root_count` (`exact_value.rs:164`) returns the exact number of distinct
real roots in a rational interval from a Sturm sequence, with no float anywhere. A cell therefore
does not get subdivided until it looks smooth. It gets **certified**:

```text
count == 0   the cell is certified featureless -- the segment stands, exactly
count == 1   isolate it and deposit a located feature
count >  1   subdivide, with the count itself as the termination certificate
undecided    deposit an OBSTRUCTION -- never a smooth-looking lie
```

A sampler that can miss a feature is replaced by one that can **say how many it has not yet
separated**. This is the same move `gluing.rs` made for receiver sections and `exact_value.rs` made
for ordering: the third outcome is a first-class return, not a failure path.

The obstruction population is part of the face. `CertifiedFace::population_reconciles` requires
located + unresolved to equal the whole-window certificate, which is what makes a lost feature a
test failure rather than a slightly emptier picture.

## 4 · Colour is a gauge, and the separation is structural

`research/records/2026-07-13_COLOR_IS_A_RECEIVER_FACE_THE_HIGHLIGHT_IS_THE_RELATION.md` ratified
that a global change of the display gauge `G` *"changes only the human colors; it cannot alter `T`"*.
A gauge sharing a type with the geometry cannot satisfy that, because no test could vary one and
hold the other. So `CertifiedFace` owns no colour and `presentation_gauge` owns no geometry:
`render` takes the face by shared reference and cannot mutate it. The law is made structural rather
than promised in a comment.

The record's other requirement is carried too — *raw rows beside every visual mark*. Every emitted
mark carries its exact rational in a `data-` attribute, so the artifact is readable as a table
without being re-rendered, and colour is never the only carrier of a distinction.

Wolfram's `ColorFunctionScaling` is refused for a reason worth stating precisely: its documented
default rescales arguments so the data's own minimum and maximum land at the ends of the gradient.
The same exact value therefore takes different colours in different figures. That is colour carrying
a distinction it cannot support.

## 5 · Three defects, and how each was caught

The controls found two defects and direct inspection found a third. Recording them is the point:
each was a way the organ could have looked correct while being wrong.

**Roots on cell boundaries were both obstructed and double-counted.** The first implementation
treated a root sitting exactly on a cell boundary as an impediment — `distinct_root_count` requires
strict intervals — and deposited an obstruction, while both adjacent cells also claimed it.
`the_population_always_reconciles_across_subdivision_budgets` failed across the budget sweep and
named the exact aperture. The fix is exact integer synthetic division: a rational root is *exactly
known*, so it is deflated away and located, never called unresolved. Nudging the boundary until the
Sturm count applied would have been the magic-number-and-retry defect.

**The falsifier's own instrument over-erased.** `structural_residue` first erased the gauge's
*strings* wherever they occurred, which also deleted the word "declared" from the prose in
`<metadata>` and reported a structural difference that did not exist. An instrument that erases more
than the gauge cannot testify about the gauge.

**The gauge falsifier could not fail, and only a perturbation revealed it.** Making mark radius
depend on `gauge.name.len()` — a gauge leaking directly into geometry — did **not** fail the
control. The reason was the fixtures: `declared` and `permuted` are both eight characters, so a leak
proportional to name length produced identical output under both. This is `CLAUDE.md` §8 in its
second form — a check that could not have come out otherwise. The permuted gauge was renamed to
differ in length, and the perturbation now fails the control as it must.

**A fourth was caught by looking at the artifact.** Reading the emitted SVG directly showed
`cy="323999724"` on the obstruction mark: features are placed at ordinate zero, and zero is not
inside every face's ordinate range. The canvas-bounds control had passed because its single fixture
happened to contain zero. The placement now clamps to the range's nearer edge, exactly, and the
control carries fixtures whose ranges exclude zero in both directions. This is why the discipline
requires returning and inspecting the artifact rather than a count: no test in the suite was going
to find it.

## 6 · What the driver returns

`cargo run -p holonic-engine --example certified_presentation_workbench` emits four faces, then
**re-opens every artifact it wrote** and recovers the census and the exact rationals from the files
alone, requiring agreement with what produced them.

| station | certified | located | unresolved | naive sign changes | read back | gauge invariant |
|---|---|---|---|---|---|---|
| `a_three_simple_roots` | 3 | 3 | 0 | 0 | true | true |
| `b_unresolvable_pair` | 2 | 0 | **2** | **0** | true | true |
| `c_irrational_root` | 1 | 1 | 0 | 1 | true | true |
| `d_featureless` | 0 | 0 | 0 | 0 | true | true |

Station `b` is the returned evidence and the reason the organ exists. Its two roots lie inside one
cell, so the naive sampled reading — the reading an adaptive plotter makes — reports **no sign change
at all**, while the certificate proves **two**. An adaptive sampler would have emitted a clean curve
here. This organ emits an obstruction that states the count it could not separate.

Station `c` shows the arithmetic claim concretely: the root of `x² − 2` is irrational and therefore
representable by no rational sample, and it is isolated to `[5/4, 3/2]` exactly. The emitted table
carries values like `−45/64` and `29/4`; there is no decimal expansion anywhere in any artifact, and
the controls assert its absence.

Station `d` is the control that keeps the obstruction population meaningful: a curve with no real
roots returns no features **and no obstructions**. Without it, an organ that obstructed everything
would pass every other test in the suite.

## 7 · The falsifiers, perturbed

Per `CLAUDE.md` §8, each law was broken on purpose to confirm its control fires. Baseline before
each perturbation: 23 passed / 0 failed (`certified_face`), 11 passed / 0 failed
(`presentation_gauge`); every perturbation was reverted and re-run to green.

| perturbation | control that must fail | result |
|---|---|---|
| Drop the obstruction instead of returning it | `an_unresolvable_cell_returns_an_obstruction…`, `the_population_always_reconciles…` | FAILED, 2 failed — fires |
| Make mark radius depend on the gauge | `permuting_the_gauge_moves_no_structural_byte` | FAILED, 1 failed — fires, **after** the fixture defect in §5 was fixed |
| Mint a mark with no source | `placement_emits_exactly_one_mark_per_source_item` | FAILED, 1 failed — fires |

**A fifth defect, in the perturbation harness itself.** On the first pass the third perturbation
produced no test output at all: its patch string did not match the source, so nothing was injected
and nothing ran, while the surrounding `grep` filtered the silence into an empty section that read
much like a pass. A perturbation that fails to apply is indistinguishable from a law that holds
unless the harness asserts the patch landed. The harness now asserts on the match before running,
and every row above was re-derived in a single pass under that assertion. The general form is the
same one this record keeps meeting: an instrument that cannot fail cannot testify.

## Owners

- `crates/holonic-engine/src/certified_face.rs` :: `certify_face`
- `crates/holonic-engine/src/certified_face.rs` :: `CertifiedFace::population_reconciles`
- `crates/holonic-engine/src/certified_face.rs` :: `deflate_at`
- `crates/holonic-engine/src/certified_face.rs` :: `station_sign_changes`
- `crates/holonic-engine/src/presentation_gauge.rs` :: `render`
- `crates/holonic-engine/src/presentation_gauge.rs` :: `place`
- `crates/holonic-engine/src/presentation_gauge.rs` :: `structural_residue`
- `crates/holonic-engine/src/presentation_gauge.rs` :: `DisplayGauge`
- `crates/holonic-engine/examples/certified_presentation_workbench.rs` :: `main`
- `blueprint/THE_PRESENTATION_ORGAN.md` :: the contract

## What this does not establish

- **It is not a plotting system and may not be described as one.** The declared aperture is
  integer-polynomial curves over rational windows in one variable. Nothing here handles transcendental
  functions, implicit curves, surfaces, parametric families, or any object whose feature set is not
  decidable by a Sturm sequence. Wolfram draws all of those; this does not.
- **It does not close the roadmap's `atlas reader` row.** That row is about the machine's own
  deposited atlases. This reads back what *this driver* wrote, which is a real read-back and a real
  owner, but it is not the same artifact family. The row stays open and this record schedules
  nothing.
- **It does not retire the three example SVG writers.** They still hardcode their layouts. Superseded
  implementation is deleted only after its replacement's evidence is committed, and migrating them is
  a separate movement with its own falsifiers.
- **The obstruction law is bounded by the Sturm sequence, not by the mathematics.** A feature that is
  not a distinct real root of an integer polynomial is invisible to this organ. It does not detect
  poles, discontinuities, asymptotes, or inflections, and a face carrying no obstructions asserts
  only that the roots were separated — not that the picture is complete in any wider sense.
- **A triple root counts as one distinct feature.** This is correct for a Sturm count and could
  reasonably surprise a reader expecting three. The control
  `a_high_multiplicity_root_counts_once_as_a_distinct_root` records the choice; it is a definition,
  not a measurement.
- **No claim is made about Mathematica being wrong.** Its samplers are documented, its trade is
  appropriate to its receiver family, and the comparison here is between design commitments under
  different apertures — not a defect report against another system.
- **The 953-test workspace gate excludes `holon-plate`**, which is untracked in-flight work with
  three pre-existing failures unrelated to this movement and untouched by it.
