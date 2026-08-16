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

---

## Part two — the modeling surface

**Provenance:** Brandon, 2026-08-08: *"I would like to be able to model advanced mathematics
topologies, geometries, and various other complex figures. The way that they represent providing
parameters to functions is also perfect."*

Part one built one certified face. This part answers the second half of the request: the **option
convention**, and the objects this body actually has to model.

### The option convention is adopted; two faculties inside it are refused

Mathematica's convention is that a call names the object and the domain, and every other degree of
freedom is a named, defaulted, inspectable option — `PlotPoints`, `MeshFunctions`,
`ScalingFunctions`, `ColorFunction`, `RegionFunction`. Its virtue is that the assumptions are
declared where a reader can see them. That is adopted wholesale, in structure and in spirit:
`ModelOptions` carries each as a typed field, and `ModelOptions::record()` deposits the option set
**into the emitted artifact**, so a figure carries the assumptions it was made under.

In holonic vocabulary an option is a **receiver coordinate**: it says how a receiver reads, never
what the object is. `option_change_never_moves_the_object` enforces exactly that — changing the
scaling changes what is read, and the winding does not move.

Two of Wolfram's faculties cannot cross into this body, and the reasons are arithmetic rather than
doctrinal:

| Wolfram | Why it cannot be computed here | The exact object that replaces it |
|---|---|---|
| `Arg[f]` — the colour wheel of `ComplexPlot3D` | transcendental; **`atan2` appears nowhere in either repository**, verified by search | the **winding number**: `eta_boundary_winding` already returns a certified integer from sign-of-cross-product ray crossings, and `read_turn` gives the same for any walk |
| `Abs[f]` — the height of `ComplexPlot3D` | `sqrt` is transcendental and a rational has no rational modulus | `SquaredModulus` (`|z|² = Re²+Im²`, exactly rational) |
| `ScalingFunctions -> "Log"` | transcendental | `IntegerDecades`: the exact integer `k` with `10^k ≤ |v| < 10^(k+1)`, by integer comparison |
| `MeshFunctions` by interpolation | a contour fitted through samples is not a witnessed statement | a **certified sign change** of `reading − level`, bracketed between stations |

**Re-measured 2026-08-15 and one row is FALSE.** `grep -rn "atan2" --include='*.rs' crates soma` returns
four hits: two doc comments and **two live calls on `f64`** at
`soma/life/examples/eros_relampago_atmospheric_current.rs:1720`. Those are a boundary codec on
foreign atmospheric data rather than library code, so `model_surface.rs`'s narrower phrasing —
*"nowhere in this body"* — is correct and this row's *"either repository"* is not.

**This is a strengthening, not a compromise.** A phase colour wheel shows a reader where a zero
probably is. A winding number over a closed boundary *proves how many zeros are inside it* — and
Wolfram's own documentation concedes its samplers may miss features. The image polygon that
`WindingReceipt` already carries is that proof made drawable: the curve encircles the origin exactly
`winding` times, and no angle is computed anywhere.

### The three objects this surface must carry

Measured in both repositories, 2026-08-08. Each is already exact; none needed new mathematics.

1. **The zeta/eta face.** `eta_boundary_winding`, `eta_evaluate`, `eta_partial_current` over
   `ComplexReceiverBox { sigma, tau }` — the complex plane as a lattice of rational rectangles, never
   as points. Certified winding per box is an exact zero count.
2. **The lightning face.** `leader_quadrature::integrate_by_leaders` — integration by lightning
   leaders over an exact rational interval, where `LocalJet::swept` is itself a winding and each
   extension rebases the material boundary it reads. This is the reflective-integration law in
   `research/records/2026-07-30_THE_REFLECTION_RETURNS_TO_THE_BODY_THE_LIGHT_FRONT_CANNOT_CLONE_THE_WORLD.md`
   made computational: *"A caused difference reaches a receiver, changes that receiver's local
   morphology, and leaves as a further caused difference."*
3. **The invariant face.** `rebase_invariants` and `smith_normal_form` over a singly-graded complex:
   per-grade Betti numbers and torsion, exact over `Z`.

### The Hodge boundary, stated before anything is drawn

`CONSTRUCTION_STATE.md` already rules on this and the ruling binds every figure produced here:
*"`Hodge` in the live body names the cellular-sheaf Laplacian in `sheaf_diffusion.rs`, a discrete
differential operator — **not** the supported-realization mechanism … Do not read one for the
other."* Verified independently: no `p,q` bigrading, no `F^p` filtration, no Hodge star, no Dolbeault
operator exists in any live Rust file in either repository.

**Therefore no figure from this surface may be captioned as a Hodge decomposition, and no Hodge
diamond may be drawn.** The invariant face renders a singly-graded complex and must say so in its
own title. A figure that implied a bigrading would be manufacturing a mathematical structure the
body does not have, which is the same defect as minting geometry — worse, because it would be
minting a theorem.

---

## What this contract does not license

- It does not schedule work. `blueprint/THE_ROADMAP.md` schedules work.
- It does not claim a general plotting system, a Mathematica replacement, or a CAS. The declared
  aperture is integer-polynomial curves over rational windows, and an organ used past its declared
  aperture is a defect even when it appears to return (`CLAUDE.md` §8).
- It does not make the display an input. Nothing rendered re-enters the construction.
- It does not retire the three example SVG writers by deleting them silently; superseded
  implementation is deleted only after its replacement's evidence is committed (`AGENTS.md`).
