# The winding is the phase; the option is a declared receiver

**Date:** 2026-08-08
**Truth status:** `established-bounded`
**Evidence:** `implemented-exact` — `crates/holonic-engine/src/model_surface.rs` (16 controls) and three
drivers: `crates/relational-geometry/examples/certified_eta_winding_figure.rs`,
`crates/holonic-engine/examples/leader_quadrature_figure.rs`,
`crates/holonic-engine/examples/graded_complex_integer_invariants.rs`.
`computational-witness` — 50 certified eta windings over the critical strip; the exact leader area
`799/72` with an out-of-aperture miss of exactly `21/8`; Betti `(1,0,0)` with one `Z/2` torsion class.
**Provenance:** Brandon, 2026-08-08: *"I would like to be able to model advanced mathematics
topologies, geometries, and various other complex figures. The way that they represent providing
parameters to functions is also perfect. I would really like to render our research on lightning and
reflective integration in a useful model, and I'd like to apply this to our research on RH regarding
the Zeta distribution and its phases, as well as Hodge."*
**Band:** 2026-08-08 · BRANDON-AUTHORIZED CONSTRUCTION / SOURCE CHANGED — ONE LIBRARY OWNER AND THREE
DRIVERS, NO EXISTING FILE EDITED / RUN — 50 CERTIFIED WINDINGS, 9 LEADER RUNS, ONE EXHAUSTIVE SURFACE
SEARCH / WINDING ATLAS INDEPENDENTLY AGREES WITH THE FIRST TEN KNOWN ZETA ORDINATES / SMITH NORMAL
FORM INDEPENDENTLY REPRODUCED / ZERO FLOATS / NO p,q BIGRADING CLAIMED OR IMPLIED / NO ROADMAP ROW
CLOSED

---

## Present question

Mathematica's modeling surface was offered as a blueprint. Which of its faculties can this body take,
which must it refuse, and what does it already have that the refused ones were standing in for?

## 1 · The option convention is the part worth taking, and it transfers whole

Wolfram's convention is that a call names the object and the domain, and every remaining degree of
freedom is a named, defaulted, inspectable option. Its virtue is not syntax; it is that the
assumptions are **declared where a reader can see them**, rather than buried in the call's behaviour.

In this body's vocabulary an option is a **receiver coordinate**: it says how a receiver reads, never
what the object is. `ModelOptions` carries `value_reading`, `phase_reading`, `scaling`,
`mesh_functions`, `region`, and `stations`, and `ModelOptions::record()` deposits the whole option
set into the emitted artifact — so a figure carries the assumptions it was made under, which is the
part of Wolfram's convention most often lost the moment a plot is exported.

The falsifier `option_change_never_moves_the_object` is the law: changing the scaling changes what is
read, and the winding does not move. A control asserting the two option sets actually differ keeps
it from passing vacuously.

## 2 · Two faculties cannot cross, and the reason is arithmetic

`ComplexPlot3D[f, {z, …}]` plots `Abs[f]` as height and colours by `Arg[f]`. Neither is computable
here, and neither is approximated:

- **`Arg` is transcendental, and `atan2` appears nowhere in either repository** — verified by search
  across both trees. A rational point has no rational argument.
- **`Abs` is transcendental too**: `sqrt` of a rational is generally irrational.
- **`ScalingFunctions -> "Log"`** likewise.

Each is replaced by the exact object it was standing in for:

| Wolfram | Exact replacement | Why it is not a compromise |
|---|---|---|
| `Arg[f]` colour wheel | **winding number** — `read_turn`, and `eta_boundary_winding` for the certified case | a winding over a closed boundary *counts the zeros inside*; a phase colour only suggests where one might be |
| `Abs[f]` height | `SquaredModulus`, `|z|² = Re²+Im²` | stays rational; `|1+i|² = 2` exactly, while `|1+i|` is irrational |
| `"Log"` scaling | `IntegerDecades` — the exact `k` with `10^k ≤ |v| < 10^(k+1)` | the honest part of a log scale is the part that is an integer; a control checks the bracket |
| interpolated `MeshFunctions` | certified **sign change** of `reading − level`, bracketed between stations | a mesh line becomes a statement with a witness rather than a curve through samples |

**Phase is not lost; it is discretised to what a rational actually determines.** `quadrant_of`
returns an exact integer 0..3, and `read_turn` sums quarter-turns by quadrant transition, using the
exact sign of the cross product for the diagonal case — the same primitive `eta_boundary_winding`
already used. Where a step's direction is genuinely undetermined it is **returned as ambiguous**,
never guessed; a step landing on the origin is returned as a hole, because phase does not exist
there.

## 3 · The zeta face: the winding IS the phase, and it is a proof

`eta_boundary_winding` was scanned over 50 unit bands of the critical strip, `σ ∈ [2/5, 3/5]`,
`τ ∈ [1, 51]`, at boundary depth 14. Every call returned `certified`; **zero refusals**.

- **10 bands returned winding 1**: `[14,15] [21,22] [25,26] [30,31] [32,33] [37,38] [40,41] [43,44]
  [48,49] [49,50]`.
- **40 bands returned winding 0** — certified empty, which is the statement a sampler cannot make.

**Independent check.** The ten charged bands are exactly the unit bands containing the first ten
known ordinates of the nontrivial zeros (14.134…, 21.022…, 25.010…, 30.424…, 32.935…, 37.586…,
40.918…, 43.327…, 48.005…, 49.773…). The machinery never saw those values. Agreement is total.

The boundary image polygon of band `[14,15]` — 48 exact rational vertices — encircles the origin
once, and the counting ray is crossed exactly once. **That encirclement is the phase**, and no angle
was computed to obtain it.

## 4 · The lightning face: reflective integration, and a refusal that is exact

`integrate_by_leaders` was driven on three material boundaries under three declared laws.

On the unaligned-piecewise material (span `139/30`, grain `1/4`), both in-aperture laws return the
exact area `799/72`, agreeing with the germwise oracle to `0`:

- **grain-only**: 20 extensions, all FOUND.
- **germ-bounded**: 6 extensions — 3 FOUND, 3 RIDE — reaching the identical rational.

Two refounding obstructions were **retained**, with exact winding residuals `−1/96` and `−1/8`. This
is the reflective-integration law of
`research/records/2026-07-30_THE_REFLECTION_RETURNS_TO_THE_BODY_THE_LIGHT_FRONT_CANNOT_CLONE_THE_WORLD.md`
made computational: *"A caused difference reaches a receiver, changes that receiver's local
morphology, and leaves as a further caused difference."* Each extension rebases the jet it reads, so
the leader is not a probe through an unchanged medium.

**The strongest result is the failure.** Driven past its declared aperture, the unclamped-ancestry
law returns `305/36` instead of `799/72` — short by **exactly `21/8`**. The organ does not return a
slightly wrong area; it returns an exactly quantified miss, and the module's own aperture falsifier
(`49/2` vs `23`, disagreement `3/2`) reproduces.

## 5 · The invariant face, and the Hodge boundary stated plainly

**There is no `p,q` bigrading and no Hodge decomposition in this repository.** `CONSTRUCTION_STATE.md`
already rules it: *"`Hodge` in the live body names the cellular-sheaf Laplacian in
`sheaf_diffusion.rs`, a discrete differential operator — **not** the supported-realization mechanism
… Do not read one for the other."* Independently confirmed: no `F^p` filtration, no Hodge star, no
Dolbeault operator, no complex structure in any live Rust file in either repository.

So the invariant figure renders what actually exists — a **singly graded** complex over `Z` — and
says so in its own title. No Hodge diamond was drawn, and none may be.

The fixture was *derived, not transcribed*: all `C(20,10) = 184,756` ten-triangle subsets of the
twenty triangles on six vertices were enumerated, and exactly 12 are closed surfaces. The first gives
f-vector `(6,15,10)`, `χ = 1`, Betti `(1,0,0)`, torsion `[2]`, with **0 of 1024 hand assignments
cohering** — non-orientable by the module's own refusal. That is the real projective plane in its
minimal triangulation, and the Smith ladder `1|1|1|1|1|1|1|1|1|2` puts the whole `Z/2` in the last
rung.

**Independently reproduced.** The boundary matrix was re-reduced from the emitted TSV by an
unrelated Smith-normal-form implementation: diagonal `[1×9, 2]`, rank 10, torsion `Z/2`. Identical.

## Owners

- `crates/holonic-engine/src/model_surface.rs` :: `ModelOptions`
- `crates/holonic-engine/src/model_surface.rs` :: `read_turn`
- `crates/holonic-engine/src/model_surface.rs` :: `quadrant_of`
- `crates/holonic-engine/src/model_surface.rs` :: `integer_decade`
- `crates/holonic-engine/src/model_surface.rs` :: `certified_crossings`
- `crates/relational-geometry/examples/certified_eta_winding_figure.rs` :: `main`
- `crates/holonic-engine/examples/leader_quadrature_figure.rs` :: `main`
- `crates/holonic-engine/examples/graded_complex_integer_invariants.rs` :: `main`
- `blueprint/THE_PRESENTATION_ORGAN.md` :: part two, the modeling surface

## What this does not establish

- **Nothing about RH.** Ten certified windings over a bounded window prove ten zeros lie in ten
  rational boxes. They do not show any zero lies on `σ = 1/2`, do not bound any ordinate beyond its
  unit band, and say nothing whatever about the infinitely many zeros outside `τ < 51`. The window
  `σ ∈ [2/5, 3/5]` was declared, not derived, and a winding of 1 counts with multiplicity.
- **The winding counts zeros of `η`, not of `ζ`.** They coincide on the scanned window, but the
  figure does not itself prove the separation.
- **No analytic continuation and no functional equation** are implemented; boxes with `σ ≤ 0`, and
  any box straddling `s = 1`, are refused by type.
- **No explicit formula and no Weil positive form exist anywhere** in either repository. That remains
  the largest named gap on the RH line and this work does not touch it.
- **No `p,q` bigrading, no Hodge decomposition, no cycle class.** The invariant face is singly
  graded. Any reading of it as Hodge-theoretic is a misreading the figure explicitly forbids.
- **The lightning face is one-dimensional.** `leader_quadrature` states its own limit: no
  transcendental germ, no branch point, no crossing, no arc out of the plane. Brandon's *"the
  lightning arcs cannot be constrained to the plane, the pathing must be complex and higher
  dimensional"* is quoted in the module and **not** realized by it. Sphere-packing appears nowhere
  and is answered by refusal rather than construction.
- **The exact area is not yet more than exact piecewise-polynomial antidifferentiation** on these
  fixtures; the self-similarity termination law was not run.
- **`ExactReading` is an enumeration, not an expression language.** Wolfram accepts arbitrary
  expressions in `MeshFunctions`; this accepts five exactly-computable readings and refuses the rest,
  which is a real narrowing of the surface.
- **No measured lightning data was used.** 273 MB of GLM/ABI/IGRA material exists in the laboratory
  repository; these figures are computed from declared fixtures only.
