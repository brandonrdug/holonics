# The complex torus fibre was received as geometry, and the three monodromies returned distinct graphs

**Date:** 2026-08-24  
**Construction authority:** Brandon's direct request for an engine-native receiver rendering; this
record does not advance or alter `CONSTRUCTION_STATE.md`.  
**Primary source:** [*A compact complex threefold fibred by tori over the projective line, and the
six-sphere*](https://alpo.ge/s6.pdf).  
**Driver:** `crates/holonic-engine/examples/complex_six_sphere_torus_transport.rs`.  
**Returned artifact:** `output/complex-s6-torus-transport/`.

## 1. The deed and its boundary

[definition] The source occurrence is the finite exact pullback atlas

```text
three special-loop branches
  × ordered monodromy stages
  × (Z/4Z)^4,
```

where each `Z/4Z` factor is geometrically realized by the four rational cardinal points of one
unit circle.  The four circle factors are declared as four `ExactComplexAxisPair` instances, so one
sampled fibre is the geometric four-torus `(S^1)^4`, a finite exact receiver sample of the real
four-dimensional topology underlying a complex two-torus.  It is not the engine's real
three-dimensional ring `ExactTorus`.

[definition] The existing source owners are `GradedCausalComplex`, `ExactDimensionalSource`,
`ExactCoordinateGerm`, and `ExactCoordinateCarrier`.  Their input ports are caused stage events,
ten exact rational coordinate axes, four unit-conic relations, source-cell identities, and declared
phase or interaction carriers.  The predecessor identity is one generic phase address
`v in (Z/4Z)^4`.  The local constitutive law is `v |-> M^s v mod 4` on branch stage `s`, with
`M = A1`, `A2`, or `M0`.  The consequence is the complete transported germ and carrier population;
no raster coordinate enters this law.

[proved-derived; formal-checked] `SixSphereMonodromy.lean` proves from the displayed integral
matrices that `A1` has order three, `A2` has order four, `A1 A2 M0 = I`, and
`(M0 - I)^2 = 0` through its inverse-transpose relation with the primal square-zero cusp
monodromy.  The driver copies those displayed matrices and refuses before source construction unless
all four identities hold by exact integer arithmetic.

[established-bounded; implemented-exact] The source returned 3,328 geometric fibre germs and
16,384 declared carriers over thirteen stages: four stages on the order-three branch, five on the
order-four branch, and four on the nonclosed cusp prefix.  Every germ carries local dimension six
in the declared atlas: two base transport coordinates plus eight real phase coordinates minus four
unit-conic relations.  Every finite elliptic return is an explicit source carrier; no corresponding
return is inserted for the unipotent cusp prefix.

## 2. The receiver family

[definition] `DimensionalReceiverAtlas` owns the first receiver passage.  Each receiver supplies two
exact covectors, an optional exact depth covector, aperture, slice constraints, event identity, and
chronology.  `relational_geometry::ProjectionLaw::PerspectiveRay` owns the second passage from that
exact three-coordinate face to a rational perspective face.  The raster membrane then performs only
integer pixel conversion and additive RGB transduction.  It cannot alter source germs, carriers,
matrix action, collision fibres, or receiver lineage.

[definition] Cyan current is the outer transducer's face of source-declared fibre phase carriers;
orange current is its face of monodromy passages; magenta current is its face of an exact finite
ordered return.  Those colors distinguish carrier species already present in the source.  They do
not found an edge, infer contact from proximity, or assign topology.

[established-bounded; implemented-exact] Seven receivers returned and were inspected:

| receiver artifact | exact receiver question | returned face |
|---|---|---|
| `00-base-quotient.png` | What survives when both visible covectors read only ordered stage and special-loop branch? | 13 collapsed buckets retain the complete 256-member geometric fibre over each base-stage occurrence. |
| `01-family-perspective.png` | What does the joint base/fibre transport graph look like when small phase directions remain visible? | All 3,328 germs and all 16,384 carriers remain visible with no exact projection collision. |
| `02-fibre-perspective.png` | What survives when the base coordinates depart and four phase circles enter one mixed perspective? | The complete population lands in 256 exact buckets, exposing the finite geometric `T^4` receiver quotient. |
| `03-fibre-after-exact-receiver-turn.png` | How does the same source face change after an exact Cayley turn in the first phase plane? | The source is unchanged, the receiver lineage advances, and the projected transport complex changes. |
| `04-order-three-monodromy.png` | What is the `A1` transport section alone? | 1,024 germs and 5,120 carriers, including the exact third return. |
| `05-order-four-monodromy.png` | What is the `A2` transport section alone? | 1,280 germs and 6,400 carriers, including the exact fourth return. |
| `06-unipotent-cusp-shear.png` | What is the bounded `M0` prefix without inserting a false closure? | 1,024 germs and 4,864 carriers; the shear remains open. |

[established-bounded; implemented-exact] `receiver-receipts.json` retains every germ disposition,
source cell, local dimension, exact normalized face coordinate, depth, collision population, carrier
disposition, source and received `f`-vectors, and receiver event/chronology for all seven views.
Every receipt reports `projection_cells = 0`: a projection emitted testimony and minted no source
incidence.

## 3. What the rendering teaches

[established-bounded; implemented-exact] The base quotient is intentionally nearly empty.  Its
thirteen visible points and three ordered rows are not a deficient source; they are the exact face
left after the receiver collapses each 256-point fibre.  The reconstruction populations remain in
the receipt.  This is the concrete visual control for the law that equal receiver output is not
source equality.

[established-bounded; implemented-exact] The joint family view exhibits the opposite aperture.
Each base stage carries a projected four-factor lattice, phase carriers stay local to one stage,
monodromy passages join stages, the two finite branches return, and the cusp prefix does not.  These
relations were read from `ExactCoordinateCarrier`; no line was authored from screen proximity.

[established-bounded; implemented-exact] The two fibre views show that perspective belongs to the
receiver.  The Cayley-turned image differs substantially from the unturned image even though the
3,328 source germs, 16,384 source carriers, matrix actions, and source incidence remain byte-equal
inside the one atlas.  The pair therefore visualizes a receiver reframe, not a deformation of the
geometric fibre.

[interpretation] The most useful next geometric widening is not a prettier raster.  It is to replace
the four-cardinal-point circle factors by certified denser exact phase sections, then couple the
pointwise period matrix to the four phase directions and let the existing dimensional receiver
carry the resulting chart family.  That would expose deformation of the lattice shape rather than
only the already checked integral monodromy action.  It must retain the same source/receiver
separation and the full collision fibres.

## 4. Exact open boundary

[open] This bounded occurrence does not construct the paper's holomorphic period functions, prove
that their columns form a discrete cocompact lattice, build `C^2 / Pi(z)Lambda`, construct the
order-three or order-four logarithmic fillings, construct the toric cusp filling and central fibre,
glue collars, compute fundamental group or integral homology, recognize the resulting smooth body
as `S^6`, or transport the complex structure through that diffeomorphism.  Those remain distinct
mathematical returns.

[open] The current fibre graph is a four-point-per-circle exact sample.  It preserves the four
circle factors, rank-four lattice action, finite elliptic orders, cusp nilpotent law, source lineage,
and exact receiver fibres at that aperture.  It does not establish a convergence theorem from these
finite graphs to the continuous complex torus family.

[counterexample; computational-witness] The discarded text-heavy SVG claimed visual access to the
family while its nontext geometry consisted of manually placed elementary shapes.  The seven
returned images refute that artifact as an engine receiver deed: changing an exact receiver here
changes thousands of projected source incidences while the source remains fixed, a consequence the
manual infographic did not possess or test.

## 5. Reproduction and receipts

[established-bounded; implemented-exact] The focused type-check passed:

```text
cargo check -p holonic-engine --example complex_six_sphere_torus_transport
```

[established-bounded; implemented-exact] The real deed passed after the final receiver widening:

```text
cargo run -q -p holonic-engine --example complex_six_sphere_torus_transport
```

and returned seven images, one 47,583,125-octet complete JSON receipt, and one summary table under
`output/complex-s6-torus-transport/`.  The final driver source address was
`89631984b6b04b7866738d7b04d9b8e1449e36eb0d77fb97af5490e5ee873852` before this record was
deposited.

[open] The output, driver, and closure ledgers are not regenerated in this dirty shared tree.  Their
checks also found a concurrently authored `soma/life` driver, four other unrecorded output
directories, and crate-wide closure motion from unrelated `clifford.rs` and `soma/life` work.
Regenerating them here would bind this deed to material outside its authorized closure.  The
`complex-s6-torus-transport` output remains explicitly `UNRECORDED` until those concurrent owners
close and one coherent ledger regeneration can be committed.

[historical] An attempted `/usr/bin/time` wrapper returned status 127 because that apparatus path
does not exist.  It enacted no driver and returned no mathematical or visual artifact.  The first
successful full deed took approximately 85 seconds at its then-current source closure; the final
changed-closure falsifier, adding the base quotient and widening the family aperture, returned in
11.39 seconds.  After mechanical Rust formatting moved the source address, the focused type-check
and identical real deed returned together in 13.31 seconds.
