# holonic-receiver

A repository-local Typst package with an exact Python companion. It realizes a supplied complex
source/current/mesh at a declared receiver. `holonic-engraving` draws the resulting packet.
These packages are original implementations and are not published to Typst Universe.

## Public Typst maps

```typst
#import "lib.typ": receiver, project, primary-response, causal-interval
#let r = receiver(pinhole: true, distance: 12, focal: 8, near: 1/16)
#let point = project(r, (1, 2, 3))
#let response = primary-response(r, (1, 2))
```

`receiver` retains origin, right/up/view covectors, finite pinhole parameters, a complex analyzer
phase and positive aperture. The Python receiver also carries the actual analyzer covector;
its contraction is applied before the quadratic response. `project` returns `(admitted,depth,point)`; a projection pole returns
no invented finite point. `primary-response` coherently forms the three quadratic responses and
returns premultiplied primaries, alpha and transmittance. The latter two sum to one before paint
quantization. `causal-interval` is a flat, time-oriented Minkowski instance, not a general metric
or an assertion of actual interaction. `metric-pair` and `tetrad-reading` read a supplied metric,
tetrad and arriving vector; the quadratic value is retained, and a null-ray interpretation needs
its actual source hypothesis. The Schwarzschild example verifies those hypotheses exactly. `softmax-cross-entropy-differential` evaluates
`Σ(q_i−p_i) ds_i` under the supplied softmax score chart. Typst values are the exterior numeric
presentation; the exact companion retains the rational source calculations.

## Exact packet compiler

Load `compile.py` as a Python module. `compile_scene` accepts:

- complex vertices and corresponding complex vector currents, separately supplied;
- triangle incidence;
- a `Receiver` with exact rational camera/phase/aperture and reference distribution;
- an explicit common viewport, hatch step, potential (`current` or `entropy`) and mark style
  (`phase`, `mono`, `stipple`);
- a source label for navigation, never as a native identity or a source of coefficients.

No physical current is inferred from a geometry name. The atlas generator supplies its nilpotent
complex field explicitly. The compiler's complex matrix helpers are arithmetic utilities and the
polynomial flow is an exterior reference instance, not a universal HNN law.

Rational source values and exact mark parameters use `[numerator, denominator]` decimal-string
pairs, so browser JSON cannot round large integers. `read_ratio` decodes those pairs. Only the
drawing endpoints/RGB/widths are decimal display values.

The output contains `source_packet` (complex vertices, currents and triangles), `meta` (receiver,
phase, clock, domain, sampling and numerical boundary), and `marks`. Each mark keeps source-face
addresses, exact visible interval and source station parameter; hatches retain their family and
rational level, stipples retain both intersecting levels, and contours retain their source edge. The packet can be read by
Typst or exported with `export_svg.py::scene_svg`, which embeds the source packet in SVG metadata
and attaches face addresses, field levels and exact intervals to the visible marks. It is a working web-format seam; no archived
browser application has been promoted into the native engine.

### Algorithms and their scopes

1. Receiver projection uses exact rational orthographic or pinhole coordinates. Reciprocal depth
   is affine in projected barycentric coordinates, so perspective visibility compares inverse
   depths rather than interpolating ordinary depth incorrectly.
2. A scalar affine field on each triangle intersects a level `kΔ` in a line segment, an empty set,
   or a degenerate fibre. Edges retain their incidence and the full source/current stays in the
   packet. The current potential uses the two analyzer components. Entropy uses the stationed
   contributions `−p_i log q_i` with positive `q_i=(κ/3+P_i)/(κ+ΣP)`.
3. Visibility intersects each segment with candidate projected triangles and their linear depth
   inequalities. It subtracts the union of occluded intervals exactly. The spatial buckets are
   an acceleration of the same test, not an admissibility rule. The viewport clips by exact
   half-spaces. Equal-depth ties do not choose a source. Opaque surface support is an explicit
   geometric visibility model; the display law's alpha is not a material absorption coefficient.
4. A contour is a source boundary, a local silhouette or a declared crease reading. The crease
   threshold is a display receiver (squared cosine below 3/4), never a topological classifier.
5. Monochrome width and the second hatch family use the exact foreshortening quantity
   `1−(n·v)^2/((n·n)(v·v))`. Stipples are intersections of two source level families; no RNG or
   randomized contour geometry is used. For monochrome cross-hatching the grazing cut is 1/2.
6. Logarithms use a rational atanh series after power-of-two range reduction. The explicit tail
   bound is retained. The current implementation targets station error at most `2^-18`; that is
   a declared exterior reading precision. It interpolates stationed readings on each face, not
   the nonlinear entropy of an interpolated distribution. This distinction is retained.
7. Each visible mark evaluates the coherent primary law at its source station. Perspective
   stations use inverse-depth interpolation. The final decimal coordinate error is reported;
   Typst/SVG then quantize to platform paint. No contrast remapping, gamma adjustment or second
   opacity multiplication is applied.

A triangle crossing the near plane is retained in `unresolved_near_faces`; the current compiler
does not silently manufacture a clipped physical surface. The examples keep every source face
in the supported domain. Degenerate source faces and rank-deficient projected faces are retained
separately. A singular view therefore does not delete the source. This restriction belongs to
this exterior mesh compiler and is not a universal certainty gate on native generation.

The hatch flux reading has an exact remainder. For a scalar potential χ and level spacing Δ,
`χ(b)−χ(a)=ΔN+r_b−r_a`, where `N=floor(χ(b)/Δ)−floor(χ(a)/Δ)` and each remainder lies in `[0,Δ)`.
Thus the missing amount is retained rather than claiming a finite ink pattern is the whole field.
A surface current interpretation uses the declared local pairing `ι_j μ=dχ`; on a one-sided
surface its orientation-valued data travel through the existing cover/local-system machinery.

## Build and verification

From the repository root:

```sh
python research/experiments/receiver_engraving/build.py
python research/experiments/receiver_engraving/relations.py
python research/experiments/receiver_engraving/friction.py
python research/experiments/receiver_engraving/finalize.py
typst compile --root research/papers research/papers/source/papers/hnn-information-chemistry/main.typ research/papers/rendered/hnn-information-chemistry.pdf
```

`build.py NAME ...` regenerates selected scenes. Common comparison viewports are fixed across
source time/receiver families. The exact controls cover visibility intervals, projective poles,
mesh links/orientation, nilpotent complex flow, primary coverage and log enclosures. `relations.py`
checks Lorentz/Wigner transport, projective cross-ratio, signed hatch remainders and the real
receiver determinant. No proof-kernel, physical-power or native-learning claim follows from these
exterior controls.

## Recovered methodology and ownership

The source laws are the existing `relational-geometry/src/projection.rs` and `receiver_atlas.rs`,
`holonic-engine/src/dimensional_wave.rs`, and the earlier CAD `render-codec/src/hatch.js`,
`colour.js`, `models.js` and `minkowski.js`. The dated review records their exact scopes.

Fiziko (`54a63dba8e6700a5e70d3508838edebcbf0f45fe`) informed variable-width/generator/occlusion
methodology; vintage-latex (`559011918849a3da819912a7c26493071d542df5`) informed separation of
texture, contour and labels. Their GPL-3.0 and CC-BY-SA-4.0 source material remains external;
no implementation code or example assets were copied. This package is not a complete Fiziko port:
refraction solvers, material-specific objects and heuristic knot-crossing discovery are not
present. It consumes actual supplied geometry and supports original vector engraving of it.

Complex geometry stations are in C³; a higher-dimensional source supplies its actual geometric
projection and retained fibre. Current vectors may have a different dimension when the analyzer
covector matches it. For n≥3, the polynomial example extends by `A_n=A⊕0_(n−3)`; extra coordinates
are retained, and vorticity is read as an exterior two-form outside the special three-dimensional
curl-vector chart. Three display primaries do not impose a three-dimensional source ontology.

`friction.py` adds source-qualified affine force/turn fields on guided linked bodies and an exact
complex interface-diffusion response. These use the same generic packet compiler rather than
the polynomial-fluid generator. The internal contact image is an explicit receiver reconstruction
of four boundary-node states; source statistics and the contact/energy laws remain in its receipt.

### Bounded logarithm stations

`compile_scene(..., log_display_bits=N)` optionally encloses each entropy logarithm
at a dyadic center of denominator `2^N`. It adds `2^-N` to the existing rigorous
series remainder before applying the reference weight. `meta.log_station_radius`
retains the resulting bound; `meta.log_display_bits` declares the chosen chart.
The default preserves the prior exact-series centers. This exterior receiver
measurement controls denominator growth during clipping and changes neither
source vertices, directional currents nor their evolution. The knot-wave figures
use `N=20`; their complete source/measurement comparison is checked by
`research/experiments/receiver_engraving/verify_stress_waves.py`.

### Closed boundaries and the woven continuation

`compile_scene(..., closed_outward=True)` is an optional visibility specialization
for a closed outward-oriented real boundary, viewed from outside. A union of such
opaque bodies is also admissible. Back faces cannot be the first ray intersection;
the full source remains in the packet and `meta.back_faces` records the omitted
population. The general two-sided path remains the default for open ribbons,
nonorientable surfaces and unsupported geometry. The caller supplies the geometric
certificate; the woven level surfaces derive it from their conforming tetrahedral
atlas and oriented boundary. Exact depth/AABB rejection changes no visibility
predicate. `verify_closed_receiver.py` compares the specialization and optimized
rejection to the prior renderer, including a skew pinhole chart.

The woven figures use the same packet-to-SVG backend inside Typst. Compile the
current paper with `--root research/papers` so it can include those rendered vector
faces. To regenerate only this continuation from the repository root:

```sh
python research/experiments/receiver_engraving/woven_bridge.py
python research/experiments/receiver_engraving/woven_ecology.py
python research/experiments/receiver_engraving/constitutive_lobes.py
python research/experiments/receiver_engraving/ecology_details.py
python research/experiments/receiver_engraving/verify_woven.py
python research/experiments/receiver_engraving/verify_closed_receiver.py
```

Its source lives in `woven-scenes.json` and `ecology-detail-scenes.json`; it does
not overwrite the earlier receiver or knot packets. The functions retain phase
storage, source work, contact heat, material flow, exact tetrahedral level cuts and
the difference between interpolated intensity and coherent amplitude.

### Sequence, fold and biochemical source

The sequence continuation supplies its actual FCC conformation and mechanochemical
population source. It uses the same receiver/engraving backend and retains kinetic
mobility/energy readings independently of H/P names. Regenerate this source with:

```sh
python research/experiments/receiver_engraving/sequence_folding.py
python research/experiments/receiver_engraving/sequence_kinetics.py
python research/experiments/receiver_engraving/sequence_figures.py
python research/experiments/receiver_engraving/verify_sequence.py
```

`sequence-scenes.json` contains the returned geometric packets. The bound-site hop
locator is an annotation with its world source/target retained, separate from phase
ink. The kinetic source retains catalyst reuse, net substrate uptake, exact product
moments and source-dependent transition rows; its reference enumerator is not the
native HNN inference algorithm.
