# Holonic rendering — extraction for a JavaScript library

READ-ONLY extraction from `/home/b/Workspaces/holonics`. Nothing modified, built, or run. Quotes verbatim; `path:line` as of 2026-08-30.

---

# PART 1 — DOCTRINE

## 1.1 `blueprint/THE_PRESENTATION_ORGAN.md`

`:7-9` — "**Truth status:** `project-postulate`. **Provenance:** Brandon, 2026-08-08 — *'I want to effectively establish our workbench for all of the same advanced mathematics graphical rendering features, but adapted rigorously to holonics.'*" `:5` — "**It schedules nothing.**"

**The defect it removes** (`:52-58`):
> A hand-placed constant is not a receiver's chart of anything. It is decoration that cannot be falsified, and it is exactly what `canon/04_GEOMETRY_NAVIGATION_AND_WEAVE.md` forbids when it says a projection *"cannot mint source cells."* The palette is fused in beside it as hex literals (`"#174f52"`, `"#7a355f"`), so colour and geometry cannot be varied independently — which makes the one falsifier that matters for a display gauge, *permute the palette and confirm nothing structural moves*, impossible to run.

**Mathematica verdicts** (`:69-79`): symbolic graphics language **adopt**; mesh regions **adopt, harden**; 3D projection **adopt, reassign ownership**; `StandardForm`/`TraditionalForm` **adopt the distinction**; adaptive sampling **refuse**; `ColorFunction` scaling **refuse**; machine-precision plotting path **refuse**; `Exclusions` **invert**; `Manipulate`/`Dynamic` **defer**.

**The central refusal** (`:81-88`):
> Wolfram's symbolic layer is exact, and its plotting path is documented as leaving that exactness at the sampling boundary. Its own reference pages concede the consequence in one sentence repeated across every sampler — of `Plot`: *"Since only a finite number of sample points are used, it is possible for Plot to miss features"*… A missed feature leaves **no trace in the output**. The figure therefore asserts a smoothness it never established, and no reader can tell the difference between a curve that is smooth and a curve whose interesting part fell between two samples.

**THE FEATURE-COUNTING LAW** (`:97-113`):
> **The inversion, and it is the organ's whole content.** Mathematica *samples and hopes*. This body can *count and know*, because `IntegerPolynomial::distinct_root_count` (`exact_value.rs:287`) returns the exact number of distinct real roots in a rational interval from a Sturm sequence, with no float anywhere. So a cell does not get subdivided until it looks smooth; it gets **certified**:
> ```text
> Wolfram:   sample the cell, subdivide up to MaxRecursion, emit whatever was found
> Holonic:   count the features in the cell exactly.
>            count == 0  ->  the cell is certified featureless, and the segment is exact
>            count == 1  ->  isolate it, deposit it as a located feature
>            count >  1  ->  subdivide, with the count as the termination certificate
>            undecided   ->  RETURN THE OBSTRUCTION. Never a smooth-looking lie.
> ```
> A sampler that can miss a feature is replaced by one that can **say how many it has not yet separated**.

**PresentationFace ports** (`:135-149`):
> **Port types.** One inbound: a receiver-supplied exact question (a polynomial and a rational window). One outbound: a `PresentationFace` carrying exact coordinates, located features, **and its obstruction population**. The codec is a separate outbound port that consumes a `PresentationFace` and returns octets.
> **The event.** A receiver asks for a face of an exact object over a declared window. The organ returns the face, the certificate, and every cell it could not decide.
> **Local constitutive law.** Sampling is certified, never adaptive-until-it-looks-right.
> **Receiver question.** *Can this body present its own exact mathematics without any point in the pipeline silently substituting an approximation for a refusal?*
> **Returned consequence.** A figure whose every drawn coordinate is an exact rational, whose feature population is Sturm-certified, and whose undecided cells are carried in the artifact rather than smoothed away.

`:151-154`: "**Grade.** `established-bounded`… bounded to the declared receiver family — integer-polynomial curves over rational windows. Not a general plotting system, and it may not be described as one."

**THE THREE FALSIFIERS** (`:157-173`):
> 1. **The obstruction falsifier.** Present a curve with a feature narrower than the initial cell width. Mathematica's documented behaviour is to miss it silently. This organ must **return it as an obstruction or locate it** — and a run that returns an empty obstruction population on a deliberately unresolvable input has failed. Control: a curve with no features in the window must return an empty obstruction population, or the law is obstructing everything and means nothing.
> 2. **The gauge falsifier.** Permute the palette and re-render. Every exact coordinate, every located feature, and every invariant must be **byte-identical**. If any structural byte moves, colour has become a carrier of a distinction and the receiver-face law is violated.
> 3. **The non-creation falsifier.** Every coordinate in the emitted face must be traceable to an exact source value. No literal layout constant may appear in the owner. Control: the count of emitted marks must equal the count of source features — a projection that emits more marks than the source has structure has minted geometry.

**"AN OPTION IS A RECEIVER COORDINATE"** (`:193-201`):
> `ModelOptions` carries each as a typed field, and `ModelOptions::record()` deposits the option set **into the emitted artifact**, so a figure carries the assumptions it was made under.
> In holonic vocabulary an option is a **receiver coordinate**: it says how a receiver reads, never what the object is. `option_change_never_moves_the_object` enforces exactly that — changing the scaling changes what is read, and the winding does not move.

**Four impossible faculties → four exact replacements** (`:204-209`): `Arg[f]` (the `ComplexPlot3D` colour wheel), "transcendental; **`atan2` appears nowhere in either repository**, verified by search" → "the **winding number**: `eta_boundary_winding` already returns a certified integer from sign-of-cross-product ray crossings"; `Abs[f]` → `SquaredModulus` (`|z|²=Re²+Im²`); `ScalingFunctions -> "Log"` → `IntegerDecades`; `MeshFunctions` by interpolation — "a contour fitted through samples is not a witnessed statement" → "a **certified sign change** of `reading − level`, bracketed between stations".

`:248-251`: "**Therefore no figure from this surface may be captioned as a Hodge decomposition, and no Hodge diamond may be drawn.** … A figure that implied a bigrading would be manufacturing a mathematical structure the body does not have, which is the same defect as minting geometry — worse, because it would be minting a theorem."

`:257-263`: "It does not claim a general plotting system… an organ used past its declared aperture is a defect even when it appears to return. — **It does not make the display an input. Nothing rendered re-enters the construction.** — It does not retire the three example SVG writers by deleting them silently; superseded implementation is deleted only after its replacement's evidence is committed."

## 1.2 `canon/TABLET_THE_MANIFOLD.md` §21

`:336` `## 21. Reflection is the mechanism, and the crossing bears the load`

`:348-354`: "**The interior is an integral over its boundary, and the kernel is built by reflection.** That is not a metaphor for diffusion; it is how the kernel is constructed. The method of images solves a boundary value problem by placing a *reflected* source across the boundary so the two cancel on it — so the boundary condition is satisfied **by construction** rather than imposed, and the resulting Green's function is literally a sum over reflections."

`:362-363`: "**integration by reflection is a boundary construction, and the half-turn is what the reflection costs.**"

`:365-372` — four optical words, four apertures: **reflection** "the boundary sends the current back | the image source; the residual is what does not cancel"; **refraction** "the medium changes the phase velocity | the impedance ratio"; **diffraction** "the *lattice* selects by phase coherence"; **interference** "two paths meet and their **cross term** decides".

`:382-395`: Brandon — *"In knots it is the crossings that bear the load, this is fundamentally how energy distributes in any system."* … "**Section modulus** `Z = I/c`… so **the geometry of the section — not its mass — decides what load it bears.** … the crossing that bears the load is the **hinge**: `TABLET_THE_TURN` §11.5 puts the curvature on the codimension-two hinge between cells and never on a cell's own corners… **A cell carries no curvature; the crossing does.**"

`:408-410`: "each is a way a receiver's aperture selects, and every one of them leaves a residual that is *addressable* — a phase, an angle, a forbidden band, a cross term. An addressable residual is one the loop can return."

## 1.3 §22

`:414` `## 22. The receiver's reach is a causal cone, and the horizon is its radius`. `:418-420` — Brandon: *"not really a 'window' I don't really like that phrase, it's a light-cone, this is relativistic physics"*; *"'horizon' shouldn't be a constant either if it is."*

`:443-462`:
> A receiver sits at an **event**, not on a surface. Its reach is the causal cone at that event:
> - **an apex, not a plane.** Every receiver has its own cone and none is privileged. …
> - **two sheets, asymmetric.** The past cone is what can have conditioned me; the future cone is what I can condition. …
> - **three regions, not two.** Inside: causally connected. **On the null boundary: traversal returns nothing** — `Q(v) = 0`… which in Minkowski *is* the light cone. Outside: not attenuated but **unable to have contributed**. A window has in and out; a cone has a boundary where the returned difference is exactly zero, and that boundary is a surface in the material.
> - **the metric sets the cone, and the metric is already a receiver face of standing.** … So the reach is not installed by anyone — **it is what standing looks like from an event.**
> - **lensing is the metric bending the cone**, not a diaphragm.

`:466-475`: a window enumerates a neighbourhood "**shell by shell** — `−1, +1, −2, +2, …` — in order of `|offset|`. That is a discrete causal diamond… **The horizon is that diamond's radius**… the window at `h` is a **prefix** of the window at `h+1`, so refinement is monotone." `:477`: "### The horizon is read off the material — and a cone propagates, it is not searched".

## 1.4 `canon/TABLET_THE_CHART.md`

`:7`: "A coordinate system is a receiver and the Jacobian is the transport; a radical is a chart that forgets a winding; warp and weft are a reading in a frame."

`:17-25`: "**The claim.** A coordinate system is not a property of a space. It is a declaration made by something that *reads* the space, and a chart change is the pullback of that reading — the Jacobian — and nothing else. … at `LocalChart`: > The chart is not an ambient coordinate system. Its origin and ordered basis vectors state how local components are embodied inside this frame. A receiver can compare it with another chart only through declared frame relations."

**The Receiver** (`:29-38`):
> What a **frame** carries is `LocalChart { origin, basis: [RatVec3; 3], labels }` (`model.rs:45`) — an origin and an ordered basis, exact over `BigRational`, with `gram()` and `orientation()` derived rather than stored. What a **reader** carries is `Receiver { frame, orientation, projection, gauge, route_overrides }` (`crates/relational-geometry/src/projection.rs:502`). Nothing in a `Construction` is written in a coordinate system; a coordinate exists only once a receiver has been applied. Two charts become comparable exactly when a `FrameRelation` (`model.rs:143`) declares an exact `AffineMap3` between them, and a comparison is refused when the relation graph admits more than one route and the caller supplied no `route_overrides`. **A chart with no declared relation to another chart is not wrong; it is incomparable, and the type says so.**

`:42-57`: `projection_pullback_gram` (`projection.rs:853`) builds the Jacobian by hand — for `PerspectiveRay{f}`, `row_x = ( f/(f+z), 0, −f·x/(f+z)² )`, `row_y = ( 0, f/(f+z), −f·y/(f+z)² )`; `gram_from_rows` returns `JᵀJ`; `receiver_metric` (`:827`) "conjugates it by the receiver's orientation and divides by the gauge's own reference length, so **the receiver measures its own declared reference as one and no universal ruler exists anywhere in the path**." `Orthographic`/`Isometric` are constant Grams — the latter "the `(2/3, −1/3)` Gram whose fiber is `span{(1,1,1)}`".

`:59-64`: "**What escapes is `JᵀJ` and not `J`.** … the metric arm keeps the magnitude and discards the hand… the hand… is retained… as `sign(det(basis))` in `LocalChart::orientation()` and as `TriangleFaceSignature::parity` (`projection.rs:483`)."

`:129-137`: "`ray_triangle_crossing` (`receiver.rs:2361`) is Möller–Trumbore over `Rat`: the determinant decides degeneracy by exact zero rather than by tolerance… it is the one chart in this table that declares no origin, and it is the one the display path can consume without importing a frame (`crates/holonic-engine/README.md:626`: color is derived by exact barycentric ratios of the receiver's own phase triple into the monitor's RGB basis, *'RGB remains a display quotient, not a universal physical spectrum'*)."

## 1.5 COLOUR

**Direct answers.** (1) **Yes** — colour is a receiver quotient of a spectrum/phase, and "after superposition" is a *law of stages*. (2) **No** — the Four Colour theorem is **not** a law of the presentation; it appears once, disclaimed. (3) "The receiver forms colour" requires per-mode superposition *before* response, three exact nonnegative quadratic responses, a declared positive aperture, a saturating rational quotient, and exactly one terminal `u8` quantization, last.

**The definition** — `research/records/2026-08-05_THE_RECEIVER_QUOTIENTS_THE_SPECTRUM_CAUSALITY_LOCKS_ITS_FACES.md:163-169`:
> `[definition]` Given a caused source, a declared transport, and a declared receiver family:
> - the **spectrum** is the receiver-local phase population the transport delivers;
> - the **lines** are the poles of that transport;
> - the **colour** is the equivalence class into which the receiver's finite channel set collapses the spectrum; and
> - the **metamers** are the kernel of that collapse.

Same file: `:18` `## 1. Colour is a kernel`; `:28-29` "Colour is therefore not a property of light. It is a name for a fiber of a receiver's response map."; `:156` "**Shape is the spatial spectrum; colour is the spectral spectrum.**"; `:54-55` "**Channel count is not resolving power.**"; `:62-63` "**Refusing more light distinguishes more.**"; `:71` "**A filter can found a channel.**"

**The ordering of stages** (`:38-45`):
> coherent paths superpose **before** intensity; incoherent spectral populations add **after** the relevant quadratic response; receptor sensitivity forms the colour equivalence.
>
> `[interpretation]` The quotient is therefore **layered**, and each layer forgets something different: coherent-to-incoherent forgets phase; incoherent-to-receptor forgets spectral shape.

`research/records/2026-07-30_THE_PRIME_POWER_EMITS_THE_TRAVELING_PHASE_THE_RECEIVER_FORMS_COLOR_AFTER_SUPERPOSITION.md:234-238`: "A color gradient is therefore not a list of interpolated endpoint RGB values. It is the receiver face of a spatially changing transported field." `:134` heading: `## Color is a receiver equivalence, not a source label`.

**The mechanism** (`:26-38`):
```text
caused arithmetic incidence -> exact modal wave current and physical successor
-> receiver restriction of the contemporary current
-> exact co-present phase population at each terminal contact
-> declared receiver-primary response -> one final monitor quantization
```
> The first three arrows are source/current physics. The last two are observation. Neither can stand in for the other.

`:136-149`: "Currents of one mode are added before response… They can therefore reinforce or cancel. **Distinct modes remain separate through this addition and cannot cancel merely because a display projects them to one address.**" `:149-156`: `P₀=Σ(Re A_m)²`, `P₁=Σ(Im A_m)²`, `P₂=Σ(Re A_m+Im A_m)²`. `:157-188`: "For declared positive aperture κ, let `D = κ+P₀+P₁+P₂`. The outer membrane returns the premultiplied four-coordinate response `(R,G,B,α) = (P₀/D, P₁/D, P₂/D, (P₀+P₁+P₂)/D)` and exact transmittance `τ = κ/D`. Consequently, `R+G+B = α`, `α+τ = 1`."

**The five rejected moves** (`:18-24`) — the JS library must do none:
> 1. mapped each exact complex current independently into one hue;
> 2. ignored its modal coexistence with other currents at the same receiver contact;
> 3. added a screen-space brightness ramp which had no source law;
> 4. quantized every contribution to `u8` before composition; and
> 5. saturating-added those terminal bytes, destroying exact cancellation and interference.

`:201-203`: "**No constituent type owns a palette.** Chroma occurs only where the exact modal population and declared receiver transduction produce it." `:190-193`: "This is a declared analytical monitor gauge. It does not assert that real optical phase is hue, that a prime is a wavelength, or that alpha is a fourth emitted wavelength."

**Rust owner** `holonic-engine/src/dimensional_wave.rs`: `ExactPremultipliedReceiverResponse{primaries:[Rat;3],alpha,transmittance}` `:196`; `ExactReceiverPrimaryDoctrine{aperture,support_response}` `:219`; `transduce` `:235-267` — `responses[0]+=re*re`, `responses[1]+=im*im`, `diagonal=re+im`, `responses[2]+=diagonal*diagonal` `:243-246`; `denominator=aperture+total` `:251`; `debug_assert_eq!` on `Σprimaries==alpha` `:255` and `alpha+transmittance==1` `:261`. Doc `:215-217`: *"This is an inspectable display gauge. It is not a universal color law and does not identify phase, wavelength, or a source constituent with red, green, blue, or opacity."*

**The gauge law.** `2026-07-13_COLOR_IS_A_RECEIVER_FACE_THE_HIGHLIGHT_IS_THE_RELATION.md:13` "Color is a further receiver-relative equivalence formed through the delivered spectrum, contemporary organ, gaze, history, surrounding field, and receiving frame."; `:27` "Color is consequently not wavelength alone but light ⊕ transducer ⊕ place ⊕ traversal ⊕ history."; `:53` "A global change of `G` changes only the human colors; it cannot alter `T`."; `:57-58` "**Raw rows and a text equivalent remain beside every visual mark. Color is never the only carrier of a distinction.**"

`canon/TABLET_THE_REALIZER.md:202-206`: "**Colour is derived from the receiver's own state, not assigned.** `examples/desktop_receiver.rs:49`: each embodied receiver's exact coordinate, momentum and net impulse form its contemporary phase triple; the monitor membrane subtracts the least component — which retains signed phase orientation — and takes exact barycentric ratios into its local RGB basis. RGB is the outer transducer's basis, not a colour ontology."

`2026-07-28_…OBSTRUCTION….md:161-162`: "**A hard-coded edge color is not a phase law.**" `receiver_phase_atlas.rs:28-33`: a fixed `CHANNEL_COUNT = 3` "made *one receiver's* channel population — RGB — a property of the law that reads receivers", against `canon/THE_AUTHORED_LEVEL.md` §1 — *"A level is either read off the material or declared by the caller. It is never authored inside the organ."* `field_atlas.rs:204-205`: "RGB channels are receiver coordinates, not universal wavelengths."

**The Four Colour theorem.** `2026-07-25_THE_SOURCE_LOOP_IS_TOO_COARSE_THE_RECEIVER_LOOP_IS_NOT_THE_SOURCE.md:7` banner: "**NO FOUR-COLOR GOVERNOR**". `:12`:
> The work did not seek a Four Color Theorem application. That theorem supplied one useful connection among planar faces, triangular duals, and finite junction states, but it neither scheduled nor governed the construction.

`:75-78` — what did the work is topology, not colouring: "The direct receiver has no crossing and a four-face dual. The precessed receiver adds one apparent `AC/BD` crossing and presents a five-face dual with a different Ihara polynomial and different primitive-loop population. No source incidence changed." `:164-165`: "No color assignment, palette optimizer, absolute camera, floating-point projection…".

**Measured absences.** Zero `Kempe` and zero `Heawood` hits in `canon/`, `blueprint/`, `research/records/`, `research/equation-atlas/`. Zero four-colour / chromatic-number / face-colouring code in `crates/` or `soma/`. **No chromatic-number law and no four-colour law for figures exists anywhere.** The only "emergent color" occurrence, `2026-07-30…md:318`, names the `dimensional_wave` transduction. `2026-08-20_THE_SWING_IS_HARMONIC_CONJUGATION….md:191-200` contributes only "**Achromaticity means the transport carries no spectral remainder: it is a rebase.**"; its "four" hits are the cross-ratio's four participants and `Λ/2Λ`.

## 1.6 Lines, thickness, arrows, traces, occlusion

**Measured empties.** No law on line thickness, stroke width, hairline, dash, hidden-line removal, z-order, painter's algorithm, draw order, or arrowheads exists in `canon/`, `blueprint/`, or `research/records/`. Every `arrow` hit is a category-theoretic morphism or `soma/body/src/arrow.rs`; every `stroke` is an engine or lightning return stroke; the only `thickness` is physical.

`canon/TABLET_THE_REALIZER.md:198-201`: "**A raster member is not a point sample.** `presentation.rs`: *'A matrix member receives every primitive whose support intersects its finite area; its center is never used as a surrogate ray.'* Point-sampling a pixel is the same defect as sampling a curve, one dimension down."

`presentation.rs:703-707` — the one stroke clause in the body: "Area fractions are used only for two-dimensional triangle support. A thread carries its exact source-parameter interval instead: **a line has no area until a downstream display gauge declares a stroke law.** Conics are currently support-certified but retain `SupportOnly` until an exact arc measure is admitted."

`canon/04_GEOMETRY_NAVIGATION_AND_WEAVE.md:47-59`: "A shadow is a receiver relation among source geometry, occluder, propagation law, and receiving surface. It is neither a detached property of the source nor a second source object. A projection can identify many distinct source fibers; **the unresolved preimage must remain open when a later receiver can distinguish it.** Perspective derivation therefore retains: … occlusion/intersection event; … chart transition/projective depth; and unresolved source fibers behind equal projected faces."

`2026-07-26_THE_LOCAL_FIBERS_RECEIVE_THE_CAUSED_WORLD….md:274-277`: "Material, lighting, occlusion, color, and labels are world-side transducers from the complete crossing fiber. A transducer may select a visible surface, integrate several layers, or display all crossings. **Its decision remains inspectable and cannot delete the underlying geometry receipt.**"

`canon/TABLET_THE_TURN.md:494-498`: "`receiver_topology.rs:65` returns `DiagramNodeKind::ApparentCrossing { under, over }`… `decorated_path.rs:41` carries `CrossingRole::{Over, Under}` with a `crossing_orientation: i8`. … `EqualDepthCrossing` and `MultipleCrossingAtOnePoint` are refused by name rather than perturbed away. **That is a signed knot diagram in all but the word.**"

`2026-07-19_THE_LIVE_WEAVE….md:470`: "**silhouette does not determine lineage;**" `2026-08-21_…REFUSED_THE_WHITE_BACKGROUND….md:106-110` — the one background law: declaring white when "the diagram's actual background is `#FBFAF5`" was refused, corrected "to read the exact border sample at `(0,0)`".

---

# PART 2 — THE EXISTING EXACT RENDERERS

## 2.1 `relational-geometry/src/projection.rs` (1613)

`:1-5`: "Projection is a mathematical map owned by the receiver. The renderer consumes its output; it does not own the camera relation or feed approximated coordinates back into the construction."

Types: `Receiver{id,name,frame,orientation,projection,gauge,route_overrides}` `:380`; `ProjectionLaw{Orthographic, PerspectiveRay{focal_distance:Rat}, StereographicNorth, Isometric}` `:345`; `ProjectedPoint{exact:ExactVec2, rational:Option<RatVec2>, receiver_point:RatVec3, depth:Rat}` `:413` — `:415` "used for exact crossing tests and **never stores a render approximation**"; `ReceiverGauge{anchor,reference}` `:330`; `ProjectedPolyline` `:423`; `ReceiverMetric` `:469`; `TriangleFaceSignature{…,parity:i8}` `:478`.

`project_point` `:501` = `receiver.orientation.matrix().apply(&transport.apply(point))` then `project_receiver_point` `:524-593`:

| law | rational face | depth | refusal |
|---|---|---|---|
| `Orthographic` `:529` | `(x,y)` | `z` | — |
| `PerspectiveRay{f}` `:541` | `(f·x/(f+z), f·y/(f+z))` | `f+z` | `f+z==0` ⇒ `Singular("the point lies on the receiver's focal plane")` |
| `StereographicNorth` `:562` | `(x/(1−z), y/(1−z))` | `1−z` | `1−z==0` ⇒ `Singular("the point is the stereographic receiver pole")` |
| `Isometric` `:580` | **`rational: None`**; `x'=(x−z)/√2`, `y'=(x+z−2y)/√6` as `ExactExpr` | `x+y+z` | — |

`Isometric` is the radical chart, so `analyze_crossings` refuses it `:1070-1080` (`exact:false`, `"crossing predicates for the radical isometric chart are not yet implemented"`).

`Crossing{first_entity,first_segment,second_entity,second_segment,point:RatVec2,first_depth,second_depth,over_entity,orientation_sign:i8}` `:1034`; `CrossingAnalysis{crossings,discriminants,exact:bool,boundary:Option<String>}` `:1047`; `ProjectionDiscriminantKind{CollinearProjectedSegments,EndpointIntersection,EqualDepth}` `:1017`.

**`classify_pair` `:1154-1252`:** (1) `d1=b−a`, `d2=d−c`, `offset=c−a`. (2) `den = d1.cross(&d2)` `:1163` — the orient2d primitive. (3) `den==0 && offset.cross(&d1)==0` ⇒ `CollinearProjectedSegments`, *"two distinct embedded segments occupy one projected line"* `:1174`. (4) `s = offset.cross(&d2)/den`, `t = offset.cross(&d1)/den` `:1180`; reject outside `[0,1]` — exact `Rat`, no epsilon. (5) `point = a + d1·s`. (6) `s` or `t` exactly `0`/`1` ⇒ `EndpointIntersection`, *"a projected crossing reaches a segment endpoint"* `:1204` — **refused, never nudged**. (7) recover **source** parameters via `source_parameter`, `interpolate` the 3-D points, `depth` each `:1215`. (8) `first_depth == second_depth` ⇒ `EqualDepth`, *"the receiver cannot order the two projected branches by depth"* `:1226`. (9) `first_is_over = first_depth < second_depth`; `orientation_sign = sign(over_dir.cross(&under_dir))` — the over-strand is the **left** argument `:1232`.

`adjacent` `:1141` skips consecutive segments of one entity and the closed-thread wrap pair. `source_parameter` `:1254-1309` inverts in closed form: orthographic via `solve_linear_parameter` `:1311`; perspective `s = (screen.x·(f+a.z) − f·a.x)/(f·Δx − screen.x·Δz)`, else the `y` form; stereographic `s = (screen.x·(1−a.z) − a.x)/(Δx + screen.x·Δz)`; isometric `None`. Also `ProjectiveRatio` `:60`, `ExactSpin` `:144`, `ReceiverOrientation` (Cayley) `:269`, `projection_pullback_gram` `:853`, `triangle_face_signature` `:930`.

## 2.2 `relational-geometry/src/receiver_topology.rs` (1870)

`:1-8`: "Source incidence and projected incidence are deliberately distinct… A regular projected crossing is split only in the receiver diagram and retains the two source branches and their over/under order. **Faces and their dual graph are therefore receiver testimony, not a reconstruction of the source.**"

`DiagramNodeKind{SourceIncidence, ApparentCrossing{first,second,over,orientation:i8,first_source_parameter:Rat,second_source_parameter:Rat}}` `:61` — `:70` "distinct from interpolation in the screen plane for perspective and stereographic receivers"; `DiagramEdge{id,source,from,to,screen_parameter_start,screen_parameter_end}` `:88` — `:93` "diagram testimony and must not be read as chronology on the source segment"; `DiagramDart{edge,forward:bool}` `:100`; `DiagramFace{id,boundary,signed_double_area:Rat,bounded:bool}` `:106`. Edge splitting `:614-634`: split points sorted by screen parameter, consecutive pairs become edges; a zero-length edge ⇒ `ZeroDiagramEdge`.

**THE ANGULAR ORDERING PREDICATE — `compare_rays` `:1055-1067`** (no angle, no atan2, no sqrt):
```rust
let first_upper  = first.y.is_positive()  || (first.y.is_zero()  && !first.x.is_negative());
let second_upper = second.y.is_positive() || (second.y.is_zero() && !second.x.is_negative());
match (first_upper, second_upper) {
    (true, false) => Ordering::Less,  (false, true) => Ordering::Greater,
    _ => match sign(&first.cross(second)) {
        1 => Ordering::Less, -1 => Ordering::Greater,
        _ => first.norm_squared().cmp(&second.norm_squared()), }, }
```

**FACE TRACING — `recover_faces` `:956-1032`:** (1) `outgoing[node]`: dart `2i` leaves `edge.from`, `2i+1` leaves `edge.to`. (2) refuse a disconnected diagram `:969`. (3) sort each node's darts by `compare_rays(dart_direction(…))`, tie-broken by dart index. (4) walk unvisited darts; the next dart is the **predecessor-cyclic** of the reverse dart `current ^ 1` in the target's sorted list — `current = target_outgoing[(reverse_position + len − 1) % len]` `:1011`. (5) `signed_double_area = Σ points[from].cross(points[to])`, exact shoelace `:1015`. (6) **outer face ⇔ non-positive**: `bounded: signed_double_area.is_positive()` `:1026`.

Euler check `:637-646`: `expected_faces = edges.len() + 2 − nodes.len()`; mismatch ⇒ `NonCellularEmbedding`. Face-dual graph `:647-661`: one vertex per face, one dual edge per diagram edge joining `dart_faces[2i]`/`dart_faces[2i+1]`. Ihara (`ihara_signature` `:1098`, `cross_check_ihara` `:1244`) runs on both graphs over `ExactPolynomial`/`BigInt`. `TopologyDiscriminant` `:316-351`: `UnsupportedRadicalProjection`, `DeclaredIncidenceDoesNotMeet`, `DistinctSourceVerticesCollapse`, `CollinearBranchOverlap`, `UnrelatedEndpointCoincidence`, `EqualDepthCrossing`, `MultipleCrossingAtOnePoint`, `ZeroDiagramEdge`, `NonCellularEmbedding`.

## 2.3 `relational-geometry/src/receiver_atlas.rs` (871)

`ReceiverGrain{width,height}` `:49`, doc `:45-47`: "The horizontal receiving interval is `[-width/height,width/height]` and the vertical interval is `[-1,1]`. **Pixel apertures therefore retain the exact aspect ratio without a rendering scalar.**"
`aperture(c,r)` `:65-83`: `x_min=(2c−w)/h`, `x_max=(2(c+1)−w)/h`, `y_min=(2r−h)/h`, `y_max=(2(r+1)−h)/h`.
`address(point)` `:85-102`, doc: "Return every closed aperture containing the exact point. **A point on a seam deliberately returns two or four cells. Selecting one by array convention would erase a real receiver discriminant.**"
`axis_cells` `:105-131`: `scaled = (coordinate_scale·coordinate + offset)/2`; outside `[0,cell_count]` ⇒ empty; `scaled.denom().is_one()` ⇒ seam, return `{seam−1, seam}` clipped; else `floor(numer/denom)`.
Also `PixelAperture` `:140`, `ApertureAddress{cells}` `:149`; `SwingCell{id,name,pivot:[OccurrenceId;3],witness}` `:172`; `ReceivedSwing{cell,cross_ratio:Rat}` `:190`; `GrainComparison{…,indistinguishable_at,distinguished_at,unaddressed_at}` `:221`.
`cross_ratio(points)` `:664-694`: four marks else `NotFourMarks`; `direction = p1−p0`, zero ⇒ `CoincidentPivotMarks`; every other point must satisfy `direction.cross(&(p−p0))==0` else `MarksOutsideOnePencil`; project onto the axis with nonzero direction component; `((c−a)(d−b))/((c−b)(d−a))`; zero denominator ⇒ `RepeatedProjectiveMember`. Doc `:630-632`: "Nothing here is approximated and no quadruple is repaired: a degenerate one is refused by name."

## 2.4 `relational-geometry/src/decorated_path.rs` (927)

`:1-11`: "**An apparent crossing never creates source adjacency.** Its two branch parameters merely refine the common path grain… the carrier itself is not a scalar weighted graph."
`CrossingRole{Over,Under}` `:41`; `ReceiverCrossingMark{source_parameter:Rat, screen_point:RatVec2, other_branch, role, crossing_orientation:i8}` `:47` — `:48` "Parameter on this source branch, not on its projected screen chord"; `ReceiverIntervalFace{source_start,source_end,screen_start,screen_end,screen_chord_squared,gauge_chord_squared}` `:58`; `ReceiverDartFace` `:70` — `:79` "Only crossings actually visible to this receiver appear here"; `ExactTurn{parallel:Rat, transverse:Rat}` `:102`, doc `:96-100` "**It retains both the dot and oriented-area faces of the turn and therefore does not collapse the turn to an angle scalar.**"; `ReceiverClosedTrace.crossing_word` `:169`.
`collect_crossing_marks` `:388-443`: each `Crossing` deposits **two** marks, one per branch, `role: if over == first { Over } else { Under }` `:412`.

## 2.5 `holonic-engine/src/presentation.rs` (2904)

`:1-7`: "Receiver faces are related by exact, caused projective maps. Their complete continuous primitives and crossing relations are assembled before a platform boundary supplies a finite matrix. **A matrix member receives every primitive whose support intersects its finite area; its center is never used as a surrogate ray.**"

`TerminalMatrixSpec{width,height,boundary}` `:506`; `PresentationBoundary{horizontal_span:Rat,vertical_span:Rat}` `:490`; `ExactCell{lower:[Rat;2],upper:[Rat;2]}` `:554`; `PresentationAddress{column,row}` `:484`.
`cell(address)` `:527-550`: `left = −H/2 + c·H/W`, `right = −H/2 + (c+1)·H/W`, `top = +V/2 − r·V/H`, `bottom = +V/2 − (r+1)·V/H` — **y inverted at the chart**.
`ExactCellSupport{Interior,Boundary,OpenProjective}` `:577`; `SurfaceCoverage{AreaFraction(Rat), SourceParameterInterval{start,end}, SupportOnly}` `:709`; `SurfaceDepth{Range{near,far}, Unavailable, OpenProjective}` `:717` — `:718` "smaller is nearer"; `SurfaceContribution{member,support,coverage,depth}` `:729`; `OcclusionObstruction{MissingDepth,OpenProjectiveDepth,OverlappingDepthRanges,EqualDepth}` `:738`; `OcclusionFace{Empty, Ordered{front_to_back}, Open{members,reason}}` `:750`, doc `:745-748` "**`Open` is a real result. It prevents the raster codec from inventing a winner where the declared receiver has not proved one.**"; `IntegralPhaseCell{NoLevel, Levels{first,last}, OpenProjective}` `:606` — `:602` "`OpenProjective` means the phase denominator crosses zero there, so no finite integer interval may replace that seam".

**`occlusion_face` `:1174-1239`:** empty ⇒ `Empty`; one ⇒ `Ordered`; any `Unavailable` ⇒ `Open{MissingDepth}` carrying the **complete** competing population; any `OpenProjective` ⇒ `Open{OpenProjectiveDepth}`; sort by `depth_near`, tie-broken by member id; for each consecutive pair `far(prev) >= near(next)` ⇒ `Open{EqualDepth}` when both ends coincide else `Open{OverlappingDepthRanges}`; otherwise `Ordered{front_to_back}`.
**`triangle_depth_over_polygon` `:1142-1172`:** evaluate the depth law at every clipped-polygon corner; zero or sign-changing homogeneous denominator ⇒ `OpenProjective`; else `Range{near:min, far:max}`.
Support: `clip_polygon_to_cell`/`clip_polygon_edge` (Sutherland–Hodgman over `Rat`) `:1259`, `polygon_area` `:1324`, `surface_contributions_for_primitive` `:1050`. `ExactSurfacePresentation` `:776`, doc `:769-774` "**The integer raster/colour codec is downstream and cannot change these cells.**"; its counters are "Receiver-work testimony… [they] do not participate in surface identity or in candidate admission." `:780`. **No feature-counting termination here.**

## 2.6 `display.rs` (133) and `live_presentation.rs` (281)

`display.rs:1-6`: "**The core crossing geometry and receiver assembly do not own color or occlusion.** A world supplies a `PresentationTransducer`… This module only packs those returned consequences into a platform carrier." `Rgb8` `:13`; `DisplayFace` `:20`; `DisplayPatch` `:28`; `trait PresentationTransducer{fn transduce(&self,&PresentationMember)->Rgb8}` `:34`, doc `:35-37` "**The transducer, not the geometric core, owns any decision to select, combine, or refuse contributions and crossing layers.**"; `encode_ppm` `:61`, doc `:57-60` "PPM is only an outer carrier. **Decoding it cannot feed approximated geometry back into the causal construction.**"

`live_presentation.rs:1-8`: "**A terminal work span is only a hidden physical partition of the bounded display quotient: it is never a simplex, a chronology node, a wavefront, or a visible partial successor.** Every receiver generation is assembled privately and becomes visible as one atomic continuous face." `TerminalTile{left,top,width,height}` `:24`; `ReceiverCoupling` `:50`; `LiveTilePayload{members,colors}` `:90`.

## 2.7 `holonic-engine/src/certified_face.rs` — the feature-counting owner

`:1-45`: "A presentation face whose feature population is Sturm-certified, not sampled. … This module never subdivides in the hope that the picture settles down… The cell law is therefore:
```text
  count == 0   the cell is certified featureless -- the segment stands, exactly
  count == 1   isolate it and deposit a located feature
  count >  1   subdivide, with the count itself as the termination certificate
  undecided    deposit an OBSTRUCTION -- never a smooth-looking lie
```
## Colour is not here
There is no colour, no palette, no pixel and no output format in this module, and that is structural rather than incidental… The gauge lives in `presentation_gauge`, downstream, and consumes this face without being able to change it.
## No coordinate here is authored
Every rational in a returned face is either a receiver-declared window endpoint or an exact value of the source polynomial. There is no layout constant in this file."

`ReceiverWindow{lower,upper,initial_cells,subdivision_bound}` `:57`; `LocatedFeature{interval, variations_at_lower, variations_at_upper}` `:107`; `CellObstruction{interval, unresolved_feature_count:u32, reason}` `:119`, doc `:113-117` "This is the type whose existence is the entire argument of the module. An adaptive sampler has no such type: when it stops subdividing it emits geometry regardless, and the failure is indistinguishable from success."; `ExactStation{abscissa,ordinate}` `:139`; `CertifiedFace{…,certified_feature_count:u32}` `:150`, doc `:146-148` "This is the `StandardForm` of the figure in Wolfram's sense — the invertible one. A rendered picture is the `TraditionalForm`."; `population_reconciles()` `:171` — `located + Σ unresolved == certified_feature_count`.

`certify_face` `:277-333`: count the whole window **first** with endpoint roots separated `:283`; `step = width/initial_cells`; inspect every cell boundary exactly once so a shared-boundary root is located once `:294`; per cell deflate at both endpoints then `resolve_cell`.
`resolve_cell` `:339-410`: `count==0` ⇒ return (`:360` "// Certified featureless. This is the sentence a sampler cannot say."); `count==1` ⇒ `LocatedFeature` with Sturm sign-variation counts; `remaining_subdivisions==0` ⇒ `CellObstruction{unresolved_feature_count: count, SubdivisionBoundReached}`; else midpoint, locate-and-**deflate** it if it is itself a root, recurse both halves. `closed_interval_census` `:245` deflates endpoint roots so `distinct_root_count` applies without refusal.

## 2.8 `holonic-engine/src/presentation_gauge.rs` — the gauge and the one vector codec

`:1-34`: "The declared display gauge, and the one vector codec this body owns… `render` takes the face by shared reference and cannot mutate it, which is the rule made structural rather than promised in a comment… Every emitted mark carries its exact rational in a `data-` attribute, so the artifact is readable as a table without being re-rendered, and colour is never the only carrier of a distinction."

`DisplayGauge{name,ground,curve,feature,obstruction,rule}` `:55`, doc `:49-53` "The gauge is supplied by the presenting world, never inferred from the data. Deriving colour from the data's own extremes — Wolfram's `ColorFunctionScaling`… would make the same exact value take different colours in different figures." `declared()` `:70-74` (`#f7f3e8`, `#173a3a`, `#a13d2d`, `#7a355f`, `#8a8f88`), `permuted()` `:88`; doc `:65-66` "nothing downstream may depend on these particular strings, and `permuted` exists to prove that nothing does."
`CanvasChart{width,height,margin}` `:103`; `PlacedMark{role,x:Rat,y:Rat,source_abscissa,source_ordinate}` `:148`.
`place` `:161-243`: `place_x(a)=margin + inner_width·(a−window.lower)/window_span` `:178`; `place_y(o)=margin + inner_height·(high−o)/ordinate_span` `:183` — `:181-182` "**The reflection belongs to the chart, not to the mathematics.**" A degenerate ordinate range is widened **symbolically by one unit** "rather than dividing by zero or perturbing with a float epsilon" `:172`. The feature axis is `place_y(0)` when zero is in range, else clamped to the nearer edge — "The clamp is a CHART decision, exact and recorded" `:196-200`. A feature's `x` is its interval midpoint, "a chart convenience, not a claim that the root is there. The exact isolating interval travels with the mark." `:211`.
`octet_coordinate` `:245-257`: "This is the single lossy step in the whole organ, it happens once, and it happens here — at a declared apparatus face, after every mathematical decision has been made. **Nothing downstream of this value re-enters the construction.** … **no float is constructed at any point.**" Body `:255`: `(numerator*2 + denominator) / (denominator*2)`.
`render` `:264-316`: `<polyline fill="none" stroke="{gauge.curve}" stroke-width="2" …/>` `:291`; `let radius = if mark.role == "station" { 2 } else { 5 };` `:301`; each mark `<circle … data-role data-abscissa data-ordinate/>` `:302`; `<metadata>` `:274` "Exact certified face… the palette is a declared gauge and carries no structure. Obstructions are drawn because they were returned, not omitted."
`rasterize` `:321` with integer `draw_line` (Bresenham) `:378`, `draw_disc` (`dx²+dy² <= r²`) `:407`, `set_sample` `:423`.
`structural_residue` `:471-497` — **the gauge falsifier**: rewrites the value inside `fill="`, `stroke="`, `data-gauge="` to `GAUGE`, "leaving every other byte — coordinates, roles, exact source values, prose — untouched" `:474`. `:465-470` records the fixture bug — both gauge names were eight characters, so any length-proportional leak was invisible; **the two palettes must differ in length as well as content.**

## 2.9 `model_surface.rs` — the option convention and the level-set law

`:18-22`: "**`Arg` cannot be computed.**… the phase face is **not approximated**: it is replaced by the exact object that Wolfram's colour wheel is a lossy picture *of* — the **winding number**"; `:33-34` "Wolfram's options are receiver coordinates in this body's vocabulary: they say how a receiver looks, not what the object is."
`MeshFunction{reading:ExactReading, levels:Vec<Rat>}` `:235`, doc `:227-233`:
> A declared level set: the exact analogue of one entry of Wolfram's `MeshFunctions`. Wolfram draws a mesh line where an expression takes evenly spaced values, found by interpolation between samples. **Here a level is a certified sign change of `reading(z) - level` between consecutive stations: the crossing is bracketed exactly, and the bracket is what is drawn. A mesh line is therefore a statement with a witness, not a curve fitted through samples.**

`certified_crossings` `:258-291`, the whole contour algorithm `:276-278`:
```rust
let crosses = (left.is_negative() && right.is_positive())
    || (left.is_positive() && right.is_negative()) || left.is_zero();
```
returning `MeshCrossing{reading, level, lower_station, value_before, value_after}` `:248` — the *bracket*, never an interpolated point. Doc `:260-262`: "Where the reading is exactly the level at a station, that is recorded as a crossing at that station rather than being perturbed away."
Others: `ExactReading` `:54`, `quadrant_of` `:147`, `read_turn` `:187`, `ScalingFunction`/`integer_decade` `:300-360`, `ModelOptions` `:403`, `read_model` `:504`.
**Grep `isoline|contour|level set|hatch|streamline|marching` over `crates/**/*.rs`:** the only level-set owner is `certified_crossings`; other hits are `receiver_phase_atlas.rs:4`, `causal_reflection.rs:127`, one test name. **No hatching, streamline, or marching-squares code exists.**

## 2.10 `receiver_phase_atlas.rs` (1817)

`:1-8`: "Receiver-local phase germs induced from finite image testimony. **A sensor address is only a witness.** Persistent extrema of exact first and second phase differences cause analytical germs whose quadratic level sets are native conics in the receiver chart. Mutually admitted germs carry an exact connection correction; a closed three-germ incidence reports its path-ordered holonomy. **Triangular incidence therefore does not pretend to be curvature by itself.**"
A **phase cell** is `ReceiverPhaseAddress{column,row}` `:80` carrying `ReceiverChannelSample(Vec<u8>)` `:35` or `None` — "absent testimony… It cannot contribute a jet, a maximum, or a germ." `:95`. `channels: NonZeroUsize` is declared per section; a mismatch is `ChannelPopulationDisagreement`, "refused by name rather than truncated or padded" `:92`.
Pipeline: `admit_section` `:625` → `extract_germs` `:707` → `phase_jet` `:837` / `window_maximum` `:1006` → `form_connections_and_cycles` `:1049` → `connection_correction` `:1194`. Carriers: `ExactReceiverPhaseJet` `:145`, `ReceiverConicSpecies` `:174`, `PhaseHand` `:206`, `ReceiverPhaseGerm` `:240`, `ReceiverPhaseCycle` `:302`. **Seams:** no seam blend; a germ pair is either mutually admitted (carrying an exact connection correction) or not.

## 2.11 Winding — `exact_analysis.rs`

`polygon_winding` `:1812-1835` — the sign-of-cross ray-crossing predicate that replaces `atan2`:
```rust
let cross = start.cross(end);                                                     // :1825
if start.im.is_negative() && end.im.is_positive() && cross.is_positive()  { with_the_turn }
else if start.im.is_positive() && end.im.is_negative() && cross.is_negative() { against_the_turn }
```
Ray parameters `0..=32` are tried until no vertex lies on the ray `:1813`; exhaustion ⇒ `NoAdmissibleWindingRay` `:1834`. **The degenerate ray is escaped by changing the ray, not by perturbing the polygon.** `eta_boundary_winding` `:1837-1912` walks the four rectangle sides via `certify_boundary_segment` (bounded by `eta_second_derivative_bound`), then takes the polygon winding.

## 2.12 The example drivers

| driver | what it renders, from what | depth / occlusion | colour & lines |
|---|---|---|---|
| **`exact_perspective_surface.rs`** `:1-5` "Render a small exact 2D/3D surface scene through **cell coverage, not point sampling**. **The JSON sidecar is the primary artifact.** … open occlusion cells are colored as open rather than assigned an invented frontmost surface." | scene of 2 `Triangle` + `Thread` + `Conic` → `PerspectiveRay`/`RayFamily::Central` `:98` → `assemble_support_presentation_with_cpu` `:255` → `exact_surface_presentation_with_executor` `:268` → `ExactRaster` → `.json`/`.ppm`/`.png` | **read, never computed** `:184-213`: `Empty` paints nothing; `Ordered` takes `.first()`; `Open` refuses to pick. **The only front-to-back consumer in the tree** | bg `[4,8,14]` `:183`; per-entity hue `1 => [30,170,255]` `:137`; intensity `value.numer()*220/value.denom()` `:149`; `SupportOnly => 140`; open occlusion amber `[170,105,20]` `:202` |
| **`desktop_receiver.rs`** `:49-52` "Project one receiver-relative exact phase triple into the monitor's local three-primary chart. Subtracting the least component retains signed phase orientation; exact barycentric ratios determine the channels. RGB is the outer transducer's basis, not a universal color ontology."; `:699-702` "**The terminal matrix never supplies this relation.**" | `build_ecology` → `terminal(640,400)` → `assemble_support_presentation_with_cpu` → `receiver_phases` `:112` → CUDA aperture (CPU fallback) → `TerminalTubeAtlas::plan/commit` → `compose_display` `:1369` → `X11Platform::present` + incremental `DisplayPatch` `:1403` | **no z-buffer**: additive accumulation over every supporting tube (`compose_pixel` `:1343`); overlap *marked* `+[35,35,35]` `:1359`, not resolved | `scaled = weight*integer(184)/&total` `:71`, floor `36`; bg `[3,8,12]`; refusal `[18,6,6]` `:1507`; `add_color` saturating `:279` — an instance of the pattern rejected at `2026-07-30…md:19-24` items 1 and 5 |
| **`exact_receiver.rs`** (no doc) | `Triangle`+`Thread` → `PerspectiveRay{focal_distance:1}` `:36` → `receive_face` → `quotient_presentation(…,{80,45}, CpuExecutor::serial())` `:66` → prints counts | none | none |
| **`receiver_graph_analysis.rs`** (no doc) | raster → `ReceiverHolonicComplexLaw` → max `HolonicQuotient` by hull size → `ReceiverGraphAtlas::mount` `:66` → 7 ordered deeds (`Found`/`Refine`/`Dilate`/`Retain`/`Traverse`×2/`Coarsen`) → RON round-trip equality `:160` → 4 TSVs | none; analogue is per-deed `upper_horizon: 0|1` | none |
| **`curved_receiver_phase_atlas.rs`** (no doc) | raster → `ReceiverPhaseAtlasLaw` → `render_phase_atlas` `:156`: per germ clamp by `germ.horizon` `:168`, per channel `crosses_conic` `:263` (sign change of `conic.evaluate` vs right/down neighbour), accumulate `taylor_phase` `:281` (value+gradient+Hessian, exact `Rat`) → 3 PNGs + 4 TSVs | **averaged, not occluded**: `sums[i]/divisor`, `divisor = multiplicity` `:217`; multiplicity exported as its own image | unsupported = source at one third `:212`; supported = 3:1 phase-to-background blend `:309` |
| **`leader_quadrature_figure.rs`** `:1-20` "deposit the lineage as exact rational TSV rows for a figure. **This example adds nothing to the model.** … no decimal anywhere, no float type in this file." | `founded_path.tsv` with `germ_index` "so a renderer can break the piecewise curve at the standing forms rather than joining across a real discontinuity" `:9-11`; `extensions.tsv`; `summary.tsv` | "**The oracle column is the grading.**… that difference is deposited as-is… a first-class return, not an error to hide" `:17-20` | none; the only rendering instruction is the `germ_index` break column |
| **`certified_presentation_workbench.rs`** `:1-28` "present exact mathematics, emit the artifact, then READ IT BACK… **re-opens what it wrote and recomputes the invariants from the file**… An artifact that cannot be read back is not a deposit, it is a leak… Station B… two roots closer together than one cell, so the naive sampled reading… reports **no sign change at all**. The Sturm certificate reports two." | `certify_face` → assert `population_reconciles()` **before drawing** `:188` → `render` under both gauges → assert `structural_residue` equality else `"{}: the palette moved a structural byte"` `:198` → read back `:217`, `:226` → naive vs certified count `:241` | resolvability, not depth: located feature vs `unresolved_feature_count` | **no colour literal in the file** — the palette is delegated to the gauge |
| **`layout_curvature_consumption.rs`** `:1-26` "LAYOUT -> CURVATURE, closed… a nonzero deficit MUST move; a flat layout MUST stay exactly fixed; *'the flow drives every deficit to zero'* is FALSE, shown twice… grade the deficit, not the combinatorial charge." | not a renderer | n/a | none; `show` `:48` under `// Exact display. Nothing here rounds` `:45` |
| **`holonic_eta_ratio_atlas.rs`** `:1-11` "**No known zero ordinate is accepted as input.** …zero-bearing bands are refined through exact boundary winding along the cut, and **all reported coordinates remain rational intervals.**" | `build_atlas`/`write_atlas`/`atlas_summary`; `verify <artifact>` re-reads a deposit | none | none; `.ron` + stdout |

---

# PART 3 — WHAT THE JS LIBRARY MUST MIRROR

All exact-rational (`BigInt` numerator/denominator, normalized). **No float above the codec boundary; exactly one rounding step, at the octet boundary.**

| # | Predicate / algorithm | Rust owner |
|---|---|---|
| 1 | **`cross(a,b)=a.x·b.y−a.y·b.x`** over `Rat` — the single orientation primitive; every orientation, collinearity, area and winding decision is `sign(cross)` | `projection.rs:1163`; `receiver_topology.rs:1061`; `receiver_atlas.rs:673`; `exact_analysis.rs:1825` |
| 2 | **Segment intersection**: `den=d1×d2`; `s=(c−a)×d2/den`, `t=(c−a)×d1/den`; reject outside `[0,1]`; `den==0 && (c−a)×d1==0` ⇒ collinear discriminant; `s`/`t` exactly `0`/`1` ⇒ **endpoint discriminant, not a crossing** | `projection.rs:1154-1207` |
| 3 | **Projection as a rational map** with its own depth per law; isometric irrational (`rational:None`) and **excluded from crossing analysis** | `projection.rs:524-593`, `:1332`, `:1070` |
| 4 | **Inverse projection to the SOURCE parameter** — closed form per law; never interpolate the screen parameter | `projection.rs:1254-1326` |
| 5 | **Over/under**: smaller depth is nearer; equal depth ⇒ refusal; `orientation_sign = sign(over_dir × under_dir)` | `projection.rs:1219-1250` |
| 6 | **Jacobian, pullback Gram `JᵀJ`**, normalized by the gauge's own reference; the hand kept separately as `parity` | `projection.rs:827-928` |
| 7 | **Angular sort by cross product** — half-plane class, then `sign(cross)`, then `norm_squared` | `receiver_topology.rs:1055-1067` |
| 8 | **Face tracing** over darts `2i`/`2i+1`; next dart = predecessor-cyclic of the reverse dart in the target's sorted list | `receiver_topology.rs:956-1032` |
| 9 | **Signed double area (shoelace)** `Σ p_from × p_to`; **outer face ⇔ non-positive** | `receiver_topology.rs:1015-1026` |
| 10 | **Euler check** `F == E − V + 2`, else `NonCellularEmbedding` — a hard refusal | `receiver_topology.rs:637-646` |
| 11 | **Face-dual graph**: one dual edge per diagram edge joining its two dart-faces | `receiver_topology.rs:647-661` |
| 12 | **Pixel aperture addressing**: `x∈[−w/h,w/h]`, `y∈[−1,1]`; bounds `(2c−w)/h…(2(c+1)−w)/h`; **a seam point returns 2 or 4 cells — never pick one by array convention** | `receiver_atlas.rs:65-131` |
| 13 | **Terminal cell bounds** `left=−H/2+c·H/W`, `top=+V/2−r·V/H`; y inverted at the *chart* | `presentation.rs:527-550` |
| 14 | **A raster member is areal, not a point sample** — a primitive contributes iff its support intersects the cell | `presentation.rs:1-7`; `TABLET_THE_REALIZER.md:198` |
| 15 | **Polygon clipping to a cell** (Sutherland–Hodgman over `Rat`) + exact `polygon_area` for `AreaFraction` | `presentation.rs:1259-1338` |
| 16 | **Occlusion**: missing/open-projective depth, or any overlapping `[near,far]` pair ⇒ `Open` with the complete competing population and a named reason. **`Open` is a result — do not invent a winner** | `presentation.rs:1174-1239` |
| 17 | **Depth over a cell** = min/max of the depth law at the clipped polygon's corners; sign-changing homogeneous denominator ⇒ `OpenProjective` | `presentation.rs:1142-1172` |
| 18 | **Feature-counting termination** — Sturm `distinct_root_count`: `0` featureless, `1` locate, `>1` subdivide with the count as certificate, budget exhausted ⇒ `CellObstruction{unresolved_feature_count}`; plus `population_reconciles()` | `certified_face.rs:339-410`, `:277`, `:171` |
| 19 | **Endpoint/midpoint deflation** so a shared-boundary root is located exactly once | `certified_face.rs:245`, `:294`, `:385` |
| 20 | **Level sets / contours by certified sign change** of `reading − level` between consecutive stations; the *bracket* is drawn, never an interpolated point | `model_surface.rs:227-291` |
| 21 | **Winding by sign-of-cross ray crossings**, retrying the ray parameter `0..=32` — the exact replacement for `atan2`/`Arg` | `exact_analysis.rs:1812-1835` |
| 22 | **Cross ratio** `((c−a)(d−b))/((c−b)(d−a))` after a collinearity test by cross product; refuse degenerate quadruples by name | `receiver_atlas.rs:664-694` |
| 23 | **Colour formation**: per-mode superposition first; `P₀=Σ(ReA)²`, `P₁=Σ(ImA)²`, `P₂=Σ(ReA+ImA)²`; `D=κ+ΣP`; `(R,G,B,α)=(P₀/D,P₁/D,P₂/D,ΣP/D)`, `τ=κ/D`; assert `R+G+B=α`, `α+τ=1`; **quantize once, last** | `dimensional_wave.rs:235-267` |
| 24 | **Gauge separation**: geometry owns no colour; the gauge takes the face by *shared reference* and provably cannot alter it | `certified_face.rs:31-38`; `presentation_gauge.rs:6-25` |
| 25 | **The gauge falsifier** — mask `fill=`, `stroke=`, `data-gauge=` values to `GAUGE`; two palettes must give byte-identical residues, and the palette *names must differ in length* | `presentation_gauge.rs:471-497`, `:465` |
| 26 | **Raw rows beside every mark** — each mark carries its exact rational as a data attribute; `format_rat` prints `n` or `n/d`, never a decimal | `presentation_gauge.rs:302`; `certified_face.rs:181` |
| 27 | **Round once**, `⌊(2n+d)/(2d)⌋` on the rational's own numerator/denominator | `presentation_gauge.rs:245-257` |
| 28 | **Non-creation control**: emitted mark count must equal source feature count; no literal layout constant in the owner | `THE_PRESENTATION_ORGAN.md:171-175`; `presentation_gauge.rs:156` |

**Two gaps the corpus leaves open:**

- **Stroke width and mark radius have no doctrinal source.** The only values in the tree are `stroke-width="2"` (`presentation_gauge.rs:291`) and `radius = 2 | 5` (`:301`). The governing sentence is `presentation.rs:703-707`: *"a line has no area until a downstream display gauge declares a stroke law."* A stroke law therefore belongs in the **gauge**, must be declared, and must fall inside the gauge-permutation falsifier's masked region if it is not to carry structure.
- **There is no painter's-algorithm doctrine.** `OcclusionFace::Ordered{front_to_back}` is the only ordering the body will assert; `Open` must be rendered as a visible refusal, never resolved by draw order.
