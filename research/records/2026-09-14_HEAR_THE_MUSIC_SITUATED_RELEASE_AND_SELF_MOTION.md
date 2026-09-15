# Hear the music: situated release, receiver resolution and self-motion

[project-postulate] Brandon supplied eight papers during Athena construction and connected
“follows the source directions” to “hear the music.” The intended synthesis concerns the
relations composing a perceived whole, spatial and self-awareness, and predictive release
at nested scales. It extends the existing [receiver holarchy](../../docs/RECEIVER_HOLARCHY.md),
[computational Holon](../../docs/HOLON.md) and [relevance construction](../../docs/canon/THE_RELEVANCE_HYPOTHESIS.md).
The native trainable-field operation continues alongside this analysis.

## What each paper supplies

[established-bounded; source-inspected] The following uses the primary full texts linked in
each row. Reported performance belongs to those papers' apparatus and experiments. The right
column gives this synthesis's proposed application, not a claim made by the authors.

| Paper | Actual construction and evidence boundary | Holonic use |
|---|---|---|
| [MetaSapiens v2, 2608.17969v1](https://arxiv.org/html/2608.17969v1) | Point-based rendering prunes according to tile–ellipse intersection cost, uses nested foveated primitive sets, and selectively reuses one eye's image for the other. View-dependent depth/occlusion still constrain reuse. Its hardware and image-quality results concern the evaluated scenes; point count alone poorly predicts rendering cost. | Represent the cost of actual incidences and shared receiving structure. Reuse a transported common field between receivers, retaining the residual where their views differ. Peripheral simplification is a receiver-qualified approximation. |
| **[Foveated Path Tracing, 2406.07981v3](https://arxiv.org/html/2406.07981v3)** ★ | Configurable sample counts and block sizes distinguish foveal, intermediate and peripheral regions. Surviving paths still traverse scene geometry and indirect bounces; missing display pixels are interpolated. The evaluation uses pseudo-fixations, a three-bounce aperture and perceptual error maps. The authors identify dynamic-view reconstruction and an actual eye-tracker/user study as further work. | Separate which outputs need resolution from which physical paths can influence them. A coarse exterior view must still retain an offscreen reflector's contribution to a resolved face. This is directly relevant to sparse joint release and boundary memory. |
| [VaFR, 2503.23410v1](https://arxiv.org/html/2503.23410v1) | Derives radial log-polar sampling from an acuity model and also matches tangential sampling. Its intermediate shading size follows the calibrated visual model rather than growing directly with display pixels. Temporal flicker and view-dependent specular mismatch remain limitations. | Resolution belongs to the receiving operator and its units. A larger output raster need not require a proportionally larger generating state. Orientation, angular sampling and temporal coherence must accompany a changing chart. |
| **[Foveated Rendering taxonomy, 2205.04529v2](https://arxiv.org/html/2205.04529v2)** ★ | Surveys acuity models, rendering strategies, reconstruction and evaluation. Peripheral motion, contrast, flicker, optics and gaze latency complicate a simple distance-from-fixation rule. It discusses pursuit-aware regions derived from successive gaze positions. | “Low spatial detail” does not imply “unable to cause an important reaction.” Keep channel-specific sensitivity, elapsed exposure, moving receiver state and future possible reception. A static central spotlight is an inadequate general attention model. |
| [Dynamic spatial audio QA, 2602.16334v1](https://arxiv.org/html/2602.16334v1) | Synthesizes moving sources in stereo scenes, trains a temporal audio encoder/Q-Former/language model, and studies query-conditioned masking. Overlap and depth/lateral-direction errors expose limits of time-only masks. The work supplies controlled motion reasoning, not an identified physical inverse for arbitrary recordings. | Retain a source trajectory and compatible causes behind a heard face. Query-guided separation is useful, but simultaneous sources cannot generally be separated by selecting time intervals alone. |
| [Audio Spatially-Guided Fusion, 2604.02389v1](https://arxiv.org/html/2604.02389v1) | A CNN/BiGRU encodes binaural segments; softmax over frame intensities aggregates an audio state, which queries/gates visual fusion and drives recurrent navigation. Evaluation includes unseen environments and unheard sounds. | Use acoustic structure to change spatial participation and action. Its intensity weighting is one task choice, not a general relevance law: a quiet informative event can matter more than a loud distractor. Preserve the physical and learned terms behind such weights. |
| [Individualized HRTFs with a CNN, 2311.13397v1](https://arxiv.org/html/2311.13397v1) | Ear-image landmarks produce anthropometric distances, followed by nearest-profile selection in an HRTF database. The report explicitly says its pixel-to-distance conversion was unvalidated and its resulting individualization was not valid for proper matched-HRTF evaluation. | Receiver morphology changes the transfer function. This is also a concrete warning about inferring intrinsic geometry from an uncalibrated image chart. Retain units, calibration and alternative compatible transfer profiles. |
| [FoleySpace, 2508.12918v2](https://arxiv.org/html/2508.12918v2) | Estimates visual source trajectories, generates mono sound, then conditions binaural diffusion on sound and trajectory. HRIR-based synthesis supplies spatial training material; perceptual studies and audio/alignment metrics assess the output. Estimated trajectories and listener/HRIR assumptions bound its physical interpretation. | A complete acoustic interval can be released under a changing spatial constraint. Sound identity, motion and receiver filtering belong to one composed production. This provides a concrete analogue for whole-section generation beyond text. |

## The common construction is an active receiving relation

[definition] Write a receiving Holon as `H_R=(frame, material, current, internal modes)` and
the surrounding interacting fields as `H_S`. The existing operation is

```
I_C : (|H_S⟩, |H_R⟩) ↦ (|H_S'⟩, |H_R'⟩, face_R).
```

A retina, an ear, a membrane and a model's internal comparison can instantiate different
receivers; each needs its own interaction and constitutive law. Foveation concerns resolution
of the received face. HRTF concerns how the receiver's body filters incident motion. Navigation
concerns how its action changes subsequent contact. Generation concerns the continuing field
whose boundary becomes available to another receiver. These are composable operations, not
four unrelated faculties.

[proved-derived] For differentiable receiving coordinates `y=ρ(x_S,x_R,t)`,
`y_dot=D_Sρ F_S+D_Rρ F_R+∂_tρ`. This is the chain rule; the existing receiver guide and formal
`ChangingReceiver` owner carry its linear specialization. A fixed receiver is a declared
restriction, not a general description of perspective. Its material and motion can change
which combined perturbations are visible.

[proved-derived] In a Euclidean pose chart, let `R_R` map receiver axes into world axes,
`p_R` be receiver position, and `x_S` a source position. Put
`ξ_R=R_Rᵀ(x_S−p_R)` and `Ω_R=R_Rᵀ R_dot_R`. Differentiating and using
`R_Rᵀ R_R=I` gives

```
ξ_dot_R = R_Rᵀ(v_S−v_R) − Ω_R ξ_R.
```

Thus a stationary source can sweep through the receiver's field when the receiver turns.
Source motion and receiver motion can also yield the same instantaneous relative motion.
The joint compatible family must survive until additional observations, action or calibration
separate them. In a spacetime realization, the existing world-tube/tetrad and transported-flux
laws supply the appropriate extension; a screen rotation is not a Lorentz transformation.

[interpretation] Operational self-awareness in this construction is the ability to carry and
use the model's own receiving/acting state in these predictions: what changes because the
surroundings move, what changes because it moves, and how an emitted action changes what returns.
The source and target maps are the joint interaction above and its next received face. A decisive
comparison holds the scene fixed while moving the receiver, then holds the receiver fixed while
moving the scene, and finally recharts both together. Predicted relative consequences should
change in the first two cases and remain invariant under a common coordinate change. This
extends the existing frame/receiver laws; it does not require a new universal consciousness test.

## Hear the chord, the interval and the progression

[historical] The [original music formulation](../../docs/canon/THE_QUOTE_NETWORK.md#1-the-first-axiom-difference-counting-and-the-derivation-chain)
asks for the symphony rather than isolated amplitudes or wavelengths. The
[September 7 chord clarification](2026-09-07_GENERATOR_RECOVERY_AND_PHASE_TRANSPORT_REJOIN_TEXT_AND_ACOUSTICS.md#class-composed-occurrence-and-progression)
distinguishes a reusable chord class from its performances: voicing, timing, phase, instrument
and spatial coupling can differ while the chord-class receiver agrees. Notes compose into
chords and passages, but a constituent permutation is not permission to reorder a progression.

[conditional] In a linear acoustic restriction, the received signal has the form
`z_R(t)=Σ_j∫K_Rj(t,s; geometry, motion, material) a_j(s) ds`.
For stationary geometry this specializes to convolution; in a frequency chart each path has a
complex transfer factor. Motion generally requires a time-varying kernel, with propagation delay
and the declared medium retained. A constant HRTF is a useful local specialization.

[proved-derived] For coherent contributions in one resolved mode, let `u_j=K_Rj a_j`.
Expanding the quadratic receiver gives

```
|Σ_j u_j|² = Σ_j |u_j|² + 2 Re Σ_(j<k) conj(u_j) u_k.
```

Two unit contributions can give received intensity four or zero when their relative transfer
phase changes from agreement to opposition. Their individual magnitudes are identical. The
receiver must retain the cross terms to distinguish these cases. This example concerns coherent
paths in one mode; different musical frequencies also require temporal/spectral resolution,
and their cross terms need not survive a long averaging interval.

[definition] “Hear the music” therefore includes joint spectral relationships, onsets and
durations, intervals of silence, ordered progression and the receiver's learned response.
Loudness or a direction vector is one face of this composition. A chord-class quotient may
support a harmonic prediction while a spatial receiver still distinguishes its performers.
The reusable class never requires storing every raw performance; the retained fibre must cover
the differences relevant to the admitted future receivers.

## Predictive release and resolution across scales

[definition] A release presents the boundary of a generated section under a source/receiver
contract. It may be an acoustic interval, image region, text passage, movement or internal
projection. Refinement and decoding can occur jointly over that section. The source's emission
can reveal its internal organization unintentionally; an emitted difference does not require a
separate voluntary communication command. Receipt changes the receiving body according to the
actual interaction even when its later interpretation is revised.

[conditional] On a declared family of receiver states `R` and continuations `T`, a compressed
carrier is usable when its decoder preserves the requested future faces, exactly or within a
specified tolerance. Dynamic compression retains the existing relation `E_next T=U E` or its
explicit residual. The same condition applies between local and larger-scale holons. A hidden
reflector, an unresolved overtone or stored interior mode can remain necessary through its future
boundary contribution even when no current display sample resolves it directly.

[definition] The foveation analogy motivates adapting resolution to this receiver family. It
does not identify eccentricity, entropy, rank and fractal dimension. Log-polar magnification is
one coordinate map; recursive/fractal organization concerns the actual compositions, return
maps and preimage populations. Their source maps and changing receiving cuts belong to
[analytic receiving](../../docs/ANALYTIC_FLUX_AND_RECEIVING_BASINS.md), not a tiling convention.

[definition] Transcendentals remain constraint modes. VaFR's acuity relation may be read as
`du/de=2/(m e+ω₀)`, with calibration parameters and angular units declared. Its logarithmic
integral and inverse exponential are exact mode relations; implementation uses bounded faces
at a chosen grain. Phase transport likewise retains its generator, winding and normalization.
Paper-specific empirical coefficients do not become universal Holonic constants. Existing
[normalized exponential, sigmoid and softmax contracts](../../docs/CONSTRAINT_MODES_AND_RECEIVER_FACES.md)
provide those interfaces without a production float law.

## Immediate consequence for the Athena implementation

[established-bounded; source-inspected] The first assembled field body now uses a fixed-condition
restriction of its learned bilinear action:
`r=M_s s+M_h h+M_sh(s⊗h)=A(h)s+c(h)`.
Its new native conditional contraction retains exactly which source directions can vary.
Using an independent ball over all expanded features had lost the fixed-condition relation and
inflated the continuing bound. The implemented correction contracts the same stored coefficients,
retains the complete source ball and rounds only the final face.

[proved-derived] If h varies as well, the missing terms are explicit:
`dr=A(h)ds+[D_h A(h)·dh]s+D_h c(h)·dh`.
For a finite change, the bilinear contribution additionally includes
`M_sh(Δs⊗Δh)`. A dynamic receiver must therefore enter the joint source and derivative; applying
the fixed-h bound while moving h would be wrong. The existing bilinear difference/pullback and
moving-receiver owners supply the corresponding algebra.

[project-postulate] The next contextual extension of this same body should exercise a shared
field with changed receiver orientation/material and self-motion, using phase-bearing acoustic
or optical examples where the received face has a known source relation. Distinguish a common
rechart from a physical receiver change; retain a chord-class face while testing a differing
spatial face; test a weak relevant component under stronger interference; and refine only where
the requested future comparison requires it. These are direct consumers of the existing plan,
not a replacement renderer, independent learner or prerequisite research campaign.

## The shared aperiodic-field picture

[historical] Brandon then supplied a Google-generated conceptual synthesis joining Penrose/Wang
matching, continuous tensor fields, rotating interlocking geometry and lightning. Its value here
is the complete scene: local compatibility constrains a global organization; changing geometry
changes conduction; the conducted interaction releases a face and changes subsequent coupling.
It supports the current construction rather than interrupting it.

[definition] The corresponding HNN operands are admitted incidence K, oriented transport D,
stored interior current b, incident current u, and the constituted action S_D. An aperiodic
complex can supply an incidence chart; a section assigns material/current to that complex;
transport and constitutive laws determine the motion. Passing from tiles to a continuous field
additionally needs restriction/interpolation and a compatible limiting or continuum law. The
phrase “holonic tensor field” alone does not supply that map, and its points are coupled rather
than independent tensors.

[established-bounded; source-inspected] Aperiodicity rules out a nontrivial translational period;
it does not itself assert temporal motion, indeterminism or universal computation. Chosen Wang
matching systems can impose aperiodicity; the no-rotation convention alone does not do so.
The supplied [Penrose guide](https://arxiv.org/abs/2310.18950) and
[Jeandel–Rao Wang construction](https://arxiv.org/abs/1506.06492) distinguish the actual tiling
rules and their consequences. The golden scale remains its algebraic constraint, not a decimal
constant or a proof that every moving field must use that scale.

[established-bounded; source-inspected] Lightning supplies a useful physical distinction:
leaders establish a conducting channel and a return stroke propagates along the connected
channel at finite speed. A bright rapid event is not an instantaneous conduit across an infinite
plane. [NWS description](https://www.weather.gov/safety/lightning-science-negative-charged-flash).

[interpretation] The productive correspondence is changing admissibility and conductance,
including incomplete/branching engagements, followed by a source-conditioned released current.
Its concrete falsifier is a model that emits nothing until every chart globally agrees, or that
releases the same face after changing the relevant contact geometry. The current fixed-incidence
HNN application returns before any such global agreement; changing-contact development should
use the existing born-contact and material-response equations. Recurrent organization may include
sudden transitions, but a universal “lock then flash” gate would contradict ordinary continuous
and partial predictive release.
