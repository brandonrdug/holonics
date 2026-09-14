# Generation refines fields and the Holon has computational faces

[project-postulate] Brandon's September 14 request makes generation explicit as nested
field refinement and boundary activity, including involuntary social cues. Image and acoustic
diffusion are essential comparisons; output-token iteration must not define the architecture.
He requests recovery of the laboratory crow/radiation account, an audit of Holons as computational
objects, a precise elementary specification and a reusable illustrated synopsis reflecting the
actual formal/software design. This extends the completed model-formula work at `cd9dd674`.

## Recovered research and source scope

[established-bounded; source-inspected] The laboratory recovery followed:

- `src/soma/RESEARCH/2026-07-21_THE_INTELLIGENCE_IS_THE_COMMUNICATING_FIELD_THE_OBSERVER_ENTERS_THE_SUCCESSOR.md`,
  especially participating observation, world-mediated communication and the crow/flock section.
  It already describes experienced birds' scanning, calls and movement as stimuli for others,
  without copying a private image or preserving original constituents.
- `2026-07-13_THE_PHOTOGRAPH_POINTS_INTO_LANGUAGE.md`: visual-to-caption pointing as production.
  Its historical caption apparatus and capability claims are not adopted as the current model.
- `src/holobrochos/THEORY/18_THE_HOURGLASS.md`: concentrated action releasing through a boundary
  into a new medium, illustrated by the whip and acoustic cone. The old byte tower and claim
  that a heard feedback completes every thought are superseded by current release/ownership scope.
- `src/labyrinth/physics/P18-stars-watch-us.md`: exterior radiation as information about an
  inaccessible interior. Historical statements identifying stars with minds are not physical
  results of this audit. Existing horizon restrictions still determine available signals.
- Current `Holon`, `Receiver`, `CausalNaturalHolon`, `HolonTensorLens`, the relevance hypothesis,
  the HNN formula, native carrier/field/session source and both information-chemistry Typst editions.

[established-bounded; source-inspected] Cornell, Marzluff and Pecoraro's
[crow experiment](https://faculty.washington.edu/wirsinga/Cornell2011.pdf) distinguishes
individual and social learning of dangerous human faces. Observed mobbing/scolding and young
birds' later independent response support the world-mediated account. Gaze alone as sufficient
teaching is not established by that study. The model correspondence uses an actual cue and
receiving response, without a semantic intent flag or access to another bird's private state.

## Diffusion and generation

[established-bounded; source-inspected] The requested
[noise-control review](https://arxiv.org/html/2502.04669v1) concerns noise schedules and
diffusion-model training/synthesis. Its Eq. 3 repeats the one-step kernel where its prose calls
for a marginal expression. Eq. 5 uses `sqrt(1-beta)` for the noise amplitude despite Eq. 1's
variance beta; the corresponding amplitude is `sqrt(beta)`. These do not change the useful
question about structured generation, but the formulas should not be imported unchanged.

[established-bounded; source-inspected] The primary comparison used
[DDPM](https://arxiv.org/html/2006.11239v2),
[DiffWave](https://arxiv.org/html/2009.09761v3), and
[score-based SDEs](https://arxiv.org/html/2011.13456v2), including their architecture and
probability-flow sections. DDPM uses a U-Net-based noise predictor. DiffWave uses bidirectional
dilated convolutions and refines an entire waveform without autoregressive sample generation.
The number of refinements and number of output coordinates are different quantities.

[conditional] The probability-flow ODE gives the same one-time marginal densities as its
associated SDE under the exact-score and regularity assumptions, not the same paths. Sampling
an initial latent and evolving it deterministically is one generative chart. Native HNN uses
its own constituted operators and exact/enclosed representations; neither Gaussian noise nor
a sequential token decoder is imposed as a universal internal mechanism.

[definition] The formula now states prepared field, constituted refinement, generated boundary
and coupling to another region explicitly. The other region may be internal to the same
larger Holon. Unknown, noisy and zero fields are distinct. Stable heat smoothing is not by
itself learned synthesis. A cue can recruit modes and prompt further reconstruction without
requiring an archived image, a singleton preimage or the recovery of every historical detail.

## Holon audit and repairs

[established-bounded; source-inspected] A bounded read-only Luna audit inspected native Rust
carriers; root inspected the cited owners and integrated the findings against the formal source.
The generic `Face`, relation, chain and membrane types are building blocks. Resident sections,
constitutive fibres, native current boundaries/frames/incidence and operative fields jointly
realize structured computational objects. Their existence does not mean every bare packet
contains a complete Holon. The numerical view and its owning equation must be distinguished.

[established-bounded; source-inspected] `NativeSession` exposes the narrower phase ecology.
It omits some internal incidence/rechart structure from wire results; the engine still owns
it. This is an exterior projection, not evidence that a second receipt API or universal Holon
wrapper is required for generation. The whole-field model must consume the richer existing
owner directly. The separate native draft was not modified by this turn.

[established-bounded; source-inspected] `Face::taken` accepts an arbitrary pair and proves no
projection relationship. `map_scalar` can be noninjective; retaining arbitrary relation data
does not make it reversible. The source comments previously claimed otherwise and now state
the actual contract. The repair also removes the unqualified implication that every bare
storage offset must duplicate a complete relation. This is a documentation correction with
no Rust runtime behavior change.

[proved-derived; formal-checked] `Foundation/Holon.lean` now contains:

- `ofEvolution`: a generated section with the prepared seed as occurrence population;
- `mapReceiver`: another reading with the same occurrence and interfaces;
- `ofEvolution_receive_eq_encoded`: full and encoded generation agree when the evolution
  and receiver squares commute;
- `ofEvolutionCompOccurrenceEquiv`: joining two deterministic refinements gives a population
  equivalent to the original seeds, without enumerating a trajectory.

[established-bounded; source-inspected] The existing `HolonTensorLens` already defined
heterogeneous tensor faces and their application to a Holon. It now reuses `mapReceiver`.
Its comment explicitly admits an internal receiver boundary; tensors are not restricted to
exterior codecs. General heterogeneous axis reindexing and the more specific homogeneous
slot-naturality theorem retain their original scopes.

## Maintained specification and presentation

[project-postulate] Brandon's two subsequent corrections require the established Information
Chemistry tori, curved fields and geometric styling, and high-level Holonic/Dirac tensor
operations rather than unfolding the four-map foundation. The first flowchart-only draft is
retained privately as an intermediate and is superseded by the geometric edition.

[established-bounded; source-inspected] The notation recovery read the predecessor
`src/docs/HOLONIC_NOTATION.md`, current `docs/canon/TABLET_THE_OPERATIONS.md`, the corpus's
`lib/dirac.typ` and `bra-receiver-ket-construction.typ`. The current operational convention
distinguishes construction ket, receiver bra, measured bracket, transport operator and
receive/emit outer product. The Holonic entity mark and frame notation are used without
restoring historical full-infall archives, hash identity or an exclusive three-operation tower.

[definition] The specification now leads with |H⟩_F, tensor coefficients, operator tensor
signatures and encapsulated interactions. Application, composition, contraction, tensor
interaction, reflection, adjoint and whole-field generation precede the span explanation.
Actual exact/native methods are mapped to this notation. An interaction vertex carries its
tensor; joined lines contract compatible port axes.

[established-bounded; source-inspected] `exact_linear/bilinear.rs` already implements the
tensor interaction, shared product, receiver composition and further fixed-port interaction.
Its module documentation now presents those operations together. No additional fitter
helper or receipt family was added as a substitute for the requested abstraction.

[definition] `docs/HOLON.md` is the elementary computational specification and operator
synopsis. The HNN formula now includes generation, latent/noise/partial-field distinctions
and nested boundary coupling. The blueprint and roadmap incorporate them into the existing
model assignment. The actual implementation of that full model is not claimed complete.

[definition] The ten-page `elementary-holon-generation` synopsis renders those contracts.
`research/papers/source/holonics/computational-holon.typ` exports reusable equations and diagram
functions; the paper's `main.typ` composes them. The final presentation reuses the original
torus/receiver, contact, knot-wave, woven-field and lobe figures with high-level Dirac notation
and an interaction vertex. Two additional plates give a recursive IFS and analytic/operator
calculus. These are source constructions, not fabricated outputs of a newly trained native model. The existing broader synopsis and
historical paper editions remain available and unchanged.

## Verification

[established-bounded; process-audit] The changed Holon target and the final
`ElementaryHolonics.Framework.Core` consumer passed `tools/lean_check.sh`. The two new
generation proofs report no axioms. Core's final build completed with 3154 build jobs,
including reused dependencies; that count is not a capability measure.

[established-bounded; process-audit] Typst compiled the final ten-page PDF. All ten final
pages were rasterized with Poppler and visually inspected. The first render's clipped span
diagram and notation/spacing issues were corrected. The subsequent geometric edition follows
the original 320 mm × 210 mm receiver-edition style; its final ten pages were re-inspected.
The PDF is an illustrated design return, not native performance evidence. Rust changes are
comments only; no unchanged CUDA campaign was rerun. `git diff --check` supplies the final
whitespace check. Local formal logs and page renders are in
`.local/artifacts/2026-09-14-generation-holon/`.
