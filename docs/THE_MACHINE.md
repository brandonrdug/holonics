# The machine: HNN in its geometry and its code

[definition] This is the shared starting point for [Codex](../AGENTS.md) and [Claude](../CLAUDE.md).
It describes the object, the equations its implementation must preserve, and the source owners.
[CONSTRUCTION_STATE](../CONSTRUCTION_STATE.md) records what has returned;
[THE_ROADMAP](plans/THE_ROADMAP.md) orders the next construction. The
[research routes](../research/records/README.md) recover the derivations behind these equations.

## One continuing geometric object

[project-postulate] HNN is being built as one continuing field of interacting Holons: circulating
modes, interlinked toroidal domains, helical passages, active contact faces and participating
receivers. This geometry describes how information is carried, compared, transformed and learned.
A Holon `|H⟩_F` is simultaneously a whole and a part, with incidence K, material Θ, currents Ψ,
interior storage and a declared frame F. Athena is the first intended application; Eros names
its collective formation and composition at every grain. Holonics also develops the broader
mathematical and physical framework these constructions instantiate.

[definition] A nonzero complex channel has amplitude and phase. Independent commuting phases
admit a toroidal chart; coupled channels retain their connection and order defects. Actual linked
or intersecting domains carry the incidence, common cells, field and material that make them
interact. Spatial overlap becomes **contact through that declared interaction law**. Friction,
conservative exchange and heat are particular material terms, not consequences of overlap alone.
A coefficient vector presents a chart of this object; its basis, topology, receiver and transport
remain part of the representation. [Full object contract](HOLON.md).

[definition] A helix combines angular and translational motion, with generator `ξ=(ω,v)` and
initial configuration: `V_ξ(x)=ω×x+v`. Two helical objects retain their own generators, orbit
points, phases and clocks. Their shared contact receiver has a source-derived first and second
variation. The [helical guide](HELICAL_GEOMETRY.md) develops these laws and the independent
circle/line/point limits. A fixed shift or periodic mode is one specialization; an arbitrary
sequence or SSM requires its actual generator and receiver map, not only the label “helix”.

[definition] The elementary binary face is a polarized distinction relative to an axis/frame.
The existing `PhaseCarrier.lean::binaryPhase` and `spinFace` realize two phase sheets separated by a
half-turn; their coupled phase energy has the exact binary Ising restriction. Binary states,
oriented changes and composed paths belong to the construction before a machine-word grouping
or an application alphabet is chosen. [Notation and existing phase owner](HOLONIC_NOTATION.md#arrows-signs-and-turns).

[project-postulate] **Compression is intelligence is navigation:** infer a generating relation
from the available constraints, retain a representation that can execute its consequences, and
navigate/reuse that construction from the current source and receiving situation. The map is
also the material through which later conduct proceeds. This is the existing
[circulating-cartographer account](canon/TABLET_THE_CIRCULATING_CARTOGRAPHER.md), with constructive
[solver inference](../research/records/2026-09-12_SOLVER_INFERENCE_AND_GENERATOR_COMPRESSION_ARE_INTELLIGENCE.md)
and generator/receiver descent as actual implementations. It is not a division into three new
faculties or a criterion postponed until conversational output succeeds.

## The operative equations

[definition] These are compatible parts and declared specializations of the same construction.
The [model formula](HNN_FORMULA.md) supplies the full hypotheses, source maps and variations.

| Operation | Equation and meaning | Starting owners |
|---|---|---|
| Situated transport | `\|H'⟩_(F') = Ĝ_(F'←F)\|H⟩_F`; carry incidence, current, material and unresolved fibre through the declared frame map | `HOLON`; `HolonTensorLens`, `TransportWord`, connection/curvature owners; exact geometry and native constitutive field |
| Elementary interaction | `\|source⟩ → [standing H_int, dynamic H_pert, contact/material law] → ⟨perspective\|`; necks join media and the receiver may participate in their dynamics | `HolonicInteractionExterior`, `HolonicSnellInteraction`, `holonic_interaction`, `holonic_chain`, `neck` |
| Participation and transported current | `T_F[Ψ]=Σ_G a_FG[Ψ] U_(F←G)[Ψ] Ψ_G`, over admitted contacts | `NormalizedExponential`, `HolonicAdjointNormalization`, `NormalizedKernel`; native normalized receiver and constitutive source/current |
| Phase comparison | One unit-phase chart has `s_ij=β cos(2π(q_i−q_j−φ_ij))`, with connection φ; amplitudes and more general pairings extend this chart | `intrinsic_holonic_flow`; `analytic_field`, exact phase/rotation and connection owners |
| Complete variation | `δT=Σ a δ(UΨ)+Σ δa UΨ`; for softmax `δa=(diag(a)−aa*)δs` | Paired tangent/adjoint, normalized section pullback, bilinear source and condition covectors |
| Local learned reaction | `Φ(s,c)=s⊕c⊕(c⊗s)`, `incoming=s+MΦ(s,c)`, `out=S_D(incoming,b)` | `ResidentBilinearFeatures`, `ResidentNormalMaterial`, field reflection/source and `NativeCoupledBody` |
| A local normal law | `H=H₀+Σw f f*`, `B=B₀+Σw t f*`, `W H=B`; priors, weights and receiving constraints are declared | `GeneratorInference`, exact normal/factor owners and resident normal material |
| Generation and reception | `∂_τ x=F_(K,Θ)(x,h,τ)`, then `y=ρ_F b_H(x)`; refinement acts on the joint field and exposes its requested boundary | `Holon.ofEvolution`, `ReceiverPotential`, native field/re-entry and receiving sections |
| Receiver reconstruction | In a declared basis, `A(z)=Σ_i ψ_i φ_i(z)`; text, image, acoustic or internal receivers read the same generated organization through their maps | `Receiver`, `ChangingReceiver`, receiver holarchy, native output/codec boundaries |
| Continuing compression | `D E=ρ`, `E_next T_g=U_g E`; otherwise retain the separating direction, interior or defect | `ReceiverHistoryCompression`, `GeneratorModeQuotient`, quadratic moments, `factor_receiver`, native retained words/modes |
| Recursive geometry | First-arrival populations `A₀=A`, `A_(n+1)=Φ⁻¹(A_n)∖A` retain the source preimages at the receiver; fixed-dimensional nonlinear recurrence can have fractal families | `HolonicRecurrentEcology.FirstArrival`, `FractalPacking`, `ChangingReceiver` and accumulated-defect owners |

[definition] Loss is the declared receiving comparison whose covector is pulled back through
these operations. For prediction probabilities p and target q, cross-entropy's logit gradient
is `p−q`; the descent/update covector is `q−p`. Squared-probability error additionally passes
through the softmax Jacobian. Dissipation is a separate constitutive quantity: for slip Jv and
`D=D*⪰0`, dissipated power is `⟨Jv,DJv⟩`. A learning loss, that power and the stored-energy change
are related only through a specified material/receiver law. The adjoint uses the operands that
produced its forward carriers. [Variation and material](HNN_COMPOSITION.md).

[definition] Exactness keeps the source constraint, branch, period, units and remainder.
Rational/algebraic coordinates carry admitted exact chart values; certified enclosures retain
a phase family and its error bound. **Periodic closure additionally needs a period or
commensurability relation**.
Nonclosing transport remains exact transport. π/e, the golden mode, and the distinct Copson and
Newman boundaries already have source owners in the
[constraint-mode guide](CONSTRAINT_MODES_AND_RECEIVER_FACES.md) and
[mathematics/native synthesis](MATHEMATICS_AND_NATIVE_CONDUCT.md#constraint-defined-modes-and-named-de-bruijn-boundaries).

## How the geometry reaches the implementation

| Source relation | Library or formal owner | Native/application connection |
|---|---|---|
| Toroidal domains, shared cells and phase connection | `analytic_field`, graded/simplicial and connection owners; `HolonicTorusKnots`; [intrinsic field](../research/experiments/intrinsic_holonic_flow/README.md) | `GeometricFieldSpec` validates existing analytic junctions/arcs and compiles their phase transport. `field_session/geometric.rs` executes the legacy geometric chart; tagged `IncidentField` uses the same declared geometry through the full incident body and preserves ordered source contacts. The supplied linked-torus boundary network has a narrower domain than the intrinsic volume/advection reference. |
| Helical pair and contact variation | `relational_geometry::screw`; `Geometry/ScrewGeometry`; `identity_atlas::screw_gram_point` | `HelicalMomentReuse` binds situated finite pair actions and quadrance to the existing observable-moment compression. Lifted phase closure preserves extra turns; an ambient moment fibre retains its physical-configuration restrictions. |
| Normalized receiver and both input covectors | `field/receiver/normalized/phase.rs`, `normal/direct/section/composition.rs`, `resident/section/bilinear_features` | The geometric word calls the existing normalized receiver and pullback, both bilinear covectors, M transpose and fixed-D reflection. It returns through every refinement stage before one staged material update. |
| Constitutive current and storage | `NativeConstitutiveField`, paired junction/source/reflection and normal material | `NativeCoupledBody` owns the operation; fixed-D scattering and its adjoint are existing mechanics. A friction/heat claim additionally supplies that material law. |
| Source, generation, observed comparison and continuation | `holonics-hna/src/native/field_session.rs`, `incident_application/`, `incident_preparation.rs`, `shared.rs`, `geometric.rs`, `alpha/exposure.rs` | Public session and exposure driver, saved comparisons/cursor, Unicode source preparation, E/R/support boundary maps, full incident q/Delta/y/global-D/b return and rest. Recorded context is recovered from the verified prior source prefix across restart. Input provenance remains at the exterior boundary. |
| Structured mathematical field port | `native/mathematical.rs`, `field_session/mathematical_port.rs`, `stream.rs` | One explicit batch creates the existing workshop on the field's resident surface, consumes retained products without host numeric readback, binds declared global complex coordinates, and enters the same incident current. Operator handles end with the batch; the field current and rest remain durable. |
| Native preparation and generator formation | `field_session/incidence.rs` derives `s=x_r`, `c_i=U_(r←i)x_i−x_r` and factors their common restriction; `native_source.rs` attaches the actual field | `body/field/formation.rs` forms compatibility and normal material at the original c; `field_condition_image` carries its full preimage to another source. [Helical generator return](../research/records/2026-09-20_NATIVE_INCIDENCE_FORMS_AND_REUSES_THE_HELICAL_GENERATOR.md). |
| Reuse at future receivers | `ObservableMomentReceiverHistoryCompression`, `ReceiverHistoryCompression`, `internal_mode`, `recurrent_condensation` | Bind a particular field/word/receiver to its encoder, decoder and induced operation; inspect the actual call rather than infer binding from the owner's existence. |
| Physical placement | `hardware_cover`, `section_partition`, mount `section_layout` and `launch_law`; native packet kernels | Read footprints and boundary dependencies determine independent work; checked layout and launch enact it. |

[established-bounded; source-inspected] The legacy geometric session binds complex sections,
analytic incidence and phase comparison to a finite held-boundary refinement word. Geometry,
β, the refinement extent, D and the exterior symbol chart are supplied; M develops through the
whole word's paired return. This preview does not yet commit a continuing global phase field,
learn the receiving geometry or compress the nonlinear word. The
[implemented equation](HNN_FORMULA.md#the-geometric-session-word) and
[campaign record](../research/records/2026-09-20_THE_GEOMETRIC_FIELD_REFINES_AND_RETURNS_ITS_COMPLETE_PAIRED_CURRENT.md)
retain those exact boundaries.
The [field-session source map](plans/THE_ATHENA_ALPHA_CULTIVATES_GENERAL_CONVERSATION_THROUGH_NATIVE_CONTEXTUAL_TRANSPORT.md#field-session-source-map)
and [current position](../CONSTRUCTION_STATE.md) state the unclosed consuming operations.

[established-bounded; source-inspected] The tagged `FieldSourceChart::IncidentField` now binds the
same analytic geometry to the full incident word. It keeps standing q and incident differences
`Delta_i=U_i q_i-q`, derives normalized participation drive y, applies one global D/b, and
relaxes the complete joint boundary under the declared held mask. `incident.rs` retains sparse
incidence columns, declared contacts, producing source/receiver sections and the paired
reverse return; `incident_application/` owns E/R/support, source joins, frozen receiving material,
codec growth and checkpoint/remount. The [September 21 return](../research/records/2026-09-21_THE_INCIDENT_FIELD_JOINS_ITS_GENERATOR_RECEIVER_AND_FROZEN_RETURN.md)
records the implemented scope, focused controls and the still-running full evaluation evidence.
Focused component checks and the full 76,599-site generation/reopen linked response have
succeeded; resumed and uninterrupted checkpoints are byte-identical. Both complete-source
text cases executed, exposed receiving-port/uncertainty defects that were repaired, and still
failed their content requirements in the corrected fixed-port model.

[definition] Co-present regions can execute together when their **complete** read/write,
lineage, obstruction and resource effects commute. Shared immutable inputs with disjoint staged
outputs are one sufficient pattern; overlapping mutable effects require their actual interchange
or reduction law. A launch then assigns the independent work to the hardware's declared capacity.
This applies the [hardware-cover method](HARDWARE_AND_MODALITY_BOUNDARIES.md), not a claim that
co-presence itself implies commutation or that a lane is a Holon.

[established-bounded; source-inspected] **Legacy encoding boundary:** `GeometricRegions`
derives its channel width, unit-current inputs, slot placement and observation targets from a
supplied alphabet. The nibble example therefore shapes the application beyond final text
serialization. Its text decoder selects basis coordinates and assembles bytes; it does not call
the separate helical moment compression. Use the existing
[Holonic Encoding construction](../research/records/2026-09-11_HOLONIC_ENCODING_RETAINS_TRANSFORMATION_GRAIN_ACROSS_MODALITIES.md)
and the [campaign correction](../research/records/2026-09-20_THE_GEOMETRIC_FIELD_REFINES_AND_RETURNS_ITS_COMPLETE_PAIRED_CURRENT.md#correction-the-nibble-control-is-not-holonic-encoding)
when continuing the actual encoder/passage/receiver composition.

[established-bounded; source-inspected] The current incident campaign is specified in the
[executable contract](plans/THE_ATHENA_ALPHA_CULTIVATES_GENERAL_CONVERSATION_THROUGH_NATIVE_CONTEXTUAL_TRANSPORT.md#executable-field-campaign):
participation supplies drive y, the local reaction reads `Phi(q,Delta)`, and one global D/b
scatters the result. Learned source/receiving boundary material connects the exterior codec to
that field without making its alphabet the local current basis. Full joint relaxation,
producing adjoints, residual-certified factor actions, atomic publication and rest are implemented
through the incident owners. The recorded mathematical/code consequence passed; both full-source
conversation cases failed. Their actual outputs and costs are retained in the campaign record.

## Research is construction material

[project-postulate] Hodge's realization and harmonic/cycle laws, RH's source-qualified spectral
placement and threshold laws, Euler/Navier–Stokes transport, Iwasawa levels, and the geometric,
quantum and information constructions are reusable parts of this framework. Apply their maps
and hypotheses to the current object. Their named conjecture endpoints remain separate claims.
The [research routes](../research/records/README.md) connect the records, formal statements and
native consumers so a session starts from that accumulated construction.

[definition] The exact normalized-current/implicit-solve controls in
[connected_holonic_field](../research/experiments/connected_holonic_field/README.md) and the
nonlinear phase/shared-cell construction in
[intrinsic_holonic_flow](../research/experiments/intrinsic_holonic_flow/README.md) have different
scopes. Use the former for its checked differential and solve; use the latter for the stated
geometric/phase recurrence. Their supplied parameters and results do not by themselves constitute
a trained HNN. The task is their applicable composition through the actual model and receiver.
