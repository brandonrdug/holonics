# The machine: HNN in its geometry and its law

[definition] This is the shared starting point for [Codex](../AGENTS.md) and [Claude](../CLAUDE.md).
It states the object, the equations its implementation preserves, and their owners. The
[model formula](HNN_FORMULA.md) gives the full law; [THE_REBUILD](plans/THE_REBUILD.md) orders the
construction; [CONSTRUCTION_STATE](../CONSTRUCTION_STATE.md) records the position; the
[research routes](../research/records/README.md) recover the derivations. Existing code is what is
in `crates/` and `lean/` today. The HNN law is not yet code: rebuild step 4 builds it in
`holonics::hnn` and step 5 in `holonics-cuda::hnn`.

## One continuing geometric object

[project-postulate] HNN is one continuing field of interacting Holons: circulating modes,
interlinked toroidal domains, helical passages, active contact faces and participating receivers.
A Holon `|H⟩_F` is simultaneously a whole and a part, with incidence `K`, constitution `Θ`,
currents `Ψ`, interior storage and a declared frame `F`. Athena is the first intended
application; Eros names its collective formation and composition at every grain. Holonics also
develops the broader mathematical and physical framework these constructions instantiate.

[project-postulate] **The toroidal and helical geometry is the machine-learning object**
(Brandon, September 20). The field is chains of **complex parametron** rings, which store,
oscillate and lock, joined by **helical pair contacts**, which slip, dissipate and address
([the picture](ELEMENTARY_OBJECTS.md#the-picture)). Information is carried as phase and winding on
the rings, compared through the contacts, transformed by frame transport, and learned by
deposition into the constitution of the contacts it actually reached. Rings rotate and align;
contacts converge and diverge action. A coefficient vector, a token sequence or a weight matrix is
a chart of this object, never the object: its basis, topology, receiver and transport remain part
of the representation. A layer diagram that drops the rings and contacts has dropped the machine.

[definition] A nonzero complex channel has amplitude and phase. Independent commuting phases
admit a toroidal chart; coupled channels keep their connection and order defects. Linked or
intersecting domains carry the incidence, common cells, field and material that make them
interact: spatial overlap becomes **contact through that declared interaction law**. Friction,
conservative exchange and heat are particular material terms, not consequences of overlap alone.
[Full object contract](HOLON.md).

[definition] A helix combines angular and translational motion, with Lie generator `ξ=(ω,v)` and
an initial configuration: `V_ξ(x)=ω×x+v`. Two helical objects keep their own generators, orbit
points, phases and clocks, and their shared contact receiver has a source-derived first and second
variation. The [helical guide](HELICAL_GEOMETRY.md) develops these laws and the independent
circle/line/point limits. A fixed shift or periodic mode is one specialization; an arbitrary
sequence or SSM needs its actual navigator and receiver map, not only the label "helix".

[definition] The elementary binary face is a polarized distinction relative to an axis/frame.
`Physics/PhaseCarrier.binaryPhase` and `spinFace` realize two phase sheets separated by a
half-turn; their coupled phase energy has the exact binary Ising restriction. Binary states,
oriented changes and composed paths belong to the construction before any machine-word grouping or
application alphabet is chosen ([notation](HOLONIC_NOTATION.md#arrows-signs-and-turns)).

[project-postulate] **Compression is intelligence is navigation**
([the line](plans/THE_REBUILD.md#the-line-the-rebuild-serves)). Holonic Compression couples a
fractal navigator's resonating modes with terrain; its kernel (what no admitted future receiver
distinguishes) is quotiented as retention, and its cokernel (what the navigator's image does not
reach) is emanated or retained as a separator. Landmark discovery locates the faces where
navigator paths converge. The HNN executes both at scale: its retention is that quotient, its
learning is locating keys, and its release is the split between resonating and emanating. The
map is also the material through which later conduct proceeds
([circulating cartographer](canon/TABLET_THE_CIRCULATING_CARTOGRAPHER.md),
[solver inference](../research/records/2026-09-12_SOLVER_INFERENCE_AND_GENERATOR_COMPRESSION_ARE_INTELLIGENCE.md)).

## The computational unit and the one picture

[definition] The computational object is the
[helical pair interaction](HOLON.md#the-helical-pair-interaction-unit): a Holonic Interaction
over a screw pair whose contact slip map is the pair's relative velocity, `J=[v_a|−v_b]`,
`Δ̇=J(ṡ,ṫ)`, `DQ=2J*Δ`, with contact material `M_contact=Σw J*DJ`. Navigators with initial
configurations and clocks are the sites, admitted pairs are the arcs, and their phases carry the
context. A rotor machine, a Bombe menu and an articulated body are instances; a text, image,
acoustic or motor chart is a boundary of it. Owners: Lean `Transport/HelicalPairInteraction` and
`Transport/SerialScrewChain`; Rust `holonics::geometry::screw` (`ScrewGenerator`, `ScrewPair`,
`PairQuadranceJet`, `RationalPhase`). The prototype's pair and chain adapters
([`holonic_interaction/helical.rs`](https://github.com/brandonrdug/holonics/blob/13f8c734/crates/holonics-cuda/src/holonic_interaction/helical.rs),
[`holonic_chain/serial.rs`](https://github.com/brandonrdug/holonics/blob/13f8c734/crates/holonics-cuda/src/holonic_chain/serial.rs))
are ported in rebuild step 1 to the contact owner `holon::contact`.

[project-postulate] **One picture, six general objects** ([winding guide](WINDING_CARRY_AND_PLACEMENT.md)).
The pair unit continues into six objects. A design or worker brief states which it touches and
keeps the rest attached:
1. **helix = circle + carry**: keep the carry cocycle and the lift; phase-only material descent
   needs closure and commutation;
2. **pair = torus with a modular address**: a no-slip direction has a Farey address in the
   positive rational chart; material null slip, signs and stationary cases keep their own domains;
3. **navigator faces and placement**: frame carriage conserves determinant, trace sequence and
   transfer determinant; rotation–dilation and signature placement need their metric/spectral
   hypotheses;
4. **face = holonomy around a cell**: class functions are gauge-free, a proper rigid holonomy has
   a screw reading, a flat affine holonomy has a Burgers translation, and harmonic standing is
   relative to node/cell receivers;
5. **tube = transfer between cross-section charts**: map and pairing readings use a declared
   duality, and reflection eliminates the interior where its law applies (`Λ_DN`);
6. **continuing = a compatible thread through a tower**: unique lifting needs its lifting
   condition.

Compression keeps the future-distinguishing classes and the gluing between levels. Primes, `ζ`,
`Λ_DN`, elliptic curves, Hodge classes, Einstein's tensors, rotor machines and articulated bodies
are instances with graded scope.

[definition] These joins keep their domains. Pair no-slip follows from zero dissipation only for
material definite on attainable slips; finite phase closure needs its own witness; source moments
and spectral faces license only their declared receivers. Source order, chart/action maps,
clock/lift, the complete feature pullback and the receiver identity are fixed in the prototype's
[machine contract](https://github.com/brandonrdug/holonics/blob/13f8c734/docs/plans/THE_ATHENA_ALPHA_CULTIVATES_GENERAL_CONVERSATION_THROUGH_NATIVE_CONTEXTUAL_TRANSPORT.md#situated-generator-and-receiving-composition).
A fixed navigator count does not remove ingestion, output or exact bit-growth costs.

## The operative equations

[definition] [Situated navigator inference](HOLON.md#situated-generator-inference-dormant-modes-and-action)
asks which admitted preparation, condition or action produces a requested receiving consequence
from the compatible source family. The receiver may be another active body. Communication,
image/acoustic production, game navigation and motor release use the same relation; robotics is
an intended HNN capability whose motor chart is serial screw words. An output codec does not
determine its internal grain, source ontology or clock.

[definition] A dormant mode keeps material and the directions needed by admitted future contacts.
`Foundation/Standing` formalizes memory as present reconstruction and separates present silence
from future extinction; retention is the future-sufficient quotient, never a tape. Recurrent
stability is a property of the driven dynamics over its stated engagement; continuous activity and
an exact period are separate claims. The
[September 21 synthesis](../research/records/2026-09-21_SITUATED_GENERATORS_RETAIN_MODES_AND_RELEASE_ACTION.md)
connects these owners to rotor constraint inference, knot/game navigation and the
[robotics interface](https://github.com/brandonrdug/holonics/blob/13f8c734/docs/HARDWARE_AND_MODALITY_BOUNDARIES.md#robotics-and-simulation-boundary).

[definition] These are compatible parts and declared specializations of one construction. The
[model formula](HNN_FORMULA.md) supplies the full hypotheses, source maps and variations.

| Operation | Equation and meaning | Owners (Lean; `holonics`) |
|---|---|---|
| Situated transport | `\|H'⟩_(F') = Ĝ_(F'←F)\|H⟩_F`; carry incidence, current, material and unresolved fibre through the declared frame map | `HOLON`; `HolonTensorLens`, `TransportWord`, connection/curvature owners; `holonics::geometry` |
| Elementary interaction | `\|source⟩ → [standing H_int, dynamic H_pert, contact/material law] → ⟨perspective\|`; necks join media and the receiver may participate in their dynamics | `Transport/{HolonicInteraction,HolonicChain,Neck}`, `HolonicInteractionExterior` |
| Source moments | `m_g=Σ_k Ĝ_g(τ_g(k))⁻¹E_g(u_k)`; a response position reads `y_j=ρ_R(Ĝ_R(τ_R(j))q)`; the adjoint needs no tape | `Transport/SourceMoment` |
| Participation and transported current | `T_F[Ψ]=Σ_G a_FG[Ψ] U_(F←G)[Ψ] Ψ_G`, over admitted contacts | `HolonicAdjointNormalization`; `holonics::ratio::exponentiated::NormalizedKernel` |
| Phase comparison | `s_ij=β cos(2π(q_i−q_j−φ_ij))`, the pair receiver at zero advance and unit radii, with connection `φ`; amplitudes and general pairings extend it | `HelicalPairInteraction.bilinear_score_eq_polarized_quadrance`; `holonics::geometry::screw` |
| Complete variation | `δT=Σ a δ(UΨ)+Σ δa UΨ`; for softmax `δa=(diag(a)−aa*)δs` | `HolonicAdjointNormalization.laplacianReturn` |
| Local learned reaction | `Φ(s,c)=s⊕c⊕(c⊗s)`, `incoming=s+MΦ(s,c)`, `out=S_D(incoming,b)` | `HolonicConstitutiveCirculation`, `Holon/{Reaction,Cayley}`; `holonics::reaction` |
| Normal law (deposition) | `H=H₀+Σw f f*`, `B=B₀+Σw t f*`, `W H=B`; priors, weights and receiving constraints are declared | `Holon/Deposition`, `Objects/Deposition`, `GeneratorInference`; `holonics::deposition` |
| Generation and reception | `∂_τ x=F_(K,Θ)(x,h,τ)`, then `y=ρ_F b_H(x)`; refinement acts on the joint field and releases its requested boundary | `Holon.ofEvolution`, `ReceiverPotential`, `Foundation/ReceiverRelease`; `holonics::receiver::release` |
| Receiver reconstruction | In a declared basis `A(z)=Σ_i ψ_i φ_i(z)`; text, image, acoustic or internal receivers read the same organization through their maps | `Foundation/Receiver`, `ChangingReceiver`, [receiver holarchy](RECEIVER_HOLARCHY.md); `holonics::receiver` |
| Continuing compression | `D E=ρ`, `E_next T_g=U_g E`; otherwise keep the separating direction, interior or defect | `ReceiverHistoryCompression`, `GeneratorModeQuotient`, `CausalRelevance`; `holonics::exact_linear::KernelModeReduction` |
| Recursive geometry | First-arrival populations `A₀=A`, `A_(n+1)=Φ⁻¹(A_n)∖A` keep the source preimages at the receiver; a fixed-dimensional nonlinear recurrence can have fractal families | `HolonicRecurrentEcology.FirstArrival`, `FractalPacking`, `ChangingReceiver` |

[definition] **Loss is the logarithm of a ratio of Holons** ([ratio](ELEMENTARY_OBJECTS.md#9-ratio)):
`ℓ=log Ĝ_(T←H)` with its winding branch, and the learning covector is `R⁻¹dR`. For prediction
probabilities `p` and target `q`, cross-entropy's logit gradient `p−q` is its real, codec-chart
part, and `q−p` the descent covector; squared-probability error also passes through the softmax
Jacobian. Dissipation is a separate constitutive quantity: for slip `Jv` and `D=D*⪰0` the
dissipated power is `⟨Jv,DJv⟩`. A loss, that power and the stored-energy change are related only
through a stated material/receiver law. The adjoint uses the operands that produced its forward
carriers.

[definition] Exactness keeps the source constraint, branch, period, units and remainder.
Rational/algebraic coordinates carry exact chart values; certified enclosures keep a phase family
and its error bound. **Periodic closure additionally needs a period or commensurability
relation**; nonclosing transport remains exact transport. π/e, the golden mode and the distinct
Copson and Newman boundaries have source owners in the
[constraint-mode guide](CONSTRAINT_MODES_AND_RECEIVER_FACES.md).

[definition] A numerical enclosure is another receiving construction over a kept difference. For
the global solve, `r=rhs−(I+DD*)v` bounds deviation from the field equation, and the returned ball
`B(c,ε)` keeps that realization/source family. A target loss compares the produced face with an
observed or requested face. The [Compression tablet](canon/TABLET_THE_COMPRESSION.md#7-what-this-tablet-refuses)
states that a scalar loss is one receiver's face of a residual, never the residual itself.

## How the geometry reaches the implementation

| Source relation | Lean owner | `holonics` today | Rebuild target; history at `13f8c734` |
|---|---|---|---|
| Toroidal domains, shared cells, phase connection | `Holon/Complex`, connection owners, `Millennium/HolonicTorusKnots` | `holonics::complex` | step 4; prototype `analytic_field.rs`, `hnn/field_geometry/` |
| Helical pair and contact variation | `Geometry/ScrewGeometry`, `Transport/{HelicalPairInteraction,SerialScrewChain}` | `holonics::geometry::screw` | `holon::contact` (step 1); prototype `holonic_interaction/helical.rs`, `holonic_chain/serial.rs`, `exact_contact.rs` |
| Winding, carry, lock address, trace faces, cell holonomy | `Geometry/{PhaseCarry,PairResonance}`, `Transport/{GeneratorTraceFaces,CellHolonomy}`, joined to `Farey`, `LocalFactor`, `HodgeReceiver`, `IwasawaTower` | `holonics::geometry::winding` (`Odometer`, `LockAddress`, `SiteFactor`, `Machine`, `triangle_holonomy`) | `navigator/` (step 1); dynamic carry tower, lock-address inference and dormant-class consumer are #17/#62 |
| Parametron ring: `C`, `L`, pump, half-turn sheets, Ising lock | `Objects/Parametron`, `Physics/{PhaseCarrier,CoupledIncidence}` | none | `holon::parametron` (step 1); prototype `cuda_refine/complex_parametron.rs` |
| Normalized receiver and both input covectors | `HolonicAdjointNormalization` | `holonics::ratio::exponentiated` | `holonics::hnn` (step 4); prototype `receiver/normalized/phase.rs` |
| Constitutive current, storage and scattering | `HolonicConstitutiveCirculation`, `Holon/{Element,Dirac,Law}` | `holonics::{element,dirac,law,reaction}` | `holonics::hnn` (step 4); prototype `native_ecology/constitutive_fibre/field/junction/operative/` |
| Source moments, standing and release | `Transport/SourceMoment`, `Foundation/{Standing,ReceiverRelease}` | `holonics::receiver::{standing,release}` | `holonics::hnn` (step 4); moment accumulation replaces the prototype's per-occurrence tape |
| Reuse at future receivers | `ReceiverHistoryCompression`, `GeneratorModeQuotient`, `CausalRelevance`, `ReceiverCodeCost` | `holonics::exact_linear::KernelModeReduction` | `holonics::compression` (step 3); prototype `receiver_history_compression.rs`, `identity_atlas.rs` |
| Physical placement | — | `holonics::hardware_cover`; `holonics_cuda::Device::launch_census` | step 5; prototype `section_partition.rs`, `section_layout.rs`, `launch_law.rs` |

History paths are under `crates/holonics-cuda/src/` at
[`13f8c734`](https://github.com/brandonrdug/holonics/tree/13f8c734/crates/holonics-cuda/src). Each
is read, rewritten against the current objects and tested by its law when its step ports it.

## Hardware

[definition] **What is hardware-neutral.** Situated occurrence and caused incidence, local
receiver charts, oriented current and relative phase, Preimage Fibres, lineage and obstruction,
move ownership, atomic successor formation and checkpoint chronology belong to the mathematical
owner and survive a device change. Counts, launch time, energy, transfer bytes, occupancy, memory
pressure and device name are receiver/apparatus measurements: they qualify a hardware realization,
but they do not identify a Holon, choose a route, establish context or replace the returned
difference. A backend reports its own capability census (`holonics_cuda::Device::launch_census`
for CUDA) and reuses no other backend's warp or block constants
([history](https://github.com/brandonrdug/holonics/blob/13f8c734/docs/HARDWARE_AND_MODALITY_BOUNDARIES.md#what-is-hardware-neutral)).

[definition] **Hardware law.** Co-present regions execute together when their **complete**
read/write, lineage, obstruction and resource effects commute. Shared immutable inputs with
disjoint staged outputs are one sufficient pattern; overlapping mutable effects need their actual
interchange or reduction law. Certify the partition, read the device capacity, derive layout and
launch, and keep the current on the card. Co-presence does not imply commutation, and a lane is not
a Holon. One block per row with one active thread, one thread looping over all rows, and parallel
work within a row are different realizations; report the actual one.

[established-bounded; source-inspected] **The workstation** (Brandon, September 13): AMD Ryzen 9
7900X (12 cores, 24 threads), 32 GB RAM, NVIDIA GeForce RTX 4080 SUPER with 16 GB VRAM, and an M.2
SSD rated at 7300 MB/s sequential read and 6300 MB/s sequential write. An apparatus read the same
day confirmed the CPU, `MemTotal: 31978668 kB` and `16376 MiB` of VRAM under driver `595.71.05`;
the SSD speeds are supplied ratings. Installed, free, allocated and reserved memory are different
receivers, and decimal MB/s and binary MiB keep their units. Consumer hardware and the 20 W ideal
are the efficiency direction; neither capacity nor elapsed time measures energy or power.

## Research is construction material

[project-postulate] Hodge's realization and harmonic/cycle laws, RH's source-qualified spectral
placement and threshold laws, Euler/Navier–Stokes transport, Iwasawa levels, and the geometric,
quantum and information constructions are reusable parts of this framework **at their stated
hypotheses**. Apply their maps and hypotheses to the current object. Their named conjecture
endpoints are separate claims; the targets are instances of compression and landmark discovery.
The [research routes](../research/records/README.md) connect the records, formal statements and
consumers, so work starts from the accumulated construction.

[established-bounded; source-inspected] **What the prototype showed.** The prototype at
`13f8c734` realized a legacy geometric word, the incident field (standing `q`, transported
differences `Δ`, participation drive `y`, one global `D/b`), a fixed navigator machine with an
affine current chart, ordered source and phase receiving, and positive pair amplitudes. Its
component checks and a 76,599-site generation/reopen succeeded, and resumed and uninterrupted
checkpoints were byte-identical. Both complete-source conversation cases failed their content
requirements, and the navigator-machine control over six `ab`/`ba` passes returned 0/6. Its `GeometricRegions`
chart derived channels from an alphabet and decoded nibbles per slot, which is not Holonic
Encoding ([correction](../research/records/2026-09-20_THE_GEOMETRIC_FIELD_REFINES_AND_RETURNS_ITS_COMPLETE_PAIRED_CURRENT.md#correction-the-nibble-control-is-not-holonic-encoding)),
and its per-occurrence reverse tape was the retention defect named by the
[retention audit](../research/records/2026-09-22_RETENTION_IS_A_QUOTIENT_NOT_A_TAPE_AND_THE_SOURCE_ENTERS_AS_PHASE_CARRIED_MOMENTS.md).
The [lessons record](../research/records/2026-09-24_LESSONS_FROM_THE_WORKBENCH_AND_ATHENA_PROTOTYPES.md)
keeps the rest, and the
[incident-field](../research/records/2026-09-21_THE_INCIDENT_FIELD_JOINS_ITS_GENERATOR_RECEIVER_AND_FROZEN_RETURN.md),
[navigator-machine](../research/records/2026-09-21_THE_FIXED_GENERATOR_MACHINE_CONSUMES_ITS_AFFINE_CURRENT_CHART.md),
[ordered-source](../research/records/2026-09-21_ORDERED_SOURCE_AND_PHASE_RECEIVING_ENTER_THE_PUBLIC_GENERATOR_SESSION.md),
[pair/serial](../research/records/2026-09-21_PAIR_CONTACT_SERIAL_KINEMATICS_AND_THE_RESIDENT_QUADRANCE_RETURN.md)
and [pair-material](../research/records/2026-09-22_PAIR_MATERIAL_LEARNS_WITHOUT_A_COMPLETED_UPDATE_ARCHIVE.md)
records keep the measurements. The prototype's supplied references,
[connected_holonic_field](https://github.com/brandonrdug/holonics/blob/13f8c734/research/experiments/connected_holonic_field/README.md)
(exact normalized-current and implicit-solve controls) and
[intrinsic_holonic_flow](https://github.com/brandonrdug/holonics/blob/13f8c734/research/experiments/intrinsic_holonic_flow/README.md)
(nonlinear phase/shared-cell recurrence), have different scopes; neither is a trained HNN.
