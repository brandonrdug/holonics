# The machine: HNN in its geometry and its law

[definition] This is the shared starting point for [Codex](../AGENTS.md) and [Claude](../CLAUDE.md).
It states the object, the equations its implementation preserves, and their owners. The
[model formula](HNN_FORMULA.md) gives the full law; [THE_REBUILD](plans/THE_REBUILD.md) orders the
construction; [CONSTRUCTION_STATE](../CONSTRUCTION_STATE.md) records the position; the
[research routes](../research/records/README.md) recover the derivations. Existing code is what is
in `crates/` and `lean/` today. The host `holonics::hnn` and resident `holonics-cuda::hnn` implement campaigns 1–2.
The landmark tree supplies most of the measured compression. The loaded resonator (`hnn::ring`)
connects the resonator's returned wave and adjoint to the field; campaigns 3–5 supply release
through modes, the motor chart, Holonic Encoding, context and joint prediction.
[CONSTRUCTION_STATE](../CONSTRUCTION_STATE.md) distinguishes measured results from these remaining consumers.

## The top: a Holarchy and its aeons

[definition; Brandon, September 27: "Aeons and Holarchies are at the top"; the construction
`agent-inferred`, [the unity audit](../research/records/2026-09-27_THE_HOLARCHY_AND_ITS_AEONS_ARE_THE_TOP_THE_DECISIONS_DISSOLVE_INTO_THEIR_OWNERS_AND_LEARNING_IS_PROTOTYPED_WHERE_A_HOLARCHY_MADE_THE_TERRAIN.md#2-the-unification)]
**The HNN is a Holarchy, and its passage is an aeon.**
- **The Holarchy.** Its closing rotor rings and its helical pair contacts are Holons, each
  certified on its own, joined at ports by `interconnect`: `hnn::Field::holarchy` returns the
  `holarchy::Holarchy`, and the mount certifies that it glues or refuses with its typed gluing
  defect. The receiving parametron's storage is the context tree (`compression::landmark::context`,
  the shift navigator's landmarks), held in `Θ` at the receiving locus. `hnn::Field` is the
  Holarchy's declaration, a chart of it.
- **The aeon.** Its passage is an aeon on the Holarchy's parametric orientation (the lift of the
  rings' joint clock torus): a receiving window is an epoch at the receiver's section; a pump
  period or a clock closure is a cycle; the aeon boundary is the collapse; and the first law over
  the aeon is `aeon::EnclosedLedger`. `hnn::Reference::expose` is a cut's passage through the
  resident's aeons, one closed at each joint-clock carry-out.
- **What the code joins** (read from source at this commit): the resident's aeon is an
  `aeon::Aeon` on the parametric orientation from its opening lift point to the joint clock's
  carry-out; each ring's epochs are the flux through its own ring section; the carry-out is an
  `aeon::Cycle` of the last ring's clock when that ring opened on its section; the boundary runs
  the collapse; and the resident carries the `EnclosedLedger`.
- [open] Three joins are not yet in the code: the receiving tree is storage read by the receiving
  face, not a Holon joined at ports in `Field::holarchy`; a receiving window is a step of the
  exposure's loop, not an `aeon::Epochs` reading at the receiver's section; and a pump's period is
  the mode quotient's lift period (`hnn::modes`), not an `aeon::Cycle`. The unity audit's order,
  item 2, owns them (#63).

## One continuing geometric object

[project-postulate] HNN is one continuing field of interacting Holons: circulating modes,
interlinked toroidal domains, helical passages, active contact faces and participating receivers.
A Holon `|H⟩_F`, a motion admitted by its law
([the Holon as one object](ELEMENTARY_OBJECTS.md#the-holon-as-one-object)), is simultaneously a
whole and a part, with incidence `K`, constitution `Θ`, currents `Ψ`, interior storage and a
declared frame `F`. Athena is the first intended
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

[project-postulate; agent-inferred at the consumer] The egg discussion's interior↔exterior
relation enters the machine through the loaded storage port: the ring receives a wave and its
returned wave changes a later receiving face. The corresponding covector reaches its material.
A receiver's current nullity is not future extinction; `Holarchy/Hearing` supplies the distinction
that campaign 3's mode retention must consume. The [audited egg/shadow record](../research/records/2026-09-26_THE_SHADOW_IS_THE_RECEIVERS_KERNEL_AND_THE_EGG_IS_TWO_RINGS_IN_RELATIVE_MOTION.md)
keeps the curve, the receiver maps still owed, and the invariant rate-form reading. The loaded
resonator (`hnn::ring`) implements the port connection; broader mode/shape and
participating-receiver consumers retain their campaign scopes. Its gains test one declared
material family: they do not replace the egg's geometry or prove that four coordinates express
every useful interior, and the finite classes come from the admitted future faces and their
grain. Integrating and differentiating directions are read through the actual rate form
`A*G + GA + Ġ` with its metric, clock and source; a rechart transports that form by congruence,
and an egg displacement is assigned no Lorentz law without its receiver/transport map. In
campaigns 3 and 5 controlled release is received action: the mode reaches another Holon's
boundary through the declared tube, and the encoding/receiver square closes or returns its
separating difference, with the Hodge, complex-fluid and spectral target laws attached at those
operations.

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
were port sources for the current contact owner `holon::contact`.

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
| Local learned reaction | `Φ(s,c)=s⊕c⊕(c⊗s)`, `incoming=s+MΦ(s,c)`, `out=S_D(incoming,b)` | `HolonicConstitutiveCirculation`, `Holon/{Reaction,Cayley}`; `holonics::holon::reaction` |
| Normal law (deposition) | `H=H₀+Σw f f*`, `B=B₀+Σw t f*`, `W H=B`; priors, weights and receiving constraints are declared | `Holon/Deposition`, `Objects/Deposition`, `NavigatorInference`; `holonics::holon::deposition` |
| Generation and reception | `∂_τ x=F_(K,Θ)(x,h,τ)`, then `y=ρ_F b_H(x)`; refinement acts on the joint field and releases its requested boundary | `Holon.ofEvolution`, `ReceiverPotential`, `Foundation/ReceiverRelease`; `holonics::receiver::release` |
| Receiver reconstruction | In a declared basis `A(z)=Σ_i ψ_i φ_i(z)`; text, image, acoustic or internal receivers read the same organization through their maps | `Foundation/Receiver`, `ChangingReceiver`, [receiver holarchy](RECEIVER_HOLARCHY.md); `holonics::receiver` |
| Continuing compression | `D E=ρ`, `E_next T_g=U_g E`; otherwise keep the separating direction, interior or defect | `ReceiverHistoryCompression`, `NavigatorModeQuotient`, `CausalRelevance`; history [`KernelModeReduction`](https://github.com/brandonrdug/holonics/blob/551d6c5d/crates/holonics/src/exact_linear/kernel_modes.rs) |
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

[definition] A numerical enclosure is another receiving construction over a kept difference.
- **The residual.** For a solve, the residual of that solve's own system, `r = rhs − A v`, bounds
  deviation from its equation. The returned ball `B(c,ε)` keeps that realization/source family.
- **The HNN's solves** are local only: a junction's admittance sum, an element's `I − ½K` and a
  contact's `M_a`.
- **No global solve.** The prototype's global `r=rhs−(I+DD*)v` is history at `13f8c734`. A change
  moves one contact per tick, inside a causal cone of one hop per tick; the connection heat
  equation is only the continuum limit ([THE_REBUILD](plans/THE_REBUILD.md#the-law-of-one-passage-a-change-on-a-medium-81-82), "The causal cone"). Brandon's
  rulings: September 1, "The way that 'weights' … are updated is a propagating local thing";
  September 11, "their states are determined by particles around them and propagating waves, not
  by spooky action at a distance"; September 22, "my brain's regions … are only affected by the
  propagating action that would reach the independent region". The tick's form is agent-inferred
  from the light record's §8.1.
- **The loss.** A target loss compares the produced face with an observed or requested face. The
  [Compression tablet](canon/TABLET_THE_COMPRESSION.md#7-what-this-tablet-refuses) states that a
  scalar loss is one receiver's face of a residual, never the residual itself.

## How the geometry reaches the implementation

| Source relation | Lean owner | Current consumer | Remaining construction / history source |
|---|---|---|---|
| Rings, contacts, phase connection | `Holon/Complex`, `HNN/Word` | `geometry::complex`, `hnn::field`, `hnn::word` | Richer field declarations; prototype `analytic_field.rs`, `hnn/field_geometry/` |
| Helical pair and contact variation | `Transport/{HelicalPairInteraction,SerialScrewChain}`, `HNN/Contact` | `geometry::screw`, `holon::contact`, `hnn::contact` | Motor consumer (#27); prototype pair and chain adapters |
| Winding, carry, lock, trace faces, cell holonomy | `Geometry/{PhaseCarry,PairResonance}`, `Transport/{NavigatorTraceFaces,CellHolonomy}` | `geometry::winding::Odometer`, `navigator::{address,trace}`, `hnn::contact` | Carry tower and continuous-key joins (#62) |
| Parametron storage, pump, sheets and lock | `Objects/Parametron`, `HNN/Ring` | `holon::parametron`, `hnn::ring`, CUDA resonator kernels | Loaded forward/adjoint connection (`hnn::ring`, built); pump/Floquet theorem (#62) |
| Receiving comparison and covectors | `Objects/Ratio`, `HNN/Ratio`, `Compression/Landmark/Context/{Tree,Compaction,Standing,Epoch}` | `hnn::{ratio,receiving}`, `compression::landmark::context`, CUDA compacted tree | Composed lattice drift and the log squaring invariant (#62) |
| Constitutive current, storage and scattering | `Holon/{Element,Dirac,Law}`, `HNN/{Word,Propagation}` | `holon::{element,dirac,law,reaction}`, `hnn::{propagation,word}` | Complete word sensitivity and concrete diamond bridge (#62) |
| Source moments, retention and release | `Transport/SourceMoment`, `HNN/{Moment,Retention}` | `hnn::{moment,pending,retention}`, `receiver::{standing,release}` | Mode release, founding and moment quotient (campaign 3) |
| Reuse at future receivers | `Compression`, `Foundation/{ReceiverHistoryCompression,NavigatorModeQuotient,CausalRelevance}` | `compression`, structural `hnn::retention` | Value-kernel/mode consumer (campaign 3), encoding squares (campaign 5) |
| Physical placement | `HNN/LatticeWord` and local law owners | `hnn::realization`, `holonics_cuda::hnn::{card,port,word,tree}` | Host deposition remains authoritative; device debts #76 |

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
