# The machine: HNN in its geometry and its law

[definition] This is the shared starting point for [Codex](../AGENTS.md) and [Claude](../CLAUDE.md).
It states the object, the equations its implementation preserves, and their owners. The
[model formula](HNN_FORMULA.md) gives the full law; [THE_REBUILD](plans/THE_REBUILD.md) orders the
construction; [CONSTRUCTION_STATE](../CONSTRUCTION_STATE.md) records the position; the
[research routes](../research/records/README.md) recover the derivations. Existing code is what is
in `crates/` and `lean/` today. The host `holonics::hnn` and resident `holonics-cuda::hnn` implement the
field. The landmark tree and the population of families that reads it supply the measured
compression; the loaded resonator (`hnn::ring`) connects the resonator's returned wave and adjoint to
the field. THE_REBUILD's [unified plan](plans/THE_REBUILD.md#the-unified-plan-september-28) orders
the joins that remain, and [CONSTRUCTION_STATE](../CONSTRUCTION_STATE.md) distinguishes measured
results from them.

## The top: a Holarchy and its aeons

[definition; Brandon, September 27: "Aeons and Holarchies are at the top"; the construction
`agent-inferred`, [the unity audit](../research/records/2026-09-27_THE_HOLARCHY_AND_ITS_AEONS_ARE_THE_TOP_THE_DECISIONS_DISSOLVE_INTO_THEIR_OWNERS_AND_LEARNING_IS_PROTOTYPED_WHERE_A_HOLARCHY_MADE_THE_TERRAIN.md#2-the-unification)]
**The HNN is a Holarchy, and its passage is an aeon.**
- **The Holarchy.** Its closing rotor rings and its helical pair contacts are Holons, each
  certified on its own, joined at ports by `interconnect`: `hnn::Field::holarchy` returns the
  `holarchy::Holarchy`, and the mount certifies that it glues or refuses with its typed gluing
  defect. `hnn::Field` is the Holarchy's declaration, a chart of it.
- **The receiving composition** [interpretation; the unified plan, September 28]. At the field's
  receiving port the receiver mixes its constituent families by Bayes, the discrete replicator
  (`receiver::population`): the landmark tree (`compression::landmark::context`, the shift
  navigator's landmarks, held in `Θ` at the receiving locus) is one family; a field-derived predictor
  (today `hnn::receiving`'s combined face `q_C`, the tree's grain logits plus the wave) is another;
  terrain navigators and composed eggs are others. The HNN's scored face is that population at its
  own port (`hnn::receiving::receiving_population`, `receiver::population::port`): the tree and
  `q_C` at ½/½, `q_C` read through its exact enclosure; it replaced the carried-ratio mixture at
  the unified plan's U1, whose codes the standing cut placed within that chart's drift of it. The
  population and its statistical
  families are not yet Holons joined at power ports: their update and code identities are their own
  laws, and their join to the Holon's energy balance is owed (the unified plan, U1 and §4).
- **The aeon.** Its passage is an aeon on the Holarchy's parametric orientation (the lift of the
  rings' joint clock torus): the receiver reads it by epochs, the cells between two crossings of its
  section; a pump period or a clock closure is a cycle; the aeon boundary is the collapse; and the
  first law over the aeon is `aeon::EnclosedLedger`. `hnn::Reference::expose` is a cut's passage
  through the resident's aeons, one closed at each joint-clock carry-out.
- **What the code joins** (read from source at this commit): the resident's aeon is an
  `aeon::Aeon` on the parametric orientation from its opening lift point to the joint clock's
  carry-out; each ring's epochs are the flux through its own ring section; the carry-out is an
  `aeon::Cycle` of the last ring's clock when that ring opened on its section; the boundary runs
  the collapse; and the resident carries the `EnclosedLedger`. Since the unified plan's U5: the
  receiver's spans of cells are an `aeon::Epochs` reading, the epochs of the cut's cell clock at
  the receiver's section (`hnn::receiving::ReceivingPhases::windows`, which the exposure reads); a
  pump's period is an `aeon::Cycle` of its own clock (`hnn::ring::PumpDeclaration::period`); every
  ring clock is its navigator's `navigator::Clock` (`hnn::field::Ring::clock_at`), and the
  selective step's carry is its jumps, the flux of its section (Lean
  `HNN/Moment.SelectiveDecl.carryIn_is_section_flux`).
- [open] One join is not yet in the code: the receiving tree is storage read by the receiving
  face, not a Holon joined at ports in `Field::holarchy` (the unified plan's U1 named the missing
  maps; #62).

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
([the line](THE_MACHINE.md#the-line-the-rebuild-serves)). Holonic Compression couples a
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
| Participation and transported current | `T_F[Ψ]=Σ_G a_FG[Ψ] U_(F←G)[Ψ] Ψ_G`, over admitted contacts | `HolonicAdjointNormalization`; the positive-kernel chart in [HNN_FORMULA](HNN_FORMULA.md#one-connected-tensor-computation) |
| Phase comparison | `s_ij=β cos(2π(q_i−q_j−φ_ij))`, the pair receiver at zero advance and unit radii, with connection `φ`; amplitudes and general pairings extend it | `HelicalPairInteraction.bilinear_score_eq_polarized_quadrance`; `holonics::geometry::screw` |
| Complete variation | `δT=Σ a δ(UΨ)+Σ δa UΨ`; for softmax `δa=(diag(a)−aa*)δs` | `HolonicAdjointNormalization.laplacianReturn` |
| Local learned reaction | `Φ(s,c)=s⊕c⊕(c⊗s)`, `incoming=s+MΦ(s,c)`, `out=S_D(incoming,b)` | `HolonicConstitutiveCirculation`, `Holon/{Reaction,Cayley}` |
| Normal law (deposition) | `H=H₀+Σw f f*`, `B=B₀+Σw t f*`, `W H=B`; priors, weights and receiving constraints are declared; an HNN locus steps `W'=W+ηD`, `D=Σw g(H'⁻¹f)*`, at the certified `η`: the largest `2^k` with `ηC≤a` and `ηc≤1` (`a=Σw⟨g,Df⟩` checked, `C` the certified curvature along the ray, `c` the lattice's covector scale), the loci together holding `s(Σηm)²≤Σηa` on their logit moves `m` | `Holon/Deposition` (`certified_step_descends`, `joint_step_descends`, `gauss_newton_curvature`, `gram_certificate_bound`, `active_element_growth`), `HNN/Normal.certified_normal_step`, `Objects/Deposition`, `NavigatorInference`; `holonics::holon::deposition::CertifiedStep`, `holonics::hnn::constitution` |
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
  equation is only the continuum limit ([THE_REBUILD](../research/records/2026-09-28_THE_REBUILDS_CONSTRUCTION_RECORD_STEPS_ZERO_TO_FIVE_THE_CAMPAIGNS_AND_THE_FORWARD_PLAN.md#the-law-of-one-passage-a-change-on-a-medium-81-82), "The causal cone"). Brandon's
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
| Parametron storage, pump, sheets and lock | `Objects/{Parametron,ParametronLock}`, `HNN/{Ring,Floquet}` | `holon::parametron`, `hnn::ring` (the Floquet certificate, the locked sheet, the receiving bank), CUDA resonator kernels | Loaded forward/adjoint connection (`hnn::ring`, built); the constitution's certified step reading the Floquet bound (`FloquetBound::reach`); the rotating pump's tongues and subharmonic multiplier (#62) |
| Receiving comparison and covectors | `Objects/Ratio`, `HNN/Ratio`, `Compression/Landmark/Context/{Tree,Compaction,Standing,Epoch}` | `hnn::{ratio,receiving}`, `compression::landmark::context`, CUDA compacted tree | Composed lattice drift and the log squaring invariant (#62) |
| Constitutive current, storage and scattering | `Holon/{Element,Dirac,Law}`, `HNN/{Word,Propagation}` | `holon::{element,dirac,law}`, `hnn::{propagation,word}` | Complete word sensitivity and concrete diamond bridge (#62) |
| Source moments, retention and release | `Transport/SourceMoment`, `HNN/{Moment,Retention}` | `hnn::{moment,pending,retention}`, `receiver::{standing,release}` | Mode release, founding and moment quotient (campaign 3) |
| Reuse at future receivers | `Compression`, `Foundation/{ReceiverHistoryCompression,NavigatorModeQuotient,CausalRelevance}`, `HNN/Encoding` | `compression`, structural `hnn::retention`, `hnn::encoding` (the encoding squares, U6) | Value-kernel/mode consumer (campaign 3); the Hankel identification of the founded dimension (#62) |
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
consumers, and the [formal framework](FORMAL_FRAMEWORK.md) connects the Lean framework's subjects,
so work starts from the accumulated construction.

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

## The line the rebuild serves

[project-postulate] **Compression is intelligence is navigation** (Brandon). The rebuild builds one
line: Holonic Compression and landmark discovery, executed at scale by the HNN and applied to every
target the framework is advanced enough to reach. The Riemann hypothesis, Hodge, complex Euler and
Navier–Stokes, and Birch–Swinnerton-Dyer are such targets. They are not a separate "Millennium"
category: work on them is landmark discovery and compression, stated in the same objects as
everything else.

- **Terrain** is stuff in general: whatever is present for a navigator to meet. That includes
  Holons, their constitutions and modes, and an exterior source.
- A **fractal navigator** is a function with an initial configuration, its own clock and carry, a
  family of restrictions with its scale square, and address words
  ([elementary objects §3](ELEMENTARY_OBJECTS.md#3-navigator)). The guides called it a
  "generator". That word keeps only its algebraic senses: a generator of a group, the Lie generator
  `ξ` of a helix, a generating function.
- **Holonic Compression** couples a navigator's resonating modes with terrain.
  - Where a navigator's mode meets a terrain mode, it rides that mode at minimal work (resonating,
    RIDE). What it cannot reach, it founds (emanating, FOUND).
  - A compression is a codec pivot that carries its decoder
    ([tablet](canon/TABLET_THE_COMPRESSION.md)). The navigator and its decoder stand in for the
    material they regenerate, and the decompression is causal: it unfolds over the navigator's clock.
- **Kernel and cokernel** are the two sides of that coupling, dual in the way Holon and coholon are.
  Against a receiver family, a navigator's face map `F` has:
  - a **kernel**: the differences no admitted future receiver distinguishes. Quotienting by it is
    compression, and it is retention. Owners: `Foundation/CausalRelevance` (the relevance kernel),
    `Foundation/ReceiverHistoryCompression` and `Foundation/NavigatorModeQuotient`.
  - a **cokernel**: what the navigator's image does not reach, the residual that is emanated or
    retained as a separator, interior or defect. `Landmarks/CokernelCalculus` states this calculus
    once, for the BSD descent and for integral Hodge.
- **Landmarks** are faces where navigator paths converge:
  - lock addresses and fixed points;
  - constraint identities: π and `e` are navigators that carry no error, and `Λ_DN` is another;
  - zeros and primes.

  **Landmark discovery** is locating keys ([keys](ELEMENTARY_OBJECTS.md#keys-locks-and-navigation)):
  inferring the configurations of navigators by loop closure. It is the same inference the HNN
  performs.
- **Measurement.** A compression is measured against the literal by description plus work
  (`Kt=|p|+log t`; `Foundation/{ReceiverCodeCost,NavigatorInference}`). It states its kernel and its
  cokernel residual. There is no single scalar of progress.

[interpretation] The targets read as instances of the line. Their records grade each claim.
- **RH.**
  - Zeros are landmarks of spectral placement: `Zeta/FosterTanks` reads the zeros as LC tanks, and
    `ZeroPairLock` gives lock ⇔ `σ=½`.
  - The de Bruijn–Newman heat flow has `Λ_DN≥0` (Rogers–Tao) and is aimed at `Λ_DN=0`.
  - `Computation/ZeroNavigation` states what finite observations can and cannot decide.
- **Hodge.** Cycle production: which harmonic coholon classes actual Holon cycles realize, with the
  obstruction in the cokernel of that realization.
- **Complex Euler and Navier–Stokes.**
  - Velocity is a coholon and vorticity is `du♭`.
  - Relevance acts on the tail.
  - Necks are convergence points, and the singular aeon is A11 of the
    [aeon record](../research/records/2026-09-24_THE_AEON_EPOCH_AND_CYCLE_STANDARDIZE_THE_PASSAGE_OF_TIME.md).
- **BSD.** The kernel of the descent face is the doubles (`EllipticCurve/FamilyKernel`). The rank
  counts independent navigators. The obstruction lives in a cokernel.

Their Lean in `Zeta`, `Hodge`, `Fluid`, `EllipticCurve`, `Gauge`, `Coupling`, `Landmarks`,
`Mathematics` and `Computation` under `lean/Holonics/` and `lean/HolonicsResearch/` is the most
developed use of the framework. It is not scheduled behind the HNN: work on a target proceeds
alongside any step. Each reusable law it finds lands in the shared objects (a navigator, a
kernel/cokernel statement, a landmark), not in a problem-named silo.


## Measurement

[definition] Moved from THE_REBUILD's step-4 design, (f), on September 28; the campaign success table stayed with the [construction record](../research/records/2026-09-28_THE_REBUILDS_CONSTRUCTION_RECORD_STEPS_ZERO_TO_FIVE_THE_CAMPAIGNS_AND_THE_FORWARD_PLAN.md).

[definition] **The cuts and their protocol.**
- **Every campaign is done on the standing real cut, with online baselines** (review E1–E4).
  Brandon's ruling of August 26: "we want an *inferred response* and not a manually posed outcome
  that you cherry-picked".
- **The standing real cut is the tail of the conversation data's development stream.** The
  private exposure dataset (`holonics.conversation-exposure.v1`, 24,768 occurrence families)
  declares its own partition at its temporal cut: 22,449 development families before it, 617
  evaluation families at or after it, 1,702 deferred. The cut is the development stream's last
  6,148 cells, of which the final 1,190 are held out: the stream's own later occurrences, so no
  held-out cell precedes a training cell. The evaluation partition is not read into it and stays
  unspent for the outcomes' frozen task splits (step 8). Cells are the UTF-8 bytes of each family's
  first view's visible parts in the dataset's declared order; roles and provenance are not
  encoded. The population is `n* = 6,148`, the smallest the declared field admits, which keeps the
  exposure near the projected six hours (3,074 receiving epochs); the held-out length is one mean
  aeon of the joint clock on uniform bytes, `⌈5·7·11·13·2⁸/1,077⌉ = 1,190`, set from the field, not
  the data. `research/notebook/hnn_design/standing_cut.py` writes the cut and its manifest (hashes,
  counts, held-out range) to `.local/cuts/`; `hnn_exposure -- cut-file` reads the held-out range
  from the manifest; the notebook reports the cut by scope and counts only, and #73 records its
  hashes. (Agent-inferred from review E1, the ruling above and the dataset's declared partition.)
- **Every comparison is scored prequentially: at the standing before its own deposit, held-out
  cells included.** The retention and deposition laws settle the protocol:
  - deposition is the only law changing a constitution, and a comparison whose covector reached a
    locus deposits there; withholding a scored comparison is an exterior choice with no law;
  - a cell scored before its own deposit has not been learned from, so scoring then depositing
    leaks nothing: the sum of those code lengths is the receiver's prequential description length
    of the held-out cells given the development cells (the sequential chain rule);
  - "held out" keeps its one meaning: no design choice (depth, precision, step, grain) is made on
    those cells.

  Every coder, the model and each baseline, is scored the same way on the same cells in the same
  order. The crib rule (review D1: no key learned from a cell before it is scored) is unchanged,
  since a crib holds only cells already scored. (Agent-inferred from the retention and deposition
  laws, after the region table's receipt located the asymmetry: the exposure compared the held-out
  cells and never deposited them, while the online baselines kept learning on them.)
- **The wide cut.** Choosing among families of hundreds of laws on 4,958 development cells did not
  transfer to 1,190 held-out cells ([record](../research/records/2026-09-26_THE_LANDMARK_TREE_AT_SCALE_THE_STOP_PRIOR_LOCAL_WEIGHING_THE_WIDE_CUT_AND_THE_STORAGE_WHERE_PATHS_PART.md) §3). A second pinned development
  cut holds the development stream's last `2^20` cells, which include the standing cut; its final
  `2^17` cells, one eighth, are held out. `2^20` is the largest power of two whose tree fits the
  workstation's memory budget at the measured bytes a node; the worker derives it and refuses a
  larger cut. The evaluation partition stays unspent. The count-only receivers' laws are chosen on
  its development cells, then one held-out pass is read. The HNN's full exposure stays on the
  standing cut until its cost per receiving epoch falls. The file is
  `.local/cuts/wide-real-cut.{bin,json}`, with the standing cut as its tail, byte for byte.
- **A larger cut re-measures the laws already chosen,** one prequential passage each, in minutes.
  A family is re-swept only when the scale could change its choice, and only at a cost stated in
  advance. (Agent-inferred; the first wide run re-swept 529 stop laws with their depth sweeps for
  43 minutes to reconfirm `½` and was stopped, [record](../research/records/2026-09-26_THE_LANDMARK_TREE_AT_SCALE_THE_STOP_PRIOR_LOCAL_WEIGHING_THE_WIDE_CUT_AND_THE_STORAGE_WHERE_PATHS_PART.md) §4.)

[definition] **How a run is read.** Every number comes from an `InteractionReturn` and is reported
with its units, population and clock. The host reference's exposure (`Reference::expose`) gathers
them into one readout, `hnn::reference::Exposure`, whose fields are named below.
1. **The scored face and the declared comparison covector.**
   - Since the likelihood mixture (September 26), `L_target|model = Σ_j −log₂ q_j(t_j)` scores the likelihood mixture of
     the tree face and the combined tree/wave face, the receiver's population over the two since
     U1. Both component codes are reported beside it.
   - The wave's covector comes from its own combined face `q_C`, in the declared odometer chart,
     with its phase excess and winding. It is not the derivative of the quantized mixture score.
     Exact enclosures and grain fibres accompany the scored readings.
   - The baselines are fitted online on the same exposure with a declared prior (review E2):
     - order-0 and order-1 with the Krichevsky–Trofimov prior;
     - PPM (order 2, exact, in `hnn::reference`);
     - xz and zstd bits per character, with their description cost: computed outside the crate
       (no processes in `holonics`), owed to the application that runs the exposure.
   - Failing to beat online order-0 is reported as a failure.
   - Selection reads the declared scored face. The component comparison that supplies each
     covector is named explicitly (the receiver's population, `hnn::receiving::receiving_population`,
     scores; the combined face's comparison supplies the wave's covector).
2. **The first law of learning over an aeon.** `ΔC = exchange + deposition` (aeon A7), with the
   released part counted as exchange, through `aeon::EnclosedLedger` (the enclosed first law; Lean
   `Aeon/Production/FirstLaw.{ledger_telescopes, ledger_is_first_law, enclosed_contains,
   enclosed_telescopes}`). Beside it, the face's comparison
   with the literal per aeon: `Σ_k ℓ_k + Σ_k g_k = n·log₂|A|`, exact algebra whose `g_k` is negative
   wherever the face predicts worse than uniform, so it is a reading, not a budget ([the perceived-difference record](../research/records/2026-09-25_THE_CLASSICAL_LOSS_IS_THE_PERCEIVED_DIFFERENCE_AND_THE_DEPOSITION_REMAINDER_IS_A_REPRESENTATION_RESIDUAL.md)).
3. **Cost against the literal (review E3).** `Kt = |Field::describe()| + |Θ_initial.describe_physics()| + K_keys + L_target|model + ⌈log₂ ExactWork⌉`.
   - The first two terms describe the field and its initial material; the located keys cost
     `⌈log₂ d_g⌉` per published key (what learning located is paid for; review D1), and
     `L_target|model` is item 1's reading.
   - The literal is `⌈log₂|A|⌉ · n`, and the pivot pays off exactly when `Kt` is smaller.
   - Over a declared population the description is paid once.
4. **State against source, in bits.**
   - The exact bit lengths of the `Current`, the `SourceMoment`, the open pending ratios and the
     constitution.
   - State bits per source bit, with and without the collapse.
   - The moment's total bits per source bit against its capacity crossover `n*` (R2 H1).
   - The constitution's bits per deposit by carrier (entries, remainders, solved charts), against
     the lattice deposit's bound, and the released tails' bits: the exposure's `constitution_curve`, one
     `CurvePoint` per published commit (the mount's first): its `commit`, its `CarrierBits`, and the
     reaching deposit's `released_bits` and `stepped` entries (zero at the mount).
   - `peak_word_bits` is the largest numerator-plus-denominator bit length of a wave, contact
     or resonator state coordinate, maximized over the word and the exposure's refines.
     Carried residuals have their separate complete bit receipts; this state-coordinate reading
     does not claim to count every arithmetic intermediate.
   - The released bits and dimension per aeon.
   - The source moment's coordinate layout is fixed by its declaration. The receiving landmark
     tree grows with arrivals: its storage where paths part bounds its nodes while its labels still depend on
     depth. Count both in retained bits and allocated bytes. The prototype's historical moment
     reading was 2,936 bytes at `N = 2`–128; it is not a bound on today's complete constitution.
5. **Work, time and rates (review E4).**
   - The `ExactWork` of each method.
   - `N_face/dt` and `N_update/dt` per receiver clock (objects §10).
   - Wall time is an exterior face recorded with its clock.
   - Cold setup, generation, update, ingestion, rest and egress are reported separately.
6. **Locality.** The loci reached per deposit (the diamond), each ring's tick count, and the cone
   per word. Beside them, the openness of the source-to-receiver path (review C2): `open_windows` of
   the `windows` read, the receiving epochs whose refine receipt's `PathAttenuation` was open at
   their cut, so a shielded receiver is reported as a located cause.
7. **Numerical health.** The receivers' fibres, and the device's ball radii and residual
   certificate (step 5). No committed-face residual exists.

[definition] **Unknown is not zero.** The following are reported as unknown whenever no receiver
counted them:
- energy in joules and device power;
- bits per joule;
- occupancy, and any other counter nothing counted.

A timeout is an unfinished run at its deadline.

[project-postulate] **No benchmark theatre.**
- A regression control is never the milestone (D8), and the standing retrospective cases keep their
  failed status until step 8 changes it.
- Every product number carries its baselines, units, population and failure count.
- No scalar of progress is formed.
- A number that no run produced is not written.

## Guards that make the rejected forms impossible

[definition] Each rejected form is excluded by a construction. A type construction is proved by a
rustdoc `compile_fail` doctest, which needs no new dependency. Lints are enforced by
`#![deny(clippy::float_arithmetic, clippy::disallowed_types, clippy::disallowed_methods)]` in
`hnn` and by `crates/holonics/clippy.toml`'s `disallowed-methods` and `disallowed-types`; the
receipt runs `cargo clippy -p holonics --all-targets -- -D clippy::disallowed_types -D
clippy::disallowed_methods -D clippy::float_arithmetic`. Each `compile_fail` doctest states its
error code, checked with `RUSTC_BOOTSTRAP=1 cargo test -p holonics --doc` (stable rustdoc
ignores the codes; gate 1, `tools/gate.sh`, runs every library doctest), and says whether its
guarantee is structural. A guard built at the notebook's exterior boundary
(`research/notebook/hnn_design/exterior.rs`) is proved by the doctests of
`crates/holonics/src/exterior_guards.rs`, which include that file as a module and exist only while
rustdoc collects doctests. No guard is a source-text scan
(review A8; agent-inferred from Brandon's September 24 message on tests, "I do not trust that the
tests can comb through anything valuable").
1. **No tape in the moment; no lossless source below capacity presented as lossy (R2 H1).**
   - `SourceMoment` is sized once, from the `Field`, and accepts closing source rings only. A
     rotation transport has no ingest port (`compile_fail`).
   - `Field::declare` computes `n*` by the counting formula, on exact integers, and refuses a
     declared population shorter than it. The formula is the identity route's (a ring steps by
     its lock's Boolean fit plus the carry); a moment that has counted a located occurrence refuses
     the reading (`SourceMoment::capacity`, `HnnError::CapacityOwed`), and the located route's
     certificate is owed (#62).
   - A capacity test checks the count, not one slot's bits: `log₂N(n)` per source bit is at least 1
     below `n*` and below 1 past it, at `n` = 2 … 4,096 on the three-ring control (R3 H1).
2. **No word outlives its return.** `Word<'c>` borrows `&'c Field` and owns its tick operands.
   `pull_back(self, …)` consumes it, and it is not `Clone`. No field of `Field`, `Current`,
   `PendingRatio` or `InteractionReturn` has a lifetime parameter (`compile_fail`).
3. **A pending ratio holds operands only:** the anchor `λ`, `M`, the `ReceivingPhases` and the
   commit.
   - No constructor accepts a material, a word or a face.
   - The resident owns it, and `compare` consumes its id when it succeeds.
   - `refine` refuses beyond the pending capacity.
   - The one other operand the resident keeps across methods is the first law's `Arrived` ((c),
     "The host reference"): the last compared pending ratio with its `A` target cells. There is at
     most one, the next compare replaces it, it is counted in the state bits, and only the ledger's
     deposition and release steps read it. Beside it, refine's word and faces are kept for its compare,
     tagged with the constitution's commit and dropped by a deposit or a collapse: a cache of a
     read on an unchanged constitution, not an operand.
4. **No journal.** `Constitution` holds only the current parameters, the normal statistics, their
   carried remainders and each locus's deposit count: no list of deposits, updates, gradients or
   producers. Its fields are private. `deposit` and the
   collapse are its only mutators.
5. **Retention only by the collapse, only at aeon boundaries.** `close_aeon` is the only operation
   that reduces the constitution, and the resident accepts it only at the joint clock's carry-out
   (R2 M12). An aeon is carried by its lift point, `O(G)` integers.
6. **No clock outside the lift point and the word's hop clock (R2 L3).** No `hnn` type holds a clock
   except `λ` in `Current` and the word's own `navigator::Clock` in `Word`, which is structural in
   the type definitions. The one sanctioned exception is key location's fibre of clock-keyed
   candidates (`RingKeys::fibre`; "Candidates" in the data → menu map), a reading of
   `locate_keys` that no state keeps. That aeon, epoch and cycle are the only time words is a
   review rule, not a type guarantee, and no identifier scan runs.
7. **No Lean in the pipeline.** `holonics` keeps its four dependencies (and `rayon`, by the hardware rule), and `clippy.toml` disallows
   the `std::fs` and `std::process` entry points, denied in `hnn` (an exterior notebook allows
   them where it reads).
8. **No templates.** Output faces are `ρ_R` readings, and no port method returns a string.
9. **The codec is not the architecture: every source enters encoded, and no exterior code reaches
   the field** (lessons, [September 24](../research/records/2026-09-24_LESSONS_FROM_THE_WORKBENCH_AND_ATHENA_PROTOTYPES.md)
   D2, and [September 29](../research/records/2026-09-29_LESSONS_THE_FAILURES_THAT_REPEATED_AFTER_THEY_WERE_RECORDED.md)
   §1.3, "text run on its codec's grain"; recurred October 5 in the byte-chart key location and
   the 2⁸-port text repair).
   - **One source type.** The field reads only `Encoded` cells (`hnn::encoding::Encoded`, each
     occurrence a `PortCell`): on each source ring, classes of its own port chart `ℤ/d_g`, carried
     with the decoder `D` and the Preimage Fibre of the encoding that produced them, the boundary's
     labels and, on the located route, the located advances as the lift's digits at their periods'
     width (`LocatedAdvances`). Its fields are private, and only `hnn::encoding` constructs one, in
     two ways:
     - `Encoded::identity`: the declared identity encoding of a known-truth terrain
       (`holarchy::terrain::KnownTruth`, built only by a terrain's generator, never from a file:
       the cyclic terrains on `ℤ/|A|` and the located transport's stepped terrain,
       `holarchy::terrain::known`). It is refused unless the terrain's classes inject into every
       source ring's ports (`|A| ≤ d_g`, else `EncodingError::Fold`): no fold, no residue.
     - `Encoded::through`: the image `E` of a founded `Encoding` (`Encoding::found`), whose squares
       `D E = ρ`, `E T_a = U_a E` and the injection square are checked on every reached state. Its
       chart must be one the field's own key location built: today the located chart
       (`PassageChart::located`), founded on the transport a `TransportLocation` locates over the
       read set when its fibre is one gauge class (`EncodingError::Plural` otherwise), and read in
       the receiving cells, never in the labels; each code enters as the receiving cell its located
       label reads.
   - **The field's entries take it, and nothing else.** `Field::selective_step`, `Current::step`,
     `SourceMoment::ingest`, `ExecutionPort::{ingest, locate_keys, compare}` (the host reference
     and the card), `hnn::keys::{locate_keys, station_pairs, damaged_station_pairs}` and the key
     location's crib helpers, `hnn::ratio::target_phases`, `hnn::receiving::clock_letters`, the
     exposure's `Cut` and `Word::compare_contact_storage` accept `&Encoded` only; a
     `compression::keys::repair::DamagedPassage` (the input of `compression::keys::local::locate`)
     is built outside the crate only from an `Encoded` and its erasures (`DamagedPassage::encoded`).
     Each entry admits a passage only when it was encoded against this field's source rings, its
     classes are at most the field's `|A|`, and a located route's helix is the field's rings
     (`Field::admit`, `HnnError::Unadmitted`). An exterior code (a byte, a code point, a sample, a
     joint angle) has no path into the field. `compile_fail` doctests show it: `E0308` on `&[usize]`
     and on one-hot cells at `Field::selective_step`, `SourceMoment::ingest`, the port and the keys,
     `E0624` on `DamagedPassage::new`, and `E0451` on a forged `Encoded`. No `From<Faces>`,
     `From<Released>` or `From<Vec<_>>` exists, so a release cannot be fed back as the next source
     cell.
   - **The located step.** An occurrence of the located route steps ring `g` by its class's located
     digit plus the carry, `a_g(c) + carry_g ≤ d_g`, its ticks held at `u64` (`SelectiveStep.ticks`),
     and the squares `D E = ρ` and `E T_a = U_a E` are checked on the lift the step reads and the
     lift it reaches (`Encoded::check_step`); an identity steps by the lock's fit as before. The
     step is atomic: it is staged and committed only once its squares hold, so a refused occurrence
     (a lift off a partial-span chart's reached coset, `EncodingError::Unreached`) leaves the lift
     point and the moment as they were. The card takes the same digits (`hnn_moment_ingest`, its
     located chart one `u64` digit per ring and class, `ResidentMoment::ingest`, Codex's), and both
     ports discard an open whose ingest failed: its handle reads no further.
   - **No residue chart.** No constructor exists for `code mod d_g`, for `code` itself on a ring
     of period `|A|`, or for a chart founded from a passage's counts or placed at first arrival.
     `PortChart` and its residue constructor are deleted (October 5, with `one_hot` and the ports'
     `codes`): a class is its own port on a source ring (the encoding refuses a fold,
     `EncodingError::Fold`), and on any other ring a class at or past `d_g` reads the port `d_g`,
     which no lock admits, and is no edge of that ring's key menu.
   - **Exterior data waits for its encoding.** Text, image, acoustic and motor passages enter only
     through `Encoded::through`. Until the field's own keys and deposition found their encoding,
     `Encoded::through` refuses the exterior chart (`EncodingError::Unencoded`), and a run reports
     that refusal as its result. `Encoding::found` founds any declared chart as mathematics (the
     terrains' moiré, copy, crib and moment charts, the byte chart itself); only a located chart
     carries the class map an exterior passage needs, so the byte chart, a chart built from bare
     matrices and the moment chart over exterior codes are refused at `through`, as is a code no
     located label reads. A declared identity is never the bypass, since a cut file is not a
     `KnownTruth`.
   - **The alphabet fixes nothing.** `FieldDeclaration` has no exterior alphabet: its `alphabet` is
     the class count of the encodings it reads. `Field::declare` fixes the ring count and widths, the
     contacts and the complex. The moment's slots and the receiving classes are the encoding's
     classes, never the codec's. **Campaign 1's consequence:** its byte alphabet existed only
     through the fold (256 codes on a source ring of period 5), so `FieldDeclaration::campaign_one`
     reads five classes, `|A| 256 → 5` and `n* 6,148 → 190 = 2·5·19`, and a text exposure is refused
     until its encoding is founded (`hnn_exposure`, `executed text` and `executed text-repair` report
     the refusal as their result).
   - **Tests that fail on the rejected form.**
     - One field is declared under two encodings of different exterior alphabets. Its widths,
       channels, complex, moment slot count and receiving class count must be equal.
     - `Encoded::identity` must refuse a terrain of `257` classes on `d_g = 60`, and
       `Encoded::through` must refuse the byte chart (both built, `hnn::tests::encoding`).
   - **The code length does not see the labels.** For every permutation `π` of an exterior
     alphabet, `L(field; π∘x) = L(field; x)`: the field's description length of a passage is
     unchanged when its symbols are relabelled (code length is invariant under relabelling; keys are
     not, [the egg's genome](../research/records/2026-09-27_THE_EGG_IS_A_GENERATORS_GENOME_SELECTION_IS_BAYES_AND_THE_FACES_OF_INTEGERS_ARE_MOIRES_OF_GRATINGS.md) §5).
     The residue chart breaks it; a test that relabels and compares fails on any chart a code
     chooses. On the located route the stronger form holds and is tested
     (`compression::keys::transport::tests`, the located route): the located chart, the founded
     encoding and every encoded cell of `π∘x` equal those of `x`, only the labels are carried,
     `λ_(π∘x) = π∘λ_x`, and the located code length is equal.
   - **Status (October 5).** Built: the type (`Encoded`, `PortCell`, `LocatedAdvances`,
     `Encoded::{identity, through}`, the located chart in `hnn::encoding`; `KnownTruth` in
     `holarchy::terrain::known`) and the entries, which accept only `Encoded`. The residue chart,
     `one_hot` and `codes` are deleted. #375's validation listings on the terrains reproduce byte for
     byte through the declared identity, and the located route reaches the field on the host.
   - **What is structural.** The type and its constructors: `compile_fail` doctests on `Encoded`
     and `PortCell` show a forged one (`E0451`), an exterior code list, one-hot cells or a code
     where they go (`E0308`), and `From<usize>`, `From<Vec<_>>`, `From<Faces>` and `From<Released>`
     (`E0277`) refused, and the lawful identity compiles and runs. The refusals (the fold, an
     unlocated chart, a plural fibre, an unread code) are runtime laws, each pinned by a test.
     Supersedes the residue chart's "stated exception" and its September 29
     `[open]` (`hnn::field`, "The port chart").
10. **No scalar operand.** `Word::pull_back` accepts only a `RatioCovector`, which only a
    `HolonRatio` constructs (`compile_fail`).
11. **Learning is locating keys and depositing covectors,** never "a current changes a later
    current's standing". Keys change only through `locate_keys`. The constitution, the standings
    `q` included, changes only through `deposit` of a `compare` return and through the collapse
    (design (a), "The light is the change"). `refine` has no path to it.
12. **No floats.** `#![deny(clippy::float_arithmetic)]`, and `f32`/`f64` are disallowed types.
13. **No compatibility.** There is one exact code, `Field::describe`; no legacy reader, alias or
    `Legacy` law arm.
14. **No global solve (§8.1).** `propagation.rs` exposes only junction-local solves. A cone test
    checks that an impulse at any ring is supported within `t` hops after `t` ticks, exactly.
15. **Declared charts and residuals (§8.4).** Every lattice split has its decoder and residual. The receiver's grain reading is
    `CarriedPower` at a face, which returns the carry, the phase class and the fibre. No port method
    takes a free tolerance: `release` reads its receiving phases' grain, and the collapse releases
    only exact complements (R2 §2), never a carried remainder. A deposit's released tail is fixed by
    the locus's deposit count, reported in its receipt, and bounded over every aeon since the locus's founding
    (`HNN/LatticeDeposit`). A constitution over its bit budget is refused
    (`ConstitutionBudget`); its declaration is not silently coarsened (R3 §5).
16. **No change outlives its word (R2 C2c, C3), or its refinement.** `Current` has no wave or
    contact-state field. Waves and contact states are fields of `Word` only, created at zero by its
    open and dropped at its return (`compile_fail` on building a `Current` from a `Word`'s waves).
    [agent-inferred, amended September 29 for U6's native generation] Within one refinement a
    continuing word opens on the change the previous word of the same refinement left
    (`Word::continuing`), so its waves, contact states and resonator states carry across the word's
    boundary. The refinement owns its words until its return consumes them (the linear readout's
    `Section::pull_back`, retired September 30 with the readout, batch H, at
    [`f5fd8f3b`](https://github.com/brandonrdug/holonics/blob/f5fd8f3b/crates/holonics/src/hnn/prediction.rs);
    that ownership binds any refinement that opens one), so the change still lives only inside one
    evaluation, bounded by its `K·w + 1` junction steps and never by a source length, and nothing
    of it reaches `Current`, a
    pending ratio or the constitution except through a deposit's covectors. The reason: generation
    refines one joint field through the model's constituted dynamics (HNN_FORMULA, "Generation as
    field refinement"), which the word-local release would cut at every word.
    [proved-derived, amended October 3 and 4 for the reception carry] Under the reception carry
    (`Reception::Carry(Absorption::Nothing)`, the default since October 4; `Reception::Rest` is its
    `A = I` limit, which keeps the guard as stated above) a
    reception's word opens on the interior of the change arriving at the last crossing of the
    previous word read (its refine writes the carry, so several pending ratios are one chain in
    refine order, record §8), at that crossing's tick so a declared pump continues from
    it, crossed into the next cut's references (each contact's waves at the junction's reference
    change, each contact's and resonator's rate at held momentum; `Word::open_received`,
    `ReceptionCarry::crossed`), so that
    change outlives its refinement into the next reception's opening and no further. The resident,
    not `Current`, holds the one carried change, its tick and the references it was measured in
    (each contact's conductance and momentum at that cut, and each resonator's momentum), overwritten at every reception, and the
    return stops at the opening: the
    covector reaching the carried change is a reading, deposited nowhere
    ([record](../research/records/2026-10-03_THE_RECEPTION_CARRIES_THE_INTERIOR_CHANGE_THE_SOURCE_PORT_IMPOSES_THE_MOMENT_AND_REST_IS_COMPLETE_ABSORPTION.md)).
17. **No catered machinery** ([antipattern record](../research/records/2026-09-29_ANTIPATTERN_CATERED_MACHINERY_A_TASKS_SOLUTION_ROUTINE_NEVER_STANDS_IN_FOR_LEARNING.md)). No receiver, family, stage or
    port computes a task's answer by an authored routine or recognizes its inputs by a grammar
    fitted to a test's layouts. A terrain generates its truth; the machine locates it. The
    arithmetic calculator and the arithmetic eggs are retired, and the byte-tree text line's
    catered layers are retired when the native encoding and prediction land. The population's
    entries are sealed (guard 20), so no code outside the crate can hand the receiver a family;
    whether an in-crate family is the machine's own navigator or an authored answer stays a review
    rule.
18. **A release reads the field, never the receiving storage** (October 5,
    [contamination history](../research/records/2026-10-05_THE_CONTAMINATION_CYCLES_EVERY_COPY_PIPELINE_FOLLOWED_A_DEMAND_FOR_OUTPUT_BEFORE_THE_FIELD_COULD_RELEASE.md)).
    `FieldMaterial` is the field's own material: rings, contacts, ports, resonators, transport
    and the receiving map `R`, the field's decoder (moved in October 5 for the physical repair,
    `hnn::prediction::repair_by_field`: `R · P_R^(τ_R) v_R` is a linear face of the ring's own
    motion and holds no count, address or seen context). It is `ConstitutionRead` without the
    landmark tree and the receiver's population, which are read at compare, and every
    `ConstitutionRead` is one through a blanket view. `generate_by_bank`, `BankPlacement::of`, the
    moment's `open_parts`, `repair_by_field` and `ReceivingPhases::read` take the material alone,
    so the release cannot read the tree's counts or a seen context. This is structural: two
    `compile_fail` doctests (E0599) on `FieldMaterial` show it, the tree and the population, and a
    third doctest shows the decoder's read compiles. A release is a joint refinement of its open stations. No
    class is drawn and fed back as the next source cell: an emitter of one cell at a time over the
    combined face is the recitation form.
19. **One release per request, shown whole.** There is no search, rerank, retry or selection
    among releases, and nothing compares a release with reference text before it is shown. Every
    text release shown carries its copy length, the longest run it shares with the admitted
    passage. An exterior notebook tool reads it outside the HNN, so recitation is visible at once.
    It is a receipt, never a control and never a grade.
    - **The one show** (October 5). `exterior::show_release(out, name, release, admitted)` is the
      notebook's only path for a text release: it writes the release whole to `<out>/<name>`,
      appends it whole, each byte for the eye, with its copy length to the private show
      `<out>/releases.show`, and prints the copy length's integers on stdout (never the bytes: the
      release may derive from private data). The copy length is `tools/copy_length.py`'s law ported
      exactly (`exterior::copy_length`, the suffix automaton of the release with its matching
      statistics, the same `key value` output), checked against the quadratic definition on 300
      pseudo-random cases and the tool's own cases (`exterior_guards`). The text harnesses show
      through it: `executed text` each request's release against the training passage and its
      request, `executed text-repair` each released span against its passage's intact runs (the
      local `common` it replaced is retired).
    - **What is structural.** Within the exterior: a release shown through `show_release` cannot be
      shown without its receipt, and nothing there cuts, selects or compares it. That a harness
      shows its text releases through it rather than writing them itself, and that no search or
      rerank exists, remain review rules; the terrain modes' class vectors on `ℤ/4` are readings of
      decisions, not text releases.
20. **The receiver's families are sealed** (October 5; the lessons' most repeated failure, "an
    authored routine stood in for learning", about seven recurrences, and guard 17).
    `receiver::population::{Family, Emitters, Layered, Keystone, PortReader}`, the entries through
    which a population reads a candidate navigator family, each have the private
    `population::sealed::Sealed` as a supertrait, so only `holonics` implements them. The
    implementors are the library's navigator families, built from a terrain's or the field's
    declarations: `KeyFamily` over `Survivors` of `GratingSheet`, `GratingParity`, `RotorKeys` or
    `PortedEmitters`; `DormantFamily` over a layered grating; `FoundedFamily`, `ChaseFamily`,
    `Unheld` and `Composed`. No library type implements `Keystone` or `PortReader`; the in-crate
    tests' rings, phase readers and scripted families (`Fixed`, `Refusing`, `Scripted`, `ByPhase`)
    are test scaffolding of the population's laws. No notebook file or example implemented any of
    them, so nothing moved. Structural: `compile_fail` doctests on each trait (`E0277`: an outside
    type does not implement `Sealed`; `E0603`: the seal's module is private), each checked to
    compile once the seal is removed. The terrain's `Chaser` is not sealed: it is the pursuer the
    machine plays against (`PurePursuit`, `ConstantBearing`) or a trace wrapped around the
    machine's own (`hnn_chase`'s `Traced`), never a family the receiver reads.
21. **Seen material is never graded as unseen** (October 5; lesson 8, "unseen means unread by any
    run", against the failure that recurred six times: F0, F2, F4 and U2's splits, `athena_field`,
    the moiré's training windows). The notebook reads a cut only through `exterior::read_cut`,
    which returns a `Cut` of two types with private fields: `Seen`, the development range
    `[0, s)` read by reference (training passages, development reads, a repair's passages), and
    `Held`, the held-out range `[s, population)`, whose positions are readable and whose bytes are
    read once, by value, at declared windows (`Held::windows`). No caller receives the bytes with a
    range to slice. `executed text` reads its training passage and development window from the
    `Seen` and its pinned requests through `held_requests(held: Held, …)`; `executed text-repair`
    reads the `Seen` alone (its read is development text by its pins) and drops the `Held` unread;
    the prequential exposure (`hnn_exposure cut-file`) takes the cut whole by `Cut::prequential`,
    whose library `Cut` compares every held cell before it deposits it. The `--read-reserve`
    bypass is removed: a cut that does not name the development reserve as excluded is refused,
    with no flag (no run had passed it). The curated cut's readers (`read_curated`, its incidence
    and aeons), which returned codes beside a held range and had no consumer since September 30,
    are retired. Structural (`exterior_guards`): a `Seen` where a `Held` is required (`E0308`), a
    `Held` forged from bytes (`E0451`), its bytes read by reference (`E0599`) and a second read
    (`E0382`) do not compile, and the lawful forms do. Whether a grading function names its input
    `Held` is a review rule; the types make the substitution impossible once it does.
22. **A run's limits are a committed pin's** (October 5; lesson 9, "a refusal changes the law or the
    partition, never the limit", against 29 raised limits; CLAUDE.md, "Waiting, deadlines and
    concurrency"). Every `hnn_prediction` mode bounded in time takes a pin's path where it took a
    deadline or a bound in milliseconds (`text`, `text-repair`; the descent's `train`, `witness`,
    `coupling`, `represent`, `run` and `resume-coupling` retired with S2 on October 5):
    `exterior::Pin::read(path, command)` reads the command, the projection, `deadline_ms`, the
    optional `unit_bound_ms` and `threads` from a file and refuses the run when it is missing,
    untracked, different from its commit, committed more than once, or of another command. A pin is
    therefore fixed once: a limit is never raised by editing it, a run past it is reported
    incomplete, and the next loop commits a new pin for a changed law, partition or read, with its
    reason. The harness installs the pin's threads as the host's pool; `text` reads the pin's unit
    bound, and `text` and `text-repair` stop at the pinned deadline (`Pin::launch`, exit
    `INCOMPLETE`). Counts that declare the read (moves, iterates, a cap, a read budget, the
    exposure's windows) stay arguments. Structural: a `Pin` is built only by `read` (`E0451`) and
    its deadline has no setter (`E0616`); the refusals are runtime laws, each run by a doctest in a
    scratch repository (missing, untracked, edited, recommitted, another command). That a new pin
    for the same read is not a disguised raise stays a review rule: the pin's projection line says
    where its numbers come from.
