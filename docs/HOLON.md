# The computational Holon

## The object and its notation

[definition] Write a Holon in a declared tensor chart as **|H⟩_F**. H carries the Holonic
entity mark (the recovered wavy underline); F specifies its frame, port/axis roles and
pairing. The notation packages the object so it can be manipulated without expanding its
construction record at every use. [Holonic notation](HOLONIC_NOTATION.md) is the consolidated
reading surface (species, index conventions, signs as passages, arrows, orientation). The existing Dirac convention is in
[the operations tablet](canon/TABLET_THE_OPERATIONS.md) and `research/papers/source/lib/dirac.typ`.

```text
|H⟩_F = Σ_I H_F^I |e_I⟩_F,          vector chart: [h₁ … hₙ]ᵀ,
Ĝ_(F'←F) = Σ_(j,i) G^j_i |e_j⟩_(F') ⟨e^i|_F,
|H'⟩_(F') = Ĝ_(F'←F) |H⟩_F,        tensor chart: H^(i₁…iₚ)_(j₁…j_q).
```

[definition] A ket denotes the participating construction in this chart; ⟨r| is a specified
linear receiver and ⟨r|H⟩ is its face. Dual basis bras in the expansion above need not be
orthonormal coordinate transposes. A metric/Riesz identification, when used, supplies its
conjugation and dual. A tensor-valued receiver retains output axes instead of contracting
all of them. A family |H(λ)⟩ keeps shared unresolved parameters λ in every participating use.

[definition] In a finite port chart, a linear operator is itself a tensor-valued Holon:
`Ĝ ∈ V_(F')⊗V_F*`; a bilinear interaction has
`𝓘 ∈ V_C⊗V_A*⊗V_B*`. It can therefore be formed, composed, differentiated and encoded using
the same algebra as its operands. A composite state can be
`|H⟩=Σ_(a,b) h_ab |a⟩⊗|b⟩` without factoring into one product `|A⟩⊗|B⟩`.
Keeping that joint tensor prevents independent component choices from inventing an
unsupported combination. These are tensor signatures, not an untyped generic wrapper.
A nonlinear navigator is a composed map; its parameters and local derivatives have their
own tensor charts. An arbitrary nonlinear map is not identified with one fixed linear matrix.

[definition] Frame, incidence and executable material belong to the object being represented;
they are not reconstructed from its displayed vector. A tensor is already a multilinear
object. HNN's computational Holon binds that tensor chart to its actual interactions and
continuation. A scalar, vector, matrix or higher tensor can be a face or a constituent of a
Holon, depending on the declared operation. A nonlinear holonic map acts on these objects
without acquiring linear superposition merely from ket notation.

[definition] The [intrinsic field construction](HNN_FORMULA.md#one-object-its-charts-and-its-recursive-geometry)
keeps heads, local sections, circulating toroidal modes and generated/recursive geometry in
one object. Smooth charts and finite tensor coordinates can describe local restrictions of
that object while its invariant or preimage families have fractal structure. A tile of copied
outputs, a column of layer nodes or a closed exterior skin is not its defining geometry.
The actual restriction, gluing, current and constitutive evolution specify what the chart shows.

[definition] A physical receiver is another participating Holon. A local interaction can
return `(H_A',H_R',Face_R)` from `(H_A,H_R)` through the shared current/material law. Its
frame, velocity, tangent/normal faces and stress/current belong to the operands. A rendered
readout is a further projection of that interaction. The
[active-face contract](CONSTRAINT_MODES_AND_RECEIVER_FACES.md#the-overlap-has-stress-bearing-faces)
connects this to traction, Lorentz/gyro transport and Einstein/Bianchi balance. The abstract
field description and its physical realization retain their declared units and constitutive
maps; an ML label does not remove these relations.

[definition] The [fluid realization](HOLONIC_FLUID_CONSTRUCTION.md) now applies this object
through material motion, oriented stress faces, Hodge decomposition, interior memory and
micro/macro restriction. The high-level interaction has a concrete energy form: advection of
an internal field and its adjoint force exchange energy, while the material gradient and
positive mobility produce diffusion and heat. Graph scattering is precisely the
[Swing](ELEMENTARY_OBJECTS.md#the-swing) `2P_D−I` about its constituted projection; the object
therefore connects to the primitive operation without replacing the field by its displayed
coefficient vector.

[definition] The [receiving Holon](RECEIVER_HOLARCHY.md) completes this distinction:
`ρ_R` is its receiving operation, while H_R carries the frame, material, current and internal
state that determine that operation. A continuous section is not intrinsically a discrete
sample; samples and coefficients present restrictions of its generating relation. Source and
receiver can both change, so their joint differential includes the receiver's motion/material
return. The first-arrival/fractal sets, entropy partitions and compression family are defined
through those actual receiving operations. A physical drive or monitor instantiates the same
interaction/encoding pattern with its own material laws.

<a id="situated-generator-inference-dormant-modes-and-action"></a>

## Situated navigator inference, dormant modes and action

[project-postulate] Text, acoustic, optical, mathematical and motor conduct use this same
construction: infer or reuse an admissible navigator relation and release its consequence
through a participating receiver. Their media supply actual interaction laws and charts.
The September 21 [source synthesis](../research/records/2026-09-21_SITUATED_GENERATORS_RETAIN_MODES_AND_RELEASE_ACTION.md)
connects the rotor/Bombe comparison, simulator interfaces and existing source owners.
“Key-like” names the configuration and phase at which a retained navigator pair closes for
the requested receiver: a Lie generator `ξ` **with an initial configuration**, which is
`SituatedScrew`, the navigator of a screw. It names no secret and no universal inverse.

<a id="the-helical-pair-interaction-unit"></a>

### The helical pair interaction unit

[definition] The computational object of this construction is the **helical pair interaction**:
an interaction (`Transport/HolonicInteraction`) whose declared rate ports carry the parameter rates
of a `holonics::geometry::ScrewPair` and whose contact slip map is that pair's relative velocity.
Its configuration, storage state and rate ports retain their explicit chart maps. The
[design record](../research/records/2026-09-21_THE_HELICAL_PAIR_INTERACTION_IS_THE_HNN_SITE_AND_PHASE_CARRIES_CONTEXT.md)
gives the source audit; the [helical guide](HELICAL_GEOMETRY.md#the-pair-is-a-holonic-interaction-contact)
owns the geometry.

```text
Objects       a=(ξ_a, x_a(0)), b=(ξ_b, x_b(0))   SituatedScrew: Lie generator and initial configuration
Parameters    (s,t), each a RationalPhase         own clock; chart phase and retained winding
Separation    Δ(s,t)=x_a(s)−x_b(t),  Q=⟨Δ|Δ⟩      PairQuadranceJet
Slip map      J=[v_a | −v_b],  Δ̇=J(ṡ,ṫ)           J_f derived from the pair, never declared apart
Variations    DQ=2 J*Δ;  D²Q=2 J*J + 2 diag(Δ·a_a, −Δ·a_b);  pullback is the adjoint
Contact       M_contact=Σ_f w_f J_f* D_f J_f; D_f⪰0, w_f>0: P=0 ⇔ D_f J_f u=0
No-slip       P=0 ⇔ ṡ v_a=ṫ v_b when D_f is definite on attainable slips
Medium        q̇=(Ω−M_contact)Gq+Bu               storage G, flux Ω, drive/action Bu, clock
Reading       ρ_R at the Perspective               release through holonics::receiver::release
```

[proved-derived; formal-checked] [`Transport/HelicalPairInteraction.lean`](../lean/ElementaryHolonics/Transport/HelicalPairInteraction.lean)
proves these pair/contact identities and the polarization identity
`⟨a|b⟩=(⟨a|a⟩+⟨b|b⟩−⟨a−b|a−b⟩)/2`. The unit-phase participation score
`β cos(2π(q_i−q_j−φ_ij))` is therefore the pair quadrance with both advances zero and unit
radii. The helix is the lift that retains the winding a torus chart forgets; the full pair
receiver reads the periodic part and the axial part together.

[established-bounded; implemented-exact] The prototype at `13f8c734` realized the unit as
[`HelicalPairInteraction`](https://github.com/brandonrdug/holonics/blob/13f8c734/crates/holonics-cuda/src/holonic_interaction/helical.rs): it built
the checked contact and interaction from the pair, an explicit rate port `C`, PSD material, a
positive weight, a clock and frame/parameter units, and its unit-storage, zero-skew specialization
exposed both material-null and kinematic kernels. It and the
[serial chain](https://github.com/brandonrdug/holonics/blob/13f8c734/crates/holonics-cuda/src/holonic_chain/serial.rs) are the port sources for
`holonics::holon::contact` (rebuild step 1). The
[construction return](../research/records/2026-09-21_PAIR_CONTACT_SERIAL_KINEMATICS_AND_THE_RESIDENT_QUADRANCE_RETURN.md)
records the feature pullback, serial consumer and resident quadrance primitive.

[definition] The action relation below is typed by this unit. `z` is a family of helical pair
interactions with their media and incidence. `T_a` is their driven medium evolution composed
with phase stepping. A control `a` is a `Bu` drive word or a policy over receiver
faces. The same object appears in each supplied reference:

| Reference | The unit's operands |
|---|---|
| Rotor machine | Fixed material carried by a phase shift, `S⁻ᵈPSᵈ`; machine state on a discrete torus with stepping as a winding; forward passage, reflection and return through the producing operands, `A⁻¹FA`; n repetitions of fixed P at uniform steps give `(PS⁻¹)ⁿSⁿ`; input-dependent material retains its ordered word. The key is material, frame offset, initial configuration and a boundary involution. |
| Bombe | The menu is the incidence law stating which `(s,t)` interact. A closed menu path closes at a boundary port exactly when the known stage word fixes that port's boundary image. Inferring an initial configuration from pairwise loop closure, with the compatible boundary family left plural, is the training operation. |
| Articulated body | An ordered chain of `SituatedScrew`s; joint space is the torus chart of revolute phases with a line per prismatic parameter; Jacobian column i is `ScrewGenerator::rechart` of `ξ_i`; `reciprocal_pairing` is wrench–twist power; each contact is one unit; actuation is `Bu`; an observation is a receiver face. |
| Bilinear field chart | The prototype HNN's bilinear participation and `Δ_i=U_i q_i−q_r` are the circle×circle collapse of the pair receiver. The unit restores radius, advance, winding, second variation and contact material. |

[definition; agent-inferred] In an HNN the sites are navigators and context is their phase
state. An ordered source passage enters through a boundary port; occurrence k is received at
the navigators' phases after k admitted steps, so a declared linear source chart can accumulate
`m_g=Σ_k Ĝ_g(τ_g(k))⁻¹E_g(u_k)` and oriented pair moments at admitted offsets. These statistics
are retained with their source fibre and future-receiver descent law; scalar correlations do
not in general preserve source order.
A response position is a receiving phase, `y_j=ρ_R(Ĝ(j)q)`. The declared navigator count is independent
of source and response length; ingestion, output, exact bit growth and any separating remainder
retain their actual costs. Each navigator advances by its own declared or inferred rate;
the exterior codec unit does not define a native clock. A navigator with no participation at
the present phase retains its material, initial configuration, phase and winding under the
standing law below. The [winding guide](WINDING_CARRY_AND_PLACEMENT.md) states the general
objects this unit continues into (carry, lock address, conserved faces, cell holonomy and the
receiver-relative harmonic class, tube, continuation) with their checked laws. The prototype's
[machine contract](https://github.com/brandonrdug/holonics/blob/13f8c734/docs/plans/THE_ATHENA_ALPHA_CULTIVATES_GENERAL_CONVERSATION_THROUGH_NATIVE_CONTEXTUAL_TRANSPORT.md#situated-generator-and-receiving-composition)
is in history; rebuild step 4 rebuilds the machine in `holonics::hnn`.

[definition] Let z carry the interacting Holons, their material, incidence, clocks and relevant
environment, and let `F_o={z:O(z)=o}` be the compatible source family. Let a specify a complete
preparation/control law over a declared interval: a prescribed action word or a causal policy
from received observation histories to controls. `T_a` is the resulting admitted evolution,
including later contacts and feedback when supplied. It may retain the trajectory when the
receiver reads more than its endpoint. Its received consequence is

```text
Y_R(a,F_o) = { ρ_R(T_a z) : z ∈ F_o and a is admissible at z }.
```

Source observations, the requested consequence and the eventual observed consequence are
different operands. Inference finds a compatible a or family of a under the requested receiving
relation. Existential reachability, robust containment over the full source family and an
expected consequence under a supplied measure have different quantifiers. Robust control uses
one chosen law for every source retained, with its actions admissible along each resulting
trajectory; a feedback law can choose different controls from different received histories.
It cannot consult an unobserved source coordinate. The request supplies this scope;
output has no universal certainty gate. A communication acts on the receiving Holon's state,
so agreement of emitted strings alone does not establish agreement of receiving consequences.
The [prepared-transport construction](../research/records/2026-09-12_PREDICTION_IS_PREPARED_TRANSPORT_AND_RELEASE_IS_BOUNDARY_CURRENT.md)
already supplies this action-inference relation and its physical release balance.

[definition] A mode can be quiet at the current receiver and remain available to an admitted
future interaction. **Standing** retains the navigator/material, unresolved directions and
source conditions needed for that future; recall constructs a present face from this standing
and present context. `Foundation/Standing.lean::StandingLaw` requires every admitted future
reading to factor through what is retained. Its `MemoryLaw` reconstructs a new occurrence,
and its future separator distinguishes two currently equal faces. Neither a silent output nor
an interval without activation proves extinction. The normal material law `W H=B` is already a
reusable generating law; keeping a copy of its latest produced word is not what makes it one.

[proved-derived] In a linear chart, a dormant direction v has `ρv=0` but may satisfy
`ρ T_w v≠0` for an admitted later word w. It cannot be discarded by a representation promising
that later reading. For example, `ρ(x,h)=x` and `T_u(x,h)=(x+u h,h)` give the same present face
for `(0,1)` and `(0,-1)`, but different faces after `u=1`. This is the existing
[future-agreement/standing law](../lean/ElementaryHolonics/Foundation/Standing.lean),
with executable separators in `holonics::exact_linear::{ContextualFactorization,KernelModeReduction}`.

[definition] Continuing compression retains `D E=ρ` and `E_next T_a=U_a E` for its declared
action and receiver family. For state-dependent actions it also retains their domain/incidence:
a quotient that merges an enabled and a disabled action cannot decide applicability from the
quotient alone. Preserve that domain as a receiving predicate or retain the distinguishing
fibre. Closed navigator words then reuse the compressed action; a failed square returns its
interior or defect. A rational-linear closure or a fixed quadratic-moment closure does not
silently cover a changing nonlinear field word.

[definition] A functional mode's homeostasis concerns a declared recurring behavior, viable
region or return section during its engagement. It may be stationary, cyclic or nonperiodically
recurrent. Availability between engagements is a property of retained standing and its
admitted reactivation; it does not require the same current to circulate continuously.
Stability additionally concerns the response to perturbations under stated material and
driving conditions. A single return, exact phase arithmetic or a conserved norm alone does
not establish attraction, robustness or periodic closure.

[proved-derived] The medium (`holonics::holon::PortHolon::medium` with no active block;
`Transport/HolonicInteraction.port_storage_rate`, `Holon/Conformance.medium_rate_agrees`) gives a
concrete flux law. With fixed real `G=Gᵀ`, `Ωᵀ=−Ω`, `M_contact⪰0`, supplied input B u and
`q̇=(Ω−M_contact)Gq+B u`, the storage `V=½qᵀGq` obeys

```text
V̇ = −(Gq)ᵀ M_contact (Gq) + (Gq)ᵀ B u.
```

Changing G adds `½qᵀĠq`. For fixed positive definite G and zero input, nonincreasing V
controls the state norm; attraction additionally requires the invariant undamped modes to
be excluded. The library also admits indefinite G, where nonincreasing V alone does not
supply that stability conclusion.
A driven recurring mode can balance incoming work and dissipative/outgoing flux while
its environment accumulates heat. Return of a selected face need not return the environment.
The [physical interaction owners](HOLONIC_FLUID_CONSTRUCTION.md) retain the actual material
and entropy balance; invertible rearrangement of a probability population alone preserves
its Shannon entropy and supplies no heat-production law.

[definition] Knot tying and untying use configuration, admissible motions, contacts, clock
and material response together. Prime/unknot classes constrain topology; a closed nontrivial
knot cannot become an unknot by ambient isotopy. An open rope can be untied through its ends,
and physical release also depends on thickness, friction, load and actuation. The pair contact,
the serial chain (`Transport/{HolonicInteraction,HolonicChain,SerialScrewChain}`) and edit
rigidity (the prototype [`edit_rigidity.rs`](https://github.com/brandonrdug/holonics/blob/13f8c734/crates/holonics-cuda/src/edit_rigidity.rs)) carry
different parts of that calculation. The Rubik group's generators similarly act on an admitted
configuration fibre; a quotient reading does not determine the full state. Games with another
actor retain that actor's choices in the action relation. Lattice, crystal and quasicrystal charts apply when their
actual generators, incidence and periodic or aperiodic order are supplied.

### Motor release: the articulation chart and the simulator boundary

[project-postulate] Robotics and physical simulation are intended HNN capabilities (Brandon,
September 21). Their observation, actuation, clock and receiving contracts constrain the shared
navigator design now; this schedules no simulator run.

[definition] The object behind a simulator interface is the serial chain of helical pair
interactions, and its **motor chart is serial screw words**. An articulation is an ordered family
of `SituatedScrew`s: joint positions are their phases on the torus chart, with a line per
prismatic parameter; joint velocities are the parameter rates; the Jacobian's columns are
recharted Lie generators; each link–link or link–object contact is a pair contact whose slip map
is the pair's relative velocity; position, velocity or effort commands are the `Bu` drive on the
medium; `reciprocal_pairing` is wrench–twist power; control cadence and held commands are clock
material. A simulator's observation and action vectors are exterior charts of that object, as a
character is an exterior chart of a text port, and inferring the joint phases and drives that
produce a requested receiving face is the Bombe's configuration inference. Simulator floats stay
exterior readings: an imported float is the exact rational of the stored value, not the physical
one, and the chart declares its calibration and quantization residual. The inspected Isaac Sim
interface (source observation, action face, timing, reset, receiving consequence) is tabled in
[history](https://github.com/brandonrdug/holonics/blob/13f8c734/docs/HARDWARE_AND_MODALITY_BOUNDARIES.md#robotics-and-simulation-boundary). Owners:
Lean `Transport/SerialScrewChain`; Rust `holonics::geometry::{SituatedScrew,ScrewGenerator}`; the
chain's port source is the prototype [`serial.rs`](https://github.com/brandonrdug/holonics/blob/13f8c734/crates/holonics-cuda/src/holonic_chain/serial.rs).

## High-level Holonic Interactions

[definition] These are the operations used to formulate the model. They are abstracted
operations on Holons, with familiar vector/tensor realizations where applicable.

| Operation | Operational notation and effect | Current owner (`holonics` unless marked) |
|---|---|---|
| Superpose | α\|A⟩+β\|B⟩ in one compatible current space; phase combines before an intensity reading | exact current addition over `Rat` |
| Assemble | \|A⊕B⟩ keeps both port blocks; direct sum is distinct from adding them in one space | `holon::PortHolon` port blocks, `dirac` interconnection |
| Tensor-compose | \|A⊗B⟩ has components A^i B^j, retaining their axis roles and shared parameters | `exact_linear::BilinearProductCore`; Lean `Foundation/HolonTensorLens` |
| Interact | \|C⟩=𝓘_(K,Θ)(\|A⟩,\|B⟩); a bilinear chart is C^c=I^c_ab A^a B^b | `exact_linear::BilinearRealization::apply`; `law::HolonLaw::interact` |
| Receive/contract | ⟨r\|H⟩, or a partial tensor contraction leaving specified output axes | `factor_receiver`, `then_receiver`; `law::HolonLaw::receive` |
| Receive then emit | (\|B⟩⟨r\|)\|A⟩=⟨r\|A⟩\|B⟩; a rank-one operator, with an explicitly declared bra | factorized linear maps in `exact_linear` |
| Compose transports | Ĝ₂Ĝ₁\|H⟩; the output port of the first joins the input of the second | `then_receiver`, `then_fixed_right`; `generator::Transport` |
| Reflect/interfere | A constituted multiport operator acts on incoming and stored-current kets together | the Swing `2P_D−I`; Lean `Computation/HolonicConstitutiveCirculation`; device scattering in history |
| Attend / normalize participation | `Y_i=Σ_j a_ij U_ij V_j`, `a_ij=exp(s_ij)/Σ_k exp(s_ik)` on admitted contacts; a sigmoid is its binary restriction | `ratio::exponentiated::NormalizedKernel` forward, differential and pullback |
| Differentiate/pull back | δ\|H'⟩=D𝓘_H δ\|H⟩; a covector acts through (D𝓘_H)* on the same material | bilinear `differential`/`pullback`; `law::HolonLaw::pullback` |
| Generate | \|X(τ)⟩=𝓤_(Θ,K)^(τ←τ₀)(\|Ξ⟩;h), then ⟨r\|b_H(X(τ))⟩; the whole field evolves | `law::HolonLaw::advance`; Lean `Foundation/Holon.ofEvolution`; the field law is rebuild step 4 |
| Recur / change scale | F^∘n(\|H⟩), or a recursive family H=union_i F_i(H); retain its scale maps and branch constraints | `restriction` (scale square, tube, tower); Lean `Foundation/FractalPacking` |
| Apply an analytic generator | exp(tA), phase exp(iθ), logarithmic scale and Gamma recurrence with their actual domains and remainders | `generator::Clock` (Cayley step), `geometry` exact analysis |
| Encode/reopen | \|ξ⟩=Ê\|H⟩; a decoder and residual reconstruct the requested field/face, with Ê_next T=U Ê | `exact_linear::{KernelModeReduction,ContextualFactorization}`; Lean `Physics/ReflectedBoundaryMemory` |

[established-bounded; implemented-exact] The factorized bilinear library (`holonics::exact_linear`)
exposes `differential`, `pullback` and `precompose_ports`. It differentiates both input Holons through
the same retained factor core; the reverse returns input covectors before any metric/Riesz
identification. A finite change retains its separate mixed product. Port precomposition carries
explicit new-to-old maps and rederives the receiver family when their ranks change. These are
operations on the existing tensor realization, not a new catch-all object wrapper.
The [architecture diagram](HNN_FORMULA.md#reading-the-field-architecture-diagram) places them
inside the whole field with contact normalization, constituted circulation and joint decoding.

[definition] The existing mixed-feature interaction is explicit:

```text
|Φ(A,B)⟩ = |A⟩ ⊕ |B⟩ ⊕ |B⊗A⟩,
|C⟩ = M̂ |Φ(A,B)⟩.
```

It includes the two direct currents and their interaction term. This is an actual operator
signature, not a statement that all Holons are bilinear regressions. Higher interactions
compose suitable tensor/contraction operators or the model's nonlinear constitutive map.
The prototype realized it on the device (`advance_bilinear_contact`, `bilinear_features`, in
history); `holonics::exact_linear` exposes receiver composition and factor reuse. A helper around
a fitter would not establish a more general Holon algebra by itself.

[definition] The [connected tensor computation](HNN_FORMULA.md#one-connected-tensor-computation)
composes these interactions into heads, layers, current integration and geometric decoding.
It names the softmax covariance differential, sigmoid derivative, value/phase returns and
the implicit derivative of generation. A vector of amplitudes becomes a geometric output
through `A(x)=Σ_i ψ_i φ_i(x)` and a declared receiver such as an intensity level set. The
basis, contact material and reconstruction operator are part of this computational Holon;
the coefficient vector alone neither specifies them nor replaces them.

[definition] In an interaction diagram, an oriented line carries a ket or port index, a
propagator carries its transport, and a vertex carries the actual interaction tensor/map.
Joining lines contracts the matching axes. For two bilinear vertices,
`C^c=I^c_ab A^a B^b` and `E^e=J^e_cd C^c D^d` compose by contracting c. A geometric crossing
without contact is not a vertex. A loop can represent a constituted circulating/internal
mode. Physical Feynman amplitudes additionally use their field theory's propagators,
couplings and integration rule; diagram notation alone supplies no quantum dynamics.

[project-postulate] The library-facing specification uses this object/operator language.
The span and occurrence formalization below proves the joins behind it; callers should not
have to rebuild that foundation to apply a supported tensor interaction. Conversely,
renaming buffers or adding an optional-field wrapper does not supply an absent operator.

## Formal foundation behind the encapsulated object

[definition] The [four-paper analysis](../research/records/2026-09-14_TRANSFORMER_FIELDS_TROPICAL_CELLS_AND_FRACTAL_GENERATORS.md)
connects this operator algebra to field/reaction composition, finite-temperature routing,
recursive latent dynamics and fractal scale. For state-dependent interaction
`T(Psi)=Σ a_i(Psi) z_i(Psi)`, its derivative contains both `Σ a_i delta z_i` and
`Σ delta a_i z_i`. The routing field and transported tensor are both operands. A tropical
winner is an approximation receiver, not a replacement for that complete interaction.

[definition] Fractal dimension belongs to an identified scale family, not to tensor rank or
an intrinsic semantic capacity. Under contraction and separation, similarity dimension D
satisfies `Σ r_i^D=1`. A recursive description can stay short while its resolved geometry
and branch information grow. Transcendental functions specify these scale/phase/transport
laws; their constants are not substitutes for the operations that realize them.

[definition] `Foundation/Holon.lean` records the general carrier as
`H=(Ω,s:Ω→X,t:Ω→Y,ρ:Ω→F)`. This supplies its admissible realizations, oriented interfaces
and reading. Ω is a type, not an event archive. Operators can use their graphs; objects can
use identity passages. The notation above is the computational presentation of these
structured objects, not a new universal Hilbert-space assumption.

[established-bounded; source-inspected] `HolonTensorLens.lean` already defines heterogeneous
`PiTensorProduct` faces and tensor-valued Holons with the original interfaces and occurrence
population. Its coherent homogeneous slot-permutation theorem transports the full preimage.
Tensor application now reuses `Holon.mapReceiver`. Such a receiver can be an internal
computational interface; tensors are not confined to exterior codecs.

## Elementary characteristics and operators

[definition] The following is the shared operational synopsis. Physical, geometric and
probabilistic structure enters with its stated hypotheses, rather than being attributed to
every elementary carrier.

| Characteristic | Mathematical content | Formal / executable owner |
|---|---|---|
| Situated difference | Compare through actual frames/receivers; the difference can be a relation, current or geometry | `Foundation/Receiver`; `holonics::geometry` |
| Multiple faces | Equal measured values need not identify interiors; preimages can be implicit families | `Holon.PreimageFibre`; `holonics::restriction::fibre` |
| Oriented interfaces | The two sides of an operation have actual domain, codomain and transport | `AddressedPassage`; `holonics::port` |
| Serial composition | Join by `t₁(ω₁)=s₂(ω₂)`, then compose the operations | `Holon.comp`, `compPreimageFibreEquiv`; `holonics::structure::Chain` |
| Joint composition | Cartesian products introduce independent degrees of freedom; a diagonal shares one occurrence | `Holon.cartesian`, `diagonal`, `offDiagonal`; `holonics::exact_linear::JointBilinearSystem` |
| Identity and associativity | Identity does no transformation; associativity uses canonical reassociation of joined populations | addressed-span and relational composition |
| Frame/parameter transport | Move interfaces, occurrence and reading through commuting maps; a rebase is invertible at its scope | `Holon.Rebase`, `CausalNaturalHolon`; `holonics::geometry` frame transport |
| Geometry and incidence | Actual contact determines interaction; a projected crossing does not add an edge | `AddressedBoundary`; `holonics::complex`, `holonics::geometry::projection` crossings |
| Constitutive response | Material relates arriving current, stored modes, geometry and outgoing field | `CoupledIncidence`, `PortEnergyHeat`; `holonics::element` |
| Differential and adjoint | Differentiate the transformation, including material/chart motion; compose its adjoints | `Holon/Law.pullback_law`; `HolonLaw::pullback`, bilinear `pullback` |
| Recursion and generation | Evolve a field/family and read its generated boundary at any nested scope | `Holon.ofEvolution`; `HolonLaw::advance` |
| Exact inference | Solve for coefficients, factors, modes or compatible realizations | exact preimage/factorization; `holonics::exact_linear` |
| Compression/refinement | `E_next T=U E`, `D E=ρ`, or an explicit transported error; retain newly relevant modes | `ReceiverHistoryCompression`, `ReflectedBoundaryMemory`; `holonics::exact_linear::KernelModeReduction` |
| Conservation/dissipation | A supplied law accounts for flux, storage and heat | `BoundaryHolon`, `Holon/Law`; `holonics::law::EnergyBalance` |
| Information and measure | Declared measures yield entropy/loss; oriented current precedes scalar readings | `InformationDifference`, `ReceiverCodeCost`; `holonics::ratio::surprisal` |
| Scale and locality | Restriction/prolongation and boundary summaries relate grains and local clocks | `WorldTube`, `ContinuingTower`; `holonics::restriction` |
| Continuing computation | Executable state, factors and live comparisons suffice where their law closes | `Foundation/Standing`; `holonics::receiver::standing`; the field is rebuild step 4 |

[definition] The operations these characteristics become are defined in the
[operator contract](ELEMENTARY_OBJECTS.md#operator-contract), which gives each operation's current
and target owner. That contract lists the ratio arithmetic (`div_rem`, `residue`, `invert` with
its nonunit fibre, `lift`, `jet`), geometric transport and pair/tube charts, the Holon's
`advance`/`interconnect -> Holarchy`/`contact`/`continue`/`restrict`/`depose`/`pullback`, joint
reception returning both participants and a receipt, and the Holarchy's receiver-relative `view`
and `count`. The table above names the formal and executable owners they come from.

[definition] A gradient, metric, mass, distribution, tensor rank or reversible decoder is
additional mathematical structure. Requiring every Holon to contain all of them confuses the
general object with a physical chart. Conversely, calling a vector a Holon does not supply
those properties. An operator must carry what its equation uses.

### Algebra and calculus in those charts

[definition] The familiar elementary operations retain their exact domains:

- On a linear current chart, `T(a x+b y)=a Tx+b Ty`. A nonlinear reaction does not inherit
  this law merely because its inputs are tensors.
- A tensor operator acts by `(A⊗B)(x⊗y)=Ax⊗By`; contraction uses the declared dual pairing.
  Reindexing slots and changing bases transport the operator and its dual axes together.
  The occurrence constraints still decide whether the two inputs are independent.
- Complex current addition precedes intensity: `|a+b|²=|a|²+|b|²+2 Re(a conjugate(b))`.
  Phase and interference cannot be recovered from component magnitudes alone.
- For differentiable composition, `D(g∘f)_x=Dg_(f(x)) Df_x`; its adjoint reverses the
  operator order. Material and frame dependence add their own differential terms.
- Incidence with `∂∂=0` gives cancellation of matched internal boundaries and the associated
  Stokes relation. A constitutive law supplies current, storage and energy; topology alone
  supplies no numerical conductance.
- A constituted flow composes by its evolution law. Noncommuting operators retain their
  order and splitting defect. Spectral/modal factorization and exact preimage solving are
  representations of those operations, rather than labels that replace them.

[established-bounded; source-inspected] Tensor lenses (`Foundation/HolonTensorLens`), exact linear
algebra (`holonics::exact_linear`) and the boundary operators supply these constructions in
their declared source families. The summary specifies their use in one Holon algebra; it
does not assert that all nonlinear operators have exact finite modal closures.

## Generation is an operation on Holons

[definition] `Holon.ofEvolution prepare evolve read` constructs a generated section from an
admissible latent/input parameter, an evolution and a reading. The latent can be an image,
acoustic field, geometric configuration or joint symbolic section. There is no output-token
order in this definition. A noise field is one initial chart; missing information and a
measured zero are different conditions.

[proved-derived; formal-checked] `ofEvolution_receive_eq_encoded` proves that generation in
an encoded state returns the same face when evolution and decoder commute.
`ofEvolutionCompOccurrenceEquiv` identifies the joined occurrences of two deterministic
refinements with the original seed population: their intermediate state is determined by
the first map. Neither result requires a trajectory archive or independently chosen output
marginals. Both extend the existing Holon owner.

[definition] `mapReceiver` changes the reading while retaining the same ports and occurrence
population. It can be noninjective; it is not automatically a rebase. Image pixels, acoustic
samples and text can read an evolving object without defining its interior dynamics. The
[model formula](HNN_FORMULA.md#generation-as-field-refinement-and-boundary-radiation)
specifies the generated field and its boundary coupling.

<a id="equation-extraction"></a>

## Equation extraction

[definition] **Equation extraction** reads a foreign realization's operators and coefficients as
the element relations, interconnection and navigators of a native Holon, so that the extracted
equations are native objects. It compresses a foreign realization into navigators and element
relations under a declared family of exposures ("Soulkiller" is a name only;
[history](https://github.com/brandonrdug/holonics/blob/13f8c734/docs/SOULKILLER.md)). Its passage has six steps:

1. **Intake:** keep the tensor codewords, configuration, graph declarations and source lineage.
2. **Realization recovery:** identify the executable mathematical operation, with its state and
   chronology, through an adapter for that architecture.
3. **Excitation:** run declared occurrences and read the chosen receiver family over their aeons.
4. **Intervention:** withdraw declared populations and observe which consequences change.
5. **Identification:** form classes from complete signatures over that declared family.
6. **Native return:** executable restricted classes with an exhibited remainder, a separate cold
   witness and explicit insufficiency.

[definition] Each architecture's adapter carries its own obligations over one native operation
calculus ([SSM and diffusion charts](HNN_FORMULA.md#state-space-convolution-and-diffusion-are-one-realization)).
- A **Transformer** adapter accounts for its contractions, nonlinearities, causal contacts and state.
- A **diffusion** adapter also carries the iterative schedule, the conditioning and any declared
  stochastic source, as exterior realization data.
- An **SSM** adapter retains the state transition, the input and output maps and the
  initialization and reset law.

Identifying a tensor shape, or calling every recurrence diffusion, discharges none of these.
Reading a file or recovering an operator is not the excitation-founded return, and unexcited
capability stays explicit. [conditional] A family is extracted when its source operation is
realized by admitted native local laws and the declared receiver consequences factor through the
returned body, with defects and insufficiency retained; an unsupported local reaction needs its
actual construction, not a universal fallback executor. The prototype recovered a configured Gemma
text realization, 1,275 operations over 719 coefficient populations
([history](https://github.com/brandonrdug/holonics/tree/13f8c734/crates/holonics-cuda/src/holonic_intelligence)). Rebuild step 6 rebuilds extraction
on the library; foreign forward graphs and Q/K/V caches are not ported whole.

## What exists now

[established-bounded; source-inspected] Since the September 24 reset the computational Holon has
these code owners:
- `crates/holonics`, over `Rat` throughout: the Holon law and its facets (`holon`, `law`, `port`,
  `dirac`, `element`, `complex`, `generator`, `restriction`, `deposition`, `reaction`,
  `conformance`); exact algebra (`exact_linear` with the factorized bilinear operators and kernel
  modes, `inertia`, `rational_polynomial`, `prime_image_algebra`); `ratio`; `geometry` (frames,
  screws and pairs, winding, projection, receiver atlases); `receiver` (release, standing, causal
  chord); and `structure` (`Face`, chains, crossings, atlases).
- `crates/holonics-cuda`: the CUDA driver only. The resident HNN is rebuilt there after its law
  exists in `holonics` (rebuild steps 4–5).
- The prototype's resident sections, operative field, coupled body and its wrappers are in
  history ([`hnn`](https://github.com/brandonrdug/holonics/tree/13f8c734/crates/holonics-cuda/src/hnn),
  [`native_ecology`](https://github.com/brandonrdug/holonics/tree/13f8c734/crates/holonics-cuda/src/native_ecology)). Their laws are stated in
  [HNN_FORMULA](HNN_FORMULA.md), and they are ported one law at a time under
  [THE_REBUILD](plans/THE_REBUILD.md).

[definition] `structure::Face::map_scalar` need not be injective or reversible: a constant map
refutes reversibility whenever the retained relation does not distinguish the prior scalars, and
reconstruction needs an actual decoder. `Face::taken` stores two supplied values; it proves no
projection equation between them.

[project-postulate] The primitive contract for HNN assembly is the complete situated operation.
Share, factor and rechart numerical sections while carrying the interface and law the consuming
operation requires, and consolidate those joins in the model owner. A universal record of
unrelated optional fields would not establish them; `holonics::Holon` is the law and its ports,
not such a record. A wire or display result that omits internal incidence is an
exterior projection; an algorithm that needs the omitted structure consumes its owner.

## Recall and communicating ecologies

[interpretation] The user's recollection account motivates constructive recall: a cue
activates retained modes, which generate a partial field; attended discrepancies direct
further refinement. It does not require a stored screenshot. Exact replay, plausible
completion and retrieval of a historical detail are different receivers. An unresolved
region must not become a falsely certain zero or detail. This is a design interpretation,
not a measurement of the user's neurological memory.

[proved-derived] Causal influence alone does not give an invertible decoder. The existing
`ReceiverTransformer.excludesInsufficiency` states the precise limit: if two compatible
interiors share the available cue but differ in the requested detail, the cue alone cannot
determine that detail. Further interaction can supply a separator. This gives gap-directed
navigation a constructive task without assuming universal exact recoverability.

[interpretation] Crow gaze, calls, posture and movement can expose internal activity without
a deliberate message. The July 21 laboratory account already describes its propagation
through light, sound and other birds' response. The cited experiment establishes social
learning of dangerous human faces through observed behavior; gaze alone as a sufficient
teaching signal is a further hypothesis, not that experiment's result.

[definition] What one subregion generates can stimulate another region of the same organism;
the enclosing system can expose a further exterior face. Causal coupling does not wait for
a linguistic instruction or consent flag. Avoidance, shielding and inhibition alter actual
pathways/responses; they do not undo a coupling that already occurred. Having been affected
does not imply a permanent locally recoverable record.

[definition] Boundary signals constrain compatible interiors without necessarily identifying
one. An event horizon adds an accessibility restriction: outgoing classical signals from
behind it are not an available channel. The predecessor's hourglass and boundary/interior
records inform this relation; historical mind/black-hole slogans supply no new physical law.

[definition] The [illustrated synopsis](../research/papers/source/papers/elementary-holon-generation/main.typ)
renders this specification, the generation formula and a reusable exact modal construction.
It owns no separate model architecture and makes no new native capability claim by appearance.
