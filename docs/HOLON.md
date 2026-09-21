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
A nonlinear generator is a composed map; its parameters and local derivatives have their
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
positive mobility produce diffusion and heat. Native graph scattering is precisely Swing
about its constituted projection; the object therefore connects to the primitive operation
without replacing the field by its displayed coefficient vector.

[definition] The [receiving Holon](RECEIVER_HOLARCHY.md) completes this distinction:
`ρ_R` is its receiving operation, while H_R carries the frame, material, current and internal
state that determine that operation. A continuous section is not intrinsically a discrete
sample; samples and coefficients present restrictions of its generating relation. Source and
receiver can both change, so their joint differential includes the receiver's motion/material
return. The first-arrival/fractal sets, entropy partitions and compression family are defined
through those actual receiving operations. A physical drive or monitor instantiates the same
interaction/encoding pattern with its own material laws.

## Situated generator inference, dormant modes and action

[project-postulate] Text, acoustic, optical, mathematical and motor conduct use this same
construction: infer or reuse an admissible generating relation and release its consequence
through a participating receiver. Their media supply actual interaction laws and charts.
The September 21 [source synthesis](../research/records/2026-09-21_SITUATED_GENERATORS_RETAIN_MODES_AND_RELEASE_ACTION.md)
connects the rotor/Bombe comparison, simulator interfaces and existing source owners.
“Key-like” describes applicability to a situated receiving constraint; it names neither a
secret, a universal inverse nor a new computational primitive.

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
future interaction. **Standing** retains the generator/material, unresolved directions and
source conditions needed for that future; recall constructs a present face from this standing
and present context. `Foundation/Standing.lean::StandingLaw` requires every admitted future
reading to factor through what is retained. Its `MemoryLaw` reconstructs a new occurrence,
and its future separator distinguishes two currently equal faces. Neither a silent output nor
an interval without activation proves extinction. The native normal material is already a
reusable generating law; keeping a copy of its latest produced word is not what makes it one.

[proved-derived] In a linear chart, a dormant direction v has `ρv=0` but may satisfy
`ρ T_w v≠0` for an admitted later word w. It cannot be discarded by a representation promising
that later reading. For example, `ρ(x,h)=x` and `T_u(x,h)=(x+u h,h)` give the same present face
for `(0,1)` and `(0,-1)`, but different faces after `u=1`. This is the existing
[future-agreement/standing law](../formal/elementary-holonics/ElementaryHolonics/Foundation/Standing.lean),
with executable separators in `exact_linear/contextual.rs` and `kernel_modes.rs`.

[definition] Continuing compression retains `D E=ρ` and `E_next T_a=U_a E` for its declared
action and receiver family. For state-dependent actions it also retains their domain/incidence:
a quotient that merges an enabled and a disabled action cannot decide applicability from the
quotient alone. Preserve that domain as a receiving predicate or retain the distinguishing
fibre. Closed generator words then reuse the compressed action; a failed square returns its
interior or defect. A rational-linear closure or a fixed quadratic-moment closure does not
silently cover a changing nonlinear field word.

[definition] A functional mode's homeostasis concerns a declared recurring behavior, viable
region or return section during its engagement. It may be stationary, cyclic or nonperiodically
recurrent. Availability between engagements is a property of retained standing and its
admitted reactivation; it does not require the same current to circulate continuously.
Stability additionally concerns the response to perturbations under stated material and
driving conditions. A single return, exact phase arithmetic or a conserved norm alone does
not establish attraction, robustness or periodic closure.

[proved-derived] The existing `holonic_interaction::Medium` gives a concrete flux law. With
fixed real `G=Gᵀ`, `Ωᵀ=−Ω`, `M_contact⪰0`, supplied input B u and
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
and physical release also depends on thickness, friction, load and actuation. The
`holonic_interaction`, `edit_rigidity` and `holonic_chain` owners carry different parts of that
calculation. Rubik generators similarly act on an admitted configuration fibre; a quotient
reading does not determine the full state. Games with another actor retain that actor's
choices in the action relation. Lattice, crystal and quasicrystal charts apply when their
actual generators, incidence and periodic or aperiodic order are supplied.

## High-level Holonic Interactions

[definition] These are the operations used to formulate the model. They are abstracted
operations on Holons, with familiar vector/tensor realizations where applicable.

| Operation | Operational notation and effect | Current executable construction |
|---|---|---|
| Superpose | α\|A⟩+β\|B⟩ in one compatible current space; phase combines before an intensity reading | Exact/current addition and resident field transport |
| Assemble | \|A⊕B⟩ keeps both port blocks; direct sum is distinct from adding them in one space | Resident sections and paired current/source owners |
| Tensor-compose | \|A⊗B⟩ has components A^i B^j, retaining their axis roles and shared parameters | `ResidentBilinearFeatures`, exact bilinear product cores |
| Interact | \|C⟩=𝓘_(K,Θ)(\|A⟩,\|B⟩); a bilinear chart is C^c=I^c_ab A^a B^b | `BilinearRealization::apply`, resident bilinear contact and constituted scattering |
| Receive/contract | ⟨r\|H⟩, or a partial tensor contraction leaving specified output axes | `factor_receiver`, `then_receiver`, resident image/readout |
| Receive then emit | (\|B⟩⟨r\|)\|A⟩=⟨r\|A⟩\|B⟩; a rank-one operator, with an explicitly declared bra | Factorized linear maps and native material-response factors |
| Compose transports | Ĝ₂Ĝ₁\|H⟩; the output port of the first joins the input of the second | `then_receiver`, `then_fixed_right`, resident relation images |
| Reflect/interfere | A constituted multiport operator acts on incoming and stored-current kets together | Operative field scattering, phase transport and internal modes |
| Attend / normalize participation | `Y_i=Σ_j a_ij U_ij V_j`, `a_ij=exp(s_ij)/Σ_k exp(s_ik)` on admitted contacts; a sigmoid is its binary restriction | Resident normalized/contact operators; exact `NormalizedKernel` forward, differential and pullback |
| Differentiate/pull back | δ\|H'⟩=D𝓘_H δ\|H⟩; a covector acts through (D𝓘_H)* on the same material | Operative tangent/adjoint and normal/preimage laws |
| Generate | \|X(τ)⟩=𝓤_(Θ,K)^(τ←τ₀)(\|Ξ⟩;h), then ⟨r\|b_H(X(τ))⟩; the whole field evolves | Joint native wave/family operations; the general field consumer is the active assembly |
| Recur / change scale | F^∘n(\|H⟩), or a recursive family H=union_i F_i(H); retain its scale maps and branch constraints | Fractal restriction/packing, generator words and recurrence owners |
| Apply an analytic generator | exp(tA), phase exp(iθ), logarithmic scale and Gamma recurrence with their actual domains and remainders | Existing exact expressions, phase/clock and analytic block generators |
| Encode/reopen | \|ξ⟩=Ê\|H⟩; a decoder and residual reconstruct the requested field/face, with Ê_next T=U Ê | Kernel-mode factorization, receiver descent and boundary memory |

[established-bounded; implemented-exact] The factorized bilinear library now exposes
`differential`, `pullback` and `precompose_ports`. It differentiates both input Holons through
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
The native code already exposes `advance_bilinear_contact` and `bilinear_features`;
mathematical operator realizations expose receiver composition and factor reuse. A helper
around the fitter would not establish a more general Holon algebra by itself.

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
| Situated difference | Compare through actual frames/receivers; the difference can be a relation, current or geometry | `Foundation/Receiver`; `relational-geometry` |
| Multiple faces | Equal measured values need not identify interiors; preimages can be implicit families | `Holon.PreimageFibre`; resident relation families |
| Oriented interfaces | The two sides of an operation have actual domain, codomain and transport | `AddressedPassage`; native current boundaries |
| Serial composition | Join by `t₁(ω₁)=s₂(ω₂)`, then compose the operations | `Holon.comp`, `compPreimageFibreEquiv`; resident images/pullbacks |
| Joint composition | Cartesian products introduce independent degrees of freedom; a diagonal shares one occurrence | `Holon.cartesian`, `diagonal`, `offDiagonal`; joint native source families |
| Identity and associativity | Identity does no transformation; associativity uses canonical reassociation of joined populations | addressed-span and relational composition |
| Frame/parameter transport | Move interfaces, occurrence and reading through commuting maps; a rebase is invertible at its scope | `Holon.Rebase`, `CausalNaturalHolon`; frame transport |
| Geometry and incidence | Actual contact determines interaction; a projected crossing does not add an edge | `AddressedBoundary`; causal contact propagation |
| Constitutive response | Material relates arriving current, stored modes, geometry and outgoing field | `CoupledIncidence`, `PortEnergyHeat`; scattering and normal material |
| Differential and adjoint | Differentiate the transformation, including material/chart motion; compose its adjoints | constitutive/normalization laws; operative response |
| Recursion and generation | Evolve a field/family and read its generated boundary at any nested scope | `Holon.ofEvolution`; joint native generation |
| Exact inference | Solve for coefficients, factors, modes or compatible realizations | exact preimage/factorization; native condition and material laws |
| Compression/refinement | `E_next T=U E`, `D E=ρ`, or an explicit transported error; retain newly relevant modes | joint/future receiver descent; kernel modes, boundary memory |
| Conservation/dissipation | A supplied law accounts for flux, storage and heat | `BoundaryHolon`; physical storage and flux owners |
| Information and measure | Declared measures yield entropy/loss; oriented current precedes scalar readings | information difference, attention summaries and code costs |
| Scale and locality | Restriction/prolongation and boundary summaries relate grains and local clocks | world-tube, scale and constitutive transport |
| Continuing computation | Executable state, factors and live comparisons suffice where their law closes | internal modes, normal moments, coupled body and rest |

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

[established-bounded; source-inspected] Tensor lenses, exact linear algebra, complex field
currents, material response and boundary operators already supply these constructions in
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

## What the active Rust code realizes

[established-bounded; source-inspected] The native code uses structured computational objects
beyond raw arrays. Their structure is distributed among numerical sections and their owners:

- `ResidentSection` is resident storage. `ResidentConstitutiveCurrent` is a borrowed coordinate
  view with extent and numeric representation; it is not a complete autonomous Holon.
- `ResidentConstitutiveFibre` and section/family objects bind paired domains, owner identity,
  compatible alternatives and image/pullback operations.
- `NativeCurrentBoundary`, `NativeCurrentIncidence` and `NativeCurrentFrame` supply interfaces
  and transport. The operative field supplies material, internal current and contact dynamics.
- `NativeCoupledBody` owns joint affine/dependent generation. `NativeSession` wraps a narrower
  phase ecology; `NativeMathematicalSession` manages operators and their products. The
  [library guide](RUST_FRAMEWORK.md) distinguishes these consumers.

[established-bounded; source-inspected] Holon structure has not simply disappeared. However,
the narrow phase session does not expose all field operations, and some wire results omit
internal incidence/rechart receipts. Those are exterior projections. A native algorithm that
needs the omitted structure must consume its actual owner, rather than reconstructing it
from JSON values. Add an inspection receipt only for a real inspection requirement; receipt
collections do not assemble the model.

[established-bounded; source-inspected] `Face::map_scalar` previously claimed that an arbitrary
scalar transformation was reversible because a relation remained attached. A constant map
disproves that claim whenever the retained relation does not distinguish the prior scalars.
Its documentation now states the actual contract. `Face::taken` stores two supplied values;
it does not prove a projection equation between them. Runtime behavior is unchanged.

[project-postulate] The primitive contract for HNN assembly is the complete situated
operation, realized by existing owners. Share, factor and rechart numerical sections while
carrying the interface and law required by the consuming operation. Consolidate those joins
in the selected model owner. Another universal record of unrelated optional fields would
not establish them, and the absence of a single `Holon` struct does not prove their absence.

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
