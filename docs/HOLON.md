# The computational Holon

## The object and its notation

[definition] Write a Holon in a declared tensor chart as **|H⟩_F**. H carries the Holonic
entity mark (the recovered wavy underline); F specifies its frame, port/axis roles and
pairing. The notation packages the object so it can be manipulated without expanding its
construction record at every use. The existing Dirac convention is in
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
