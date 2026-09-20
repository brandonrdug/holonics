# The machine: what HNN is, in its own geometry

[definition] Read this first. It states what is being built, why its geometry is the machine
learning, and where each part lives. The mathematics in this repository is the implementation
specification of the engine; none of it is background. [HOLON](HOLON.md) and
[HNN_FORMULA](HNN_FORMULA.md) hold the full equations, [HELICAL_GEOMETRY](HELICAL_GEOMETRY.md)
the elementary pair, [ARCHITECTURE_MAP](ARCHITECTURE_MAP.md) every owner.

## The object

[project-postulate] An HNN is one continuing field: **a chain of interlinked tori**. Each torus
carries circulating phase modes; neighbouring tori overlap, and their shared volume is a
**contact face** where currents meet with friction, exchange energy and deposit heat. A **Holon**
`|H⟩_F` is this field in a declared frame: simultaneously a whole and a part, at every grain.
Heads, layers, levels and time steps are charts of the one object. A **receiver** is another
participating Holon with its own moving frame; every measurement, readout, stored file and
displayed image is a face it receives.

## Why this geometry is the learning

| Machine-learning operation | What it is in the object | Classical restriction it contains |
|---|---|---|
| **Embedding** | An occurrence enters as amplitude and phase on the torus chain: a complex channel is a circle with a radius, several commuting modes are a torus `Tⁿ`, and which tori link is the incidence `K` | Rotary position embedding rotates query/key pairs by position-dependent phases: a point on a torus. Fourier features and complex-valued networks are the same chart |
| **Sequence, position, time** | A **helix**: a phase advancing along an axis, the screw generator `ξ=(ω,v)` acting on a configuration. A sequence of text, a strand, a signal and a trajectory are helical orbits | A fixed shift is the pure translation (`ω=0`: convolution, SSM step); a pure rotation is the periodic mode; both are collapses of one helix |
| **Attention** | The situated phase comparison on admitted contact, `s_ij=β cos 2π(q_i−q_j−φ_ij)` with connection `φ`, normalized over the contacts a torus actually has: `a=softmax(s)`. The **pair of helices** and its quadrance `Q=⟨Δ|Δ⟩` is its elementary trigonometry | `Re⟨Q_i,K_j⟩` is the cosine of a phase difference weighted by amplitudes. Softmax ranges over contact, never all-to-all |
| **Learning** | The variation of that interaction: `δT=Σ a δ(UΨ)+Σ δa UΨ`, returned through the contact and the material by the paired adjoint; the contact's dissipated energy is the measured difference | Backpropagation through attention, including `J=diag(a)−aaᵀ`; normal equations where the law is linear |
| **Generation** | Refinement of the whole field, `x(τ)`, released at a boundary: `y=ρ_F b_H(x)`. The refinement coordinate is never an output-token index | Diffusion over a whole image or waveform; an implicit solve `(I−λB)x*=(1−λ)h` |
| **Decoding** | Integration of the boundary along its cycles by a receiver: periods and amplitudes in the toroidal basis, `A(x)=Σψ_iφ_i(x)`. Text, image and sound are receiving faces of one boundary | A readout matrix is the receiver with a fixed frame |
| **Compression** | Commensurate windings close: a `(p,q)` torus knot is a finite recurrence, and the identities among faces are what need not be stored. `E_next T=U E` keeps exactly what future receivers can separate | Low-rank and modal reduction; key/value class aggregation `(m_c,p_c)` |
| **Exactness** | A constant is a constraint mode (`−1=e^{iπ}`, a period, a winding); a float is one face of it. Phases are rational or algebraic, so cycles close exactly | Floating point is an exterior presentation |
| **Depth, scale, recursion** | The recurrence of the torus map: first-arrival populations and preimage families carry fractal geometry with a fixed number of state axes. A tube is the object over time, a tower one frame of it, a staircase its passage between grains, a neck where its section converges | A layer stack is one execution chart of the recurrence |
| **Hardware** | Overlapping domains' shared cells are co-present: they commute, so they occupy the card's lanes together under the cover, partition and launch laws | A batch dimension |

[definition] Hodge (which cycles are realized), RH (where spectral landmarks sit), complex Euler
and Navier–Stokes (how flux transports with and without dissipation) and Iwasawa theory (the tower
of grains) are developed because the engine executes exactly these objects: cycle classes,
spectral placement, flux and levels. Their conjectures are side questions; their objects are parts.

## Where each part lives

| Part | Formal | Rust | Native HNN (resident on the card) |
|---|---|---|---|
| Linked toroidal carrier, shared contact cells | `Millennium/HolonicTorusKnots`, `Foundation/Holon`, `HolonTensorLens` | `simplicial`, `algebraic::GradedCausalComplex`, `analytic_field`, `traversible_chain::BandReading`; reference [`intrinsic_holonic_flow`](../research/experiments/intrinsic_holonic_flow/README.md) | **Not yet.** The native carrier is a generic section with no toroidal incidence |
| Helix and helical pair | `Geometry/ScrewGeometry`, `TwoSidedIdentityAtlas` | `relational_geometry::screw`, `identity_atlas` | **Not yet** |
| Phase attention and its variation | `Computation/HolonicAdjointNormalization`, `AttentionModeCompression` | `exponentiated_ratio::transport::NormalizedKernel`; reference [`connected_holonic_field`](../research/experiments/connected_holonic_field/README.md) | Row-sectioned normalized receiver, pullback and condition covector (Wave 11); not yet composed on a toroidal incidence |
| Contact face, friction, energy | `Physics/PhaseContactPassage`, `ReceiverStressEnergy`, `CoupledIncidence` | `contact_receiver_faces`, `holonic_interaction`, `junction_law` | The constitutive field's D-reflection and paired adjoint |
| Whole-field refinement and release | `Foundation/Holon.ofEvolution`, `Transport/ReceiverPotential` | `receiver_release`, `continuing_tube` | One reaction-plus-reflection pass; the re-entry port exists |
| Receiver and decoding | `Foundation/Receiver`, `Transport/ChangingReceiver` | `receiver_atlas`, [receiving Holon](RECEIVER_HOLARCHY.md) | Unit-basis symbol selection: a text codec, the first receiver only |
| Closure, identities, compression | `Foundation/ReceiverHistoryCompression`, `GeneratorModeQuotient`, `Millennium/{LandmarksAndModuli,Farey}`, `HolonicQuadraticMomentCondensation` | `exact_linear::{factor_receiver,kernel_modes}`, `receiver_history_compression`, `winding_inertia` | `internal_mode`, `recurrent_condensation`; not bound to the session |
| Co-present cells on the card | `Foundation/{SectionLayout,DeviceLaunchLaw}` | `hardware_cover`, `section_partition`, `holonic-mount::{section_layout,launch_law}` | Not called by the field path (#61) |

[established-bounded; source-inspected] At `ee5a4b50` no file under `crates/holonics-hna/src`,
`crates/holonic-engine/src/native_ecology` or `crates/holonic-engine/kernels` names a torus, helix
or knot. The object is realized in Lean, in `relational-geometry` and in the two exterior reference
experiments. **That gap is the work.** Bringing the object onto the resident body is what #17 and
#61 do; the native code being generic is never evidence that the geometry is unrelated to it.

## How to read a task

[project-postulate] Every task realizes or serves a part of this object. Before planning, say
which part, which row above it extends, and what its native column becomes. A description in
which the geometry does not appear has lost the object.
