# THE ALGORITHM IS A CAUSAL DIAGRAM; THE HARDWARE REALIZES ITS RESOURCE CURRENT

**2026-07-26 · HOLONIC COMPUTER SCIENCE FOUNDATION / EXACT RECEIVER ENGINE CPU
REFERENCE BUILT / CATEGORY + EVENT + RESOURCE + WORLD + VISIBILITY CUT / NO FLOAT /
NO BEVY / NO GRAPHICS OR PHYSICS FRAMEWORK / NO VULKAN BACKEND YET**

Exact bounded result:
[`HOLONIC EXACT RECEIVER ENGINE 01`](../observations/holonic-exact-receiver-engine-01/RESULTS.md).

Current Eros machine-learning pickup:
[`THE TEXT ENTERS AS ONE CAUSAL EVENT`](2026-07-26_THE_TEXT_ENTERS_AS_ONE_CAUSAL_EVENT_THE_CURRENT_ECOLOGY_IS_THE_PICKUP.md).

## 1. Present question and answer

The question was not how to redraw the rejected Bevy scene. It was:

> What is an algorithm, data structure, programming object, hardware execution, and
> first-person graphic/physical observation when none of them is permitted an
> absolute frame?

The answer is a receiver-indexed relation whose first implementation exposed
four levels:

1. an **abstract boundary category** states which transformations can compose;
2. an **unfolded causal diagram** states which actual event occurrences precede or
   coexist with which others;
3. a **standing incidence structure** affords the traversals used by the algorithm; and
4. a **hardware realization** embodies those events as storage, transport,
   synchronization, switching, and dissipation on one physical substrate.

The same abstract algorithm can have many physical realizations. The same physical
instruction trace can be interpreted under different abstract boundaries. Neither
side alone is the whole computation.

The later category-theory audit records three additional structures which this
first source cut has not yet embodied:

5. an **interaction doctrine** states how juxtaposed open systems actually
   meet;
6. a **parameter enrichment** states which controls, occurrences, and
   resources may be copied, retained, or discarded; and
7. a **receiver fibration and observation sheaf** state how local ecologies
   transport and when their compatible sections assemble over one bounded
   region.

Exact authority:
[`THE GLOBAL IS THE TRANSPORTED LOCAL`](2026-07-26_THE_GLOBAL_IS_THE_TRANSPORTED_LOCAL_THE_INTERACTION_SELECTS_THE_REALISATION.md).

In the current holonic notation, an algorithmic world law participates in

\[
\Lambda_F(Q\otimes A\otimes L)\longrightarrow(P,\pi_B).
\]

Here \(Q/F\) gives the present question and frame, \(A\) is the standing incidence
affording continuation, \(L\) is the actual current population with its native
chronology, \(P\) is the complete emitted successor placement, and \(\pi_B\) is
receiver testimony. An algorithm is not a new subsystem between these terms. It is
the lawful causal relation by which this world carries the event.

## 2. Algorithms are causal diagrams, not output functions alone

### Definition 2.1 — situated algorithm

A situated algorithm is

\[
\mathcal A=(\Theta,I,S,O,\iota,\delta,\omega,\rho),
\]

where \(\Theta\) is the parameter boundary, \(I,S,O\) are input, standing, and output
boundaries, \(\iota\) initializes standing, \(\delta\) is one lawful transition,
\(\omega\) exposes a result, and \(\rho\) states refusal or completion.

The extensional map \(I\to O\), when it exists, is only one receiver face. It erases
intermediate standing, causal partial order, refusal, memory traffic,
synchronization, source/returned consequences, and alternative paths that happen
to expose the same output.

### Definition 2.2 — occurrence and recurrence

An event occurrence is singular in its causal position. A law may recur. A loop
therefore does not make causal time circular. Its runtime unfolding is

\[
e_0\prec e_1\prec\cdots\prec e_n,
\qquad
\operatorname{law}(e_i)=\operatorname{law}(e_j)
\]

for some \(i\ne j\). Cycles may remain in standing data, control law, or returned
world relation without fabricating a causal cycle among completed occurrences.

### Definition 2.3 — co-presence

Two events are co-present when the causal diagram contains neither
\(e_i\prec e_j\) nor \(e_j\prec e_i\). An executor may serialize them for physical
reasons. That serialization is not promoted to logical causality.

The new `CausalDiagram` computes deterministic topological layers from declared
precedence and refuses causal cycles.

## 3. Category theory supplies composition, not a universal classifier

Let \(\mathcal C\) contain local boundary types as objects and lawful
transformations as arrows. A path

\[
X_0\xrightarrow{f_1}X_1\xrightarrow{f_2}\cdots\xrightarrow{f_n}X_n
\]

exists only when adjacent codomain and domain agree. The implementation now checks
this explicitly in `CategoryPresentation`.

Ordinary categories organize sequential composition. An algorithm's
`CausalDiagram` should therefore be understood as an abstract evolution shape
\(\mathcal S\), while exact geometry, a world law, and a hardware execution are
separate functorial realizations of that shape.

Holonics also needs open boundaries and world/material incidence, so the more
faithful laboratory carrier is the holonic process double category:

- objects: local boundary types;
- horizontal arrows: decorated open constructions;
- vertical arrows: lawful boundary recharts;
- two-cells: commuting, lax, or oplax comparisons and exact refusals; and
- monoidal product: independent juxtaposition.

Actual co-presence is not supplied by the monoidal product alone. A declared
interaction doctrine acts on the systems through port plugging, variable
sharing, guarded incidence, a lens, or another typed interface pattern.
Parameterized conduct belongs in enriched hom-objects, where the parameter's
own structure determines whether it may be copied, retained, or discarded.

This aligns with applied category theory's use of monoidal categories, cospans,
system doctrines, enrichment, and open-system composition without asserting that
every implementation is identical.
See Fong and Spivak's
[*Seven Sketches in Compositionality*](https://arxiv.org/abs/1803.05316) and Fong's
[*The Algebra of Open and Interconnected Systems*](https://arxiv.org/abs/1609.05382).

### Definition 3.1 — sameness

There is no context-free predicate called “same” doing every job.

- **Literal equality** is equality in one chosen inscription.
- **Isomorphism** is reversible transport in a declared category.
- **Receiver equivalence** is equality after a declared observation functor.
- **Natural correspondence** relates whole families of transports coherently.
- **Physical equivalence** requires a declared physical receiver and tolerance law.

A SHA digest is testimony about one serialized face. It is neither an object's soul
nor its complete identity. Source-provided names and addresses are lawful identities
at their boundaries; they simply do not exhaust all other relations.

## 4. A programming object is a situated body with an interface

The word “object” conflates three things that must remain typed:

1. a categorical object is a compositional boundary;
2. an object-oriented value is a situated body exposed through an interface; and
3. a physical object is a material occurrence supporting that exposure.

For a situated carrier \(X\):

- a property is an observation arrow \(p:X\to V\);
- a parameterized method is a process
  \[
  m:P\otimes X\to X'\otimes R.
  \]

The value boundary \(V\), parameter boundary \(P\), successor \(X'\), and returned
face \(R\) are themselves objects. Properties and methods are recursive classifiers
because their boundaries can again expose relations. They are not scalar essence
stored “inside” an object.

A class or trait is a theory/signature of afforded arrows. An instance is one
situated model or occurrence. Dynamic dispatch chooses a lawful arrow through the
present interface; it does not change the occurrence's complete identity.

## 5. Data structures are standing incidence optimized for intended paths

A data structure is not a container species attached to information. It is a
standing incidence pattern whose lawful paths make some operations direct and
others costly.

| Structure | Holonic face | Afforded path | Required invariant |
|---|---|---|---|
| array | ordered address chart | index to resident slot | contiguous chart and extent |
| linked list | free directed path of node occurrences | successor composition | retained link at every open node |
| stack | one exposed boundary of a path | last-founded / first-returned | one active top |
| queue | path with distinct ingress and egress cuts | first-founded / first-returned | preserved order |
| tree | hierarchical boundary refinement | root-to-region traversal | parent/child incidence |
| binary search tree | ordered branching refinement | comparison-directed path | order invariant |
| hash table | quotient into address fibers | key to candidate fiber | hash plus retained collision distinction |
| graph | arbitrary incidence complex | local or global path | declared vertices and edges |
| simplicial complex | incidence closed under faces | transport among cells of several ranks | face/coface compatibility |

### Linked-list traversal and the swing

For links \(l_i:N_i\to N_{i+1}\), traversal is composition

\[
N_0\xrightarrow{l_0}N_1\xrightarrow{l_1}\cdots\xrightarrow{l_{n-1}}N_n.
\]

This resembles the swing because each contemporary node re-bases the available
next relation. It does **not** imply physical locality: a heap-linked list may
require a separate cache or memory current at every step.

### Binary search and lightning

Binary search is exact only under three supplied invariants:

1. a total order;
2. random access to the ordered region; and
3. a monotone comparison partition.

It follows one path through a balanced decision tree and reduces an interval of
size \(n\) to at most \(\lceil n/2\rceil\) per comparison. Lightning search is not
therefore “binary search.” The closer computational form is a plural frontier
propagating through locally afforded conductive relations, with branches refusing,
joining, or becoming a return path. Binary search is one degenerate world where
the frontier has an exact monotone two-way partition.

### Structure selection

Choosing a data structure means factoring the desired algorithm through a standing
incidence whose resource receipt is acceptable:

\[
\text{question}\to
\text{admissible operations}\to
\text{standing incidence}\to
\text{execution paths}\to
\text{resource faces}.
\]

No DSA is universally efficient. Its complexity is relative to the operations,
input family, hardware realization, and measured resource.

## 6. Complexity is a family of receiver faces

### Definition 6.1 — logical resource receipt

For one unfolded event diagram \(D\):

\[
\mathcal R_{\mathrm{logical}}(D)=
\bigl(W(D),S(D),P(D),\{\#\operatorname{law}_i\}\bigr),
\]

where \(W\) is total event work, \(S\) is longest causal-layer depth, \(P\) is an
exposed co-present frontier width, and the law population retains the work's
species.

### Definition 6.2 — physical resource receipt

For a hardware realization \(H\):

\[
\mathcal R_H(D)=
\bigl(
Q_{\text{tier}}^{read},
Q_{\text{tier}}^{write},
M_{\text{tier}},
N_{\text{message}},
N_{\text{sync}},
N_{\text{cycle}},
N_{\text{merge}}
\bigr).
\]

Missing coordinates are unknown, not zero.

Big-O notation is an asymptotic receiver over a selected input family and cost
coordinate. It does not measure all of computation. Hong and Kung's
[red-blue pebble model](https://www.eecs.harvard.edu/~htk/publication/1981-stoc-hong-kung.pdf)
and later [communication lower bounds](https://arxiv.org/abs/0905.2485) make
data movement explicit. The
[Roofline model](https://www2.eecs.berkeley.edu/Pubs/TechRpts/2008/EECS-2008-134.html)
relates attainable performance to arithmetic intensity and memory bandwidth.
These are complementary receivers, not replacements for causal semantics.

### Proposition 6.3 — hardware realization is generally lax

A hardware realization can be modeled as a lax monoidal functor

\[
\mathfrak R_H:\operatorname{Exec}(\mathcal A)\to\operatorname{Phys}(H).
\]

It is lax because logically co-present events may contend for one physical
resource, while one physical vector instruction may realize several logical
arrows. It need not be faithful: distinct logical traces may compile to one
machine trace, and one logical arrow may compile differently by context.

An optimizer is valid only when a refinement relation makes the implementation
diagram commute at every declared public boundary. Matching one output example is
insufficient.

## 7. Information has logical, statistical, and physical faces

Shannon entropy and mutual information require a declared distribution over a
declared alphabet. They measure uncertainty under that quotient; they do not define
the identity or semantics of the carried occurrences.

A channel is a conditional transport law. A deterministic algorithm is a special
channel whose receiver quotient has one consequence for each admitted source
state. A first-person observer may still have a plural field because its current
information does not distinguish all source states.

Logical irreversibility occurs when distinguishable predecessors merge into one
successor without retained residual:

\[
x_1\ne x_2,\qquad f(x_1)=f(x_2).
\]

Landauer's original paper connects such irreversible machine functions to physical
dissipation
([paper](https://www.dna.caltech.edu/courses/cs191/paperscs191/landauer1961.pdf)).
Bennett shows how reversible computation can retain enough history to avoid
logical erasure
([paper](https://www.cs.princeton.edu/courses/archive/fall06/cos576/papers/bennett73.html)).
Neither result licenses assigning one universal energy scalar to an abstract
operation. Actual energy also depends on device, voltage, capacitance, leakage,
temperature, timing, memory movement, and control.

The engine evaluates energy only from exact executor-observed physical counts and
a caller-declared exact coefficient for every nonzero term. If any coefficient is
absent, energy remains unknown.

## 8. CPU, GPU, RAM, clocks, and transistors

### 8.1 Address is a chart

A pointer or array index is a local address chart into one memory realization. It
is not the complete identity of the value stored there and not the causal reason
the value exists.

### 8.2 Memory is a physically maintained standing face

Registers, SRAM, DRAM, device memory, and durable storage retain distinguishable
states through different material mechanisms. DRAM charge must be sensed and
refreshed; SRAM uses a maintained bistable circuit; caches copy and evict address
faces. “Read memory” is a physical transport, even when the programming language
presents it as a primitive expression.

### 8.3 A clock is a synchronization current

A clock supplies ordered sampling apertures to a synchronous circuit. It does not
create semantic causality. Combinational propagation, metastability constraints,
out-of-order execution, cache coherence, and device queues remain physical
relations around those apertures.

### 8.4 CPU and GPU are different physical factorizations

A CPU may dynamically schedule instructions, speculate, and use deep cache
hierarchies. A GPU exposes large populations of lanes grouped into warps/wavefronts
with tiered memory and synchronization scopes. The current
[CUDA Programming Guide](https://docs.nvidia.com/cuda/cuda-programming-guide/index.html)
distinguishes thread, block, grid, warp, and global/shared/private memory; its
coalescing rules show that equal logical work can cause unequal memory transactions
solely because the address geometry differs.

Logical antichains identify available parallelism. They do not prove simultaneous
hardware execution or efficient data movement.

### 8.5 Instruction sets are boundary contracts

An ISA such as the
[RISC-V unprivileged specification](https://docs.riscv.org/reference/isa/v20191213/_attachments/riscv-unprivileged.pdf)
defines architectural states and transitions visible at its boundary.
Micro-operations, transistor switching, caches, and timing refine that contract
without becoming identical to it.

## 9. Exact first-person graphics and physics

### Definition 9.1 — receiver

A receiver is a participating local frame, a finite aperture, and a declared ray
family. It is not an external camera.

Receivers form a context category \(\mathcal R\). Their local ecologies are
fibers of \(p:\mathcal E\to\mathcal R\), and their received faces form local
sections. A face is global over a declared region only when compatible local
sections glue across a cover of that boundary-defined region. There is no
scene-wide state outside those local fibers; the total category is an atlas,
not an absolute observer.

For aperture width \(W\), height \(H\), exact spans \(s_x,s_y\), and discrete
column/row \((c,r)\), the engine uses pixel-center ratios

\[
u_c=\frac{(2c+1)-W}{2W}s_x,
\qquad
v_r=\frac{H-(2r+1)}{2H}s_y.
\]

The resolution is a finite receiver constraint. No floating-point normalization
enters. The ray family is either

\[
\text{parallel:}\quad
R_{c,r}(t)=\bigl(o+u_ch+v_rv\bigr)+td,
\]

or

\[
\text{central:}\quad
R_{c,r}(t)=o+t\bigl(f+u_ch+v_rv\bigr).
\]

All vectors are components in the receiver's own chart. Source faces can be
compared only after a declared frame relation transports them into that chart.

### Definition 9.2 — exact crossing fiber

For transported triangle vertices \(a,b,c\), solve

\[
o+td=a+\beta(b-a)+\gamma(c-a).
\]

A crossing exists when

\[
t\ge0,\qquad
\beta\ge0,\qquad
\gamma\ge0,\qquad
\beta+\gamma\le1.
\]

The engine retains

\[
\left(t,\;1-\beta-\gamma,\;\beta,\;\gamma,\;\operatorname{hand}\right)
\]

as exact ratios. This is the change-of-basis content of the
[Möller–Trumbore relation](https://doi.org/10.1080/10867651.1997.10487468),
but evaluated with arbitrary-size rationals and with no epsilon, approximate
normalization, or preselected nearest surface.

Every pixel returns the ordered fiber

\[
\Phi_{c,r}=\bigl[L_0,L_1,\ldots,L_k\bigr],
\]

where a layer \(L_i\) contains every crossing at the same exact ray parameter.
Same-depth crossings remain plural. A material/display law may later turn that
fiber into color, sound, force, or another consequence; the geometry core does
not silently collapse it.

### Definition 9.3 — physical succession

An exact world law derives

\[
(B_t,E_t)\longmapsto(B_{t+1},R_t)
\]

from an immutable predecessor. `CausalWorld` commits \(B_{t+1}\) only after the
whole law succeeds. Refusal leaves \(B_t\) exact and creates no false instant.

Graphics and physics share this carrier: physics changes the caused relational
complex by event law; receiving transports its contemporary surfaces into a local
aperture; and the crossing receipt is testimony from that event, not an absolute
snapshot.

## 10. Why Vulkan is not yet the authority

The current [Vulkan specification](https://registry.khronos.org/vulkan/specs/latest/html/vkspec.html)
does provide explicit low-level queues, memory, synchronization, compute dispatch,
and SPIR-V programs. It is therefore a viable **physical executor boundary**.

The fixed graphics pipeline is not acceptable as the mathematical owner because it
normally assumes fixed clipping, depth, interpolation, and finite scalar formats.
A future backend should use compute and storage buffers/images only.

Vulkan does not supply arbitrary-size exact rational arithmetic. The backend must
implement checked signed-limb integers, normalized numerator/denominator pairs,
overflow continuation, exact comparisons, and the same plural crossing fibers.
Until host/card equivalence closes, the CPU reference is authoritative.

## 11. Constructed source

New crate:

```text
crates/holonic-engine/
├── category.rs   boundary objects, arrows, and composable paths
├── causal.rs     unfolded occurrence diagrams and co-present layers
├── display.rs    explicit crossing-fiber-to-pixel world membrane
├── resource.rs   typed logical/physical/energy receipts
├── world.rs      atomic exact successor commitment
└── receiver.rs   exact receiver-aperture ray/surface crossing fibers
```

It depends on `relational-geometry` for exact ratios, local frames, declared frame
relations, and caused geometry. It has no Bevy, wgpu, glam, Avian, Vulkan, CUDA,
window, or floating-point dependency.

The rejected `apps/geometry-lab` Bevy shell was moved to trash and removed from the
workspace. `relational-geometry` was retained because it is the exact causal
mathematics underneath that shell, not the rejected presentation.

## 12. Exact standing and open work

Established:

- algorithms can be represented as typed composable paths plus actual causal
  occurrence diagrams;
- co-presence is not fabricated from executor order;
- logical and physical resources are separate typed receipts;
- unknown energy is not fabricated;
- world succession is atomic;
- finite receiver apertures use exact ratios;
- source faces require declared frame transport;
- every exact ray/triangle crossing and barycentric relation is retained; and
- same-depth and multi-depth crossings remain plural and ordered; and
- color packing occurs only after an explicit world transducer receives the
  complete fiber.

Not yet established:

- evolution-shape realizations as an explicit functorial source contract;
- an explicit interaction doctrine separated from monoidal juxtaposition;
- enriched parameter lifecycle and resource permissions;
- receiver fibers, local-section restriction, and exact gluing or obstruction;
- curves and higher-dimensional cells as native crossing surfaces;
- acceleration structures derived from the incidence complex;
- physical motion, collision, conservation, or field laws for a selected world;
- a selected world's material, occlusion, lighting, and response law;
- window or device presentation;
- exact Vulkan limb arithmetic and host/card equivalence;
- measured CPU cache/DRAM traffic or energy; and
- integration of this standalone engine with the production Eros mouth.

These are distinct constructions. This record schedules none of them automatically.
