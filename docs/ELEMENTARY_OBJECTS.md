# The elementary Holonic objects

[project-postulate] Brandon, September 22, 2026: these objects are cemented as the library, and
design, briefs, formal work and code state their operations **only** in them. A text, image,
acoustic, motor or arithmetic application is a boundary chart of these objects. A new noun that
is not one of them, or a composition of them, is a design defect to be named and repaired.
This guide owns the definitions; [CLAUDE.md](../CLAUDE.md) and [AGENTS.md](../AGENTS.md) carry the
operating summary. The [derivation record](../research/records/2026-09-22_THE_ELEMENTARY_OBJECTS_ARE_CEMENTED_AS_THE_HOLONIC_LIBRARY.md)
retains the conversation, surveys and open theorems.

## The picture

[definition] The complete implementation is a continuing field of chains of **complex
parametrons** — annular rings that store, oscillate and lock — joined by **helical pair contacts**
that slip, dissipate and address. Rings rotate and align; contacts converge and diverge action
between them. Every other object below is a part, a dual, a comparison or a continuation of that
picture. Neither half reduces to the other: the ring is the reactive (second-order, storing) cell,
the contact is the dissipative (first-order, addressing) cell.

<a id="the-holon-as-one-object"></a>

## The Holon as one object

[definition; agent-inferred] The objects below are facets of one object
([refinement record](../research/records/2026-09-22_THE_HOLON_IS_AN_INTERCONNECTED_PORT_OBJECT_ON_A_COMPLEX.md),
from the [proposal](../research/records/2026-09-22_PROPOSAL_THE_HOLON_AS_A_RECURSIVE_GENERATOR_FLUX_OBSERVER_OBJECT.md)).
A **Holon** is the law and its ports, not its state:

```text
H = (K, ∂_A;  Π;  𝒟;  𝓔;  G;  π)
K, ∂_A   oriented complex, connection-valued incidence d_A (d_A² = F_A, curvature a cell face)
Π        ports: flow f and effort e per interface cell, ⟨e,f⟩ = power (entropy rate × temperature for information)
𝒟        interconnection (Dirac) structure, 𝒟 = 𝒟^⊥; power neutral: ⟨e,f⟩ = 0 on 𝒟 (Tellegen, Stokes)
𝓔        element relations = constitution: storage E_Θ (C, K), resistive (contacts, M ⪰ 0 where passive),
         sources, active/learned relations with their power, pumps
G        navigators: initial configuration (the key), clock, phase lift θ̃ = θ + 2πn; supply U_e and skew transport
π        restrictions to coarser grains; the scale square or a typed defect
motion   flows/efforts in 𝒟 satisfying 𝓔;  d/dτ E_Θ = −dissipation + port power + active power + ⟨∂_Θ E, Θ̇⟩
```

A state is a point on a Holon; a trajectory is one of its admitted motions. Receivers are Holons
joined at ports; a passive coholon is the zero-storage limit that reads an effort. Interconnecting
Holons through their ports yields a Holon, which is the recursion. Passivity is a proved property,
never assumed: learned or nonlocal relations enter with their actual power term. Linear SSMs,
diffusion, Maxwell (Stokes–Dirac on the de Rham complex) and Euler/Navier–Stokes (Lie–Poisson plus
viscous resistance) are specializations; the occurrence Holon of `Foundation/Holon.lean` is its event
chart. The Lean foundation is `Holonics.Framework.HolonObject` (`Holon/{Port,Dirac,Complex,Element,
Generator,Restriction,Law,Conformance}`); the Rust core `holonics` mirrors it facet by facet, and every
later owner implements or charts it.

<a id="operator-contract"></a>
[definition] **Operator contract** (September 24, [the rebuild](plans/THE_REBUILD.md)).
Each object's operations and their owners are listed below. The *current* column is the
checked code today. The *target* column is its home in the main `holonics` library and the
Lean `Holonics` library in the rebuild. A target name is not importable until its owner is
built. Each rebuild step updates this table in the same commit.

| Object | Operations | Current owners | Target |
|---|---|---|---|
| Ratio | `present`, `compare`, `compose`, `invert` (nonunit fibre), `div_rem`, `residue`, `lift`, `jet`, `log` with branch | Lean `Objects/{Ratio,RatioPhase,RatioBlock}`, `Foundation/TransportLift`, `Geometry/{PhaseCarry,CrossRatio}`, `Geometry/Farey`; Rust `holonics::ratio::{Rat,Presentation,ExactOrdering}` (the undivided pair, compared by cross-multiplication), `holonics::ratio::linear` (inversion with its fibre), `holonics::geometry::winding::Odometer`, `holonics::navigator::address::LockAddress`, `holonics::ratio::ring::{ExactRing,ModularWords}`, `holonics::ratio::exponentiated::{RatioFamily,NormalizedKernel}`, `holonics::ratio::surprisal`, `holonics::holon::contact::Alignment` (the undivided squared-cosine face) | `holonics::ratio`; `Holonics.Ratio` |
| Complex, frame, clock, carry | `boundary`, `transport`, `transport_rate`, `join_axes` (commuting square or defect), phase lift | Lean `Holon/Complex`, `Geometry/*`; Rust `holonics::geometry::complex`, `holonics::navigator::Clock`, the frame carriers `holonics::geometry::{RatVec3,RatMat3,AffineMap3,Axis}` over `holonics::ratio::Rat` | `holonics::geometry`; `Holonics.Geometry` |
| Swing | `swing` (half-turn about an anchor), `compose` (two Swings are a translation; odd words are Swings), `pantograph` (scale about an anchor), `tick` (oriented section crossing), inner fibre of a coarse Swing | Lean `Geometry/{AffineSwing,SwingPotential}`, `Geometry/{Swing,SwingBridges,Navigation,HolonicPantographicSwingJets,HolonicClockedPantographicSwing,HolonicClockedPantographicSwingApparatus}`; Rust `holonics::geometry::swing` (`swing`, `composed_translation`, `pantograph`, `harmonic_conjugate`, `swing_pair`) | `holonics::geometry`; `Holonics.Geometry` |
| Pair and tube charts | `screw_pair` (two motions, relative jet), `tube` (longitudinal transfer), `restrict` (transverse, gluing unique/plural/obstructed), neck, fold, junction | Lean `Transport/{HelicalPairInteraction,ContinuingTube,WorldTube,Neck,Fold,JunctionLaw,JetStaircase}`, `Geometry/PairResonance`, `Foundation/{ContinuingTower,IwasawaTower}`; Rust `holonics::geometry::screw`, `holonics::holon::restriction::{tube,tower}` | `holonics::geometry`; `Holonics.Geometry` |
| Pair contact | `slip` (`J=[v_a\|−v_b]`), `quadrance` (`Q`, `DQ=2J*Δ`, `D²Q`), `material` (`M_contact=ΣwJ*DJ`), `power` (resistive element on slip), `lock_address` (Farey), `chain` (serial screw words and contact rows) | Lean `Transport/{HelicalPairInteraction,HolonicInteraction,HolonicChain,SerialScrewChain}`, `Geometry/PairResonance`, `Holon/Conformance.pairContact_resistive`; Rust `holonics::geometry::screw::{ScrewPair,PairQuadranceJet,SituatedScrew}` (the pair geometry), `holonics::holon::contact` (`PairContact`, `ContactMaterial`, `Alignment`, `SerialChain`), `holonics::navigator::address::LockAddress` | `holonics::holon::contact`; `Holonics.Holon` |
| Parametron | `store`/`exchange` (`C`, `L`, `ω=1/√(LC)`, mode energy), `pump`, `lock` (half-turn sheets, Ising pairing), `tick` (section crossing), `read` (the perceptron face) | Lean `Objects/Parametron`, `Physics/{PhaseCarrier,CoupledIncidence,HolonicMeasuredParametron,HolonicTorusParametronRealization}`; Rust `holonics::holon::parametron` (`Parametron`, `Carrier`, `Population`, `pump_storage`, `ring_crossings`) and the pumped-LC witness of `holonics::holon::conformance` | `holonics::holon::parametron`; `Holonics.Holon` |
| Navigator | `configure` (initial configuration: the key), `advance` (own clock, carry), `restrict` (scale square), `address` (source word), trace faces and the dynamical zeta, lock address, `release` at tolerance | Lean `Holon/Generator`, `Foundation/{FractalPacking,GeneratorInference}`, `Transport/{GeneratorTraceFaces,SourceMoment,ReflectiveContinuation}`; Rust `holonics::navigator` (`Navigator`, `Transport`, `Clock`, `PhaseLift`, `reflection`, `address`), `holonics::navigator::trace::{SiteFactor,Machine}` | `holonics::navigator`; `Holonics.Navigator` |
| Holon | `advance` (state, bond, energy balance), `interconnect -> Holarchy`, `contact` (a pair contact as element), `continue` (through a tube), `restrict`, `depose`, `pullback` | Lean `Holon/{Law,Port,Dirac,Element,Generator,Restriction,Deposition,Reaction,Cayley,Conformance}`, `Foundation/{Holon,Lineage,ConnectionLineage}`, `Objects/Deposition`; Rust `holonics::holon` (`law`, `port`, `dirac`, `element`, `restriction`, `deposition`, `reaction`, `conformance`, `contact`, `parametron`), `holonics::navigator` | `holonics::holon`; `Holonics.Holon` |
| Receiver and receipt | `interact`/`receive -> InteractionReturn` (both participants' next states, face, receipt, boundary currents, power balance, unresolved fibre); `Ratio::between(receipts)`; `width`, `release` (caller-declared decision and tolerance checks); `chord` (transfer object) | Lean `Holarchy/{Reception,Receipt}`, `Foundation/{Receiver,ReceiverRelease,Standing,CausalChord,ReceiverAtlas,PresentationCost,SituatedInformationRate}`, `Transport/ChangingReceiver`, `Objects/Pairing`; Rust `holonics::receiver::reception` (`JointLaw::interact -> InteractionReturn` on the solved joint step, `ReceiverFace` and its three-term `FaceMotion`, `JointLaw::of_holarchy`; `HolonLaw::receive` is its zero-storage specialization `JointLaw::reading`), `holonics::receiver::receipt` (`Receipt`, `ReceiptLaw`, `ReceiptRatio::between` and `follow`, with `ratio::Presentation::follow`), `holonics::receiver::face` (faces and passive law), `holonics::receiver::{release,standing,causal_chord}`, `holonics::ratio::work::ExactWork`; history [`presentation_cost.rs`](https://github.com/brandonrdug/holonics/blob/13f8c734/crates/holonics-cuda/src/presentation_cost.rs), [`landauer.rs`](https://github.com/brandonrdug/holonics/blob/13f8c734/crates/holonics-cuda/src/landauer.rs); guide [RECEIVER_HOLARCHY](RECEIVER_HOLARCHY.md) | `holonics::receiver` (release operations); `Holonics.Receiver` |
| Holarchy | `interconnect -> Holarchy` (typed port/cellular gluing); `whole`, `view(receiver, grain, clock)`, `count` (receiver-certified finite partition), `refine` (commuting square or defect), `parametric` (the aeons' clock lift) | Lean `Holarchy/{Join,View,Receipt,Reception,Globe}` (`Constituent`, `interconnect_ok_iff`, `join_power_balance`, `shared_face_cancels`, `Holarchy.parametric`, `HolarchyGlobe`); Rust `holonics::holarchy` (`Holon::interconnect -> Result<Holarchy, GluingDefect>` over a `Gluing` checked against both Holons' own units, complexes and pumps, navigators joined; `Holarchy::{whole, interface_fibre, power_balance, flux, pump_lock, parametric}`), `holonics::holarchy::view` (`Holarchy::{view, count, refine, block_boundaries, interface_flux}`); Rust has no globe consumer | `holonics::holarchy`; `Holonics.Holarchy` |
| Aeon, epoch, cycle | `reading(clock, aeon) -> (windings, phase)`, `concat` (with carry), `reverse`, `epochs(receiver, grain)`, `coarsen` (induced section), `is_cycle`, `rate`, `hodge_split`, `production`, `zeta` | Lean `Aeon/Clock/{Groupoid,Reading,Winding,Lock,Epoch}`, `Aeon/Production/{HodgeTime,Kac,PathReversal,Zeta,FirstLaw}` over `Geometry/PhaseCarry`, `Transport/CellHolonomy`, `Objects/Pairing`; Rust `holonics::aeon` (`Aeon`, `Cycle`, `ClockLift`, `reading`, `rate`, `Epochs`, `EpochTower`, `TwoClocks`, `hodge_split`, `MarkovChain`, `zeta`, `learning_balance`) | `holonics::aeon`; `Holonics.Aeon` |
| Physical instances | fluid `face_flux`/`advance`; wave `propagate`/`interfere`; thermal `exchange`/`diffuse`/`entropy_production`; spacetime `einstein_residual`/`observer_current`; information `apply` | Lean `Physics/{Fluid,Wave,Thermal}/*` (cells reflect/join, control volume, complex fluid, singularity flows, closed bodies; interference, telegrapher cone, radiation; two-cell exchange, viscous port, Schnakenberg, chain axes), `Physics/*`, `Holon/Conformance`, `Fluid/{NavierStokesLambCurrentCell,NavierStokesCurvedTransport}`; Rust `holonics::physics::{fluid,wave,thermal}` and `holonics::holon::conformance`; missing: fluid time `advance` with its pressure solve, many-cell `diffuse` (#62); spacetime and information instances are K4 (#75) | `holonics::physics`; `Holonics.Physics` (construction K3–K4) |
| Compression and landmarks | `kernel` (relevance kernel; its quotient is retention), `cokernel` (the residual to emanate or retain, with its horizon), `resonate`/`emanate` split, `cost` (description + work against the literal), `infer` (loop closure), site kinds (rotation, null, boost; reflection, degenerate), fixed-point landmarks, identity atlas (checked coverage), constraint-identity windows, primitive cycles | Lean `Compression/Core/{FaceMap,Resonance,Cost,Keys}`, `Compression/Landmark/{SiteKind,FixedPoint,Identity,ConstraintIdentity,PrimitiveCycle}` over `Foundation/{CausalRelevance,ReceiverHistoryCompression,GeneratorModeQuotient,ReceiverCodeCost,GeneratorInference}`, `Geometry/TwoSidedIdentityAtlas`, `Mathematics/{RatioSeriesTransport,RadixWindowReceiver}`; target joins in `HolonicsResearch/Landmarks`; Rust `holonics::compression` (`FaceMap`, `resonance_split`, `CompressionCost`, `Menu`) and `holonics::compression::landmark` | `holonics::compression`; `Holonics.Compression` (#145) |
| HNN | field law, source moments, adjoint, deposition return, execution port | none since the reset; the prototype is in history ([`native_ecology/constitutive_fibre/field`](https://github.com/brandonrdug/holonics/tree/13f8c734/crates/holonics-cuda/src/native_ecology/constitutive_fibre/field), [`hnn`](https://github.com/brandonrdug/holonics/tree/13f8c734/crates/holonics-cuda/src/hnn)) | law and port in `holonics::hnn`; resident realization in `holonics-cuda::hnn`; `Holonics.HNN` (rebuild steps 4–5) |

The restructure's detailed contracts are in history at
[`13f8c734`](https://github.com/brandonrdug/holonics/blob/13f8c734/docs/plans/THE_REPOSITORY_RESTRUCTURE.md).

[definition] **Use of a Holon's material across an event boundary.** These are admissibility
conditions on a Holon's existing ports, element relations and admitted futures, not a separate
parameter object. An occurrence may be copied only when the relation at that interface supplies a
lawful diagonal; a cloneable carrier alone does not establish that law. What remains available is
governed by the admitted future: a retained representation is lawful only when every admitted
receiver reading factors through it (`Foundation/Standing.lean::StandingLaw`). A local event
boundary releases the occurrences declared event-local, and a separately declared departure may
remove one occurrence earlier. When an event-local occurrence also carries an explicit return
obligation, departure is refused until it returns, and closing the boundary is refused while that
obligation remains. A successful return consumes that occurrence; it does not create a retained
event archive. These copy, retention and departure labels are a local policy
chart, not a general standing law: the hypotheses are the declared interface, obligations and
future receiver family. Absent them, do not infer copyability, safe departure or a need for
persistence from the Rust carrier type. This records the reusable relation isolated by the
[August 14 audit](../research/records/2026-08-14_THE_CENSUS_DECAYED_THE_CYCLE_IS_BUILT_AND_THE_OPEN_GRADE_IS_THE_NONIDENTICAL_NEIGHBOURHOOD.md#6-corrections-to-the-record-this-audit-produced).

## The objects

Each object comes with its dual. A reading is always a pairing of the two, and orientation exists
only in that pairing.

### 0. Complex

[definition] Oriented cells with boundary `∂`, `∂²=0`: the incidence on which everything is
placed. Owners: `Geometry/ExteriorBoundary`, `Holon/Complex`, `Foundation/Holon.BoundaryHolon`,
`Foundation/AperturedGradedComplex`; Rust `holonics::geometry::complex`.

### 1. Holon and coholon

[definition] A **Holon** `|H⟩` is a continuing object on the complex: a current, flux or motion
with oriented ports. It is not produced by a computation. Its admitted motions — including the
implicit navigator relations that bind a passage of writing, a gait or a knot — are already
present as potential, whether or not a receiver currently reads them. A **coholon** `⟨Ȟ|` is its
dual: a potential or receiver, with coboundary `d=∂ᵀ`. Their pairing is the face:

```text
face      ⟨Ȟ|H⟩
Stokes    ⟨dȞ, H⟩ = ⟨Ȟ, ∂H⟩                                  ExteriorBoundary.stokes_pairing
drop      ⟨φ, ∂H⟩ = φ(target) − φ(source)                     Objects/Pairing.face_is_potential_drop
gauge     classes mod d and mod ∂ pair: H_k × Hᵏ → R          CellHolonomy.cell_flux_is_gauge_free, HodgeReceiver
orient    flipping a cell negates both sides; the pairing is unchanged      Objects/Pairing (joint reorientation)
classes   one bilinear class pairing, read by the harmonic representative  Objects/Pairing.classPairing
```

Chain/cochain, vector/covector, ket/bra, current/potential, kernel/cokernel (the two-term case) and
cycle/cocycle/coboundary (the classes) are all this one pairing. A Holon alone is **unoriented
potential**; it becomes oriented relative to a frame when a coholon over a relatively complete
region (object 7) is paired with it. A cycle whose joint signs multiply to −1 admits no orientation,
and one whose product is +1 does (`Objects/Pairing.no_orientation_of_reversing_cycle`,
`orientation_of_preserving_cycle`; the older `JunctionLaw` statement is vacuous, #62).

### 2. Constitution

[definition] The **constitution** `Θ` is the declared material law on the complex that relates a
coholon to the motion of a Holon it excites. It does not create the Holon: it states which admitted
motion a given potential drives and at what cost. It has two kinds, which exchange:

```text
capacitive   C = Bᵀ M_C B        energy ½⟨ẋ, C ẋ⟩ in the node-flux chart
inductive    K = Bᵀ M_L B        (M_L inverse-inductive/stiffness) energy ½⟨x, K x⟩
modes        K v = ω² C v        the two energies exchange along a mode      CoupledIncidence.IsGeneralizedMode
dissipation  D ⪰ 0,  power ⟨Jv, D Jv⟩                                         HelicalPairInteraction
```

Which of the two exchanging energies is read as storage (standing) and which as flow (emanation) is
a chart choice; the exchange itself is chart-free (`Objects/Parametron.modeEnergy_conserved`).

A Holon's motion decomposes into exact (potential-driven) ⊕ coexact (induced; Faraday emf is not an
exact drop, `HolonicDiscreteInduction.emf_ne_exactDrop_of_fluxDifference_ne_zero`) ⊕ harmonic
(dormant, silent at node/cell receivers, `CellHolonomy.dormant_mode_is_locally_silent`). Owners:
`HodgeReceiver`, `PositiveCellHodge`, `Physics/CoupledIncidence`, the normal law `W H=B`.

<a id="3-navigator"></a>
### 3. Navigator

[definition] A **navigator** `Ĝ` is a transport with an **initial configuration** and its own
clock. The guides called it a *generator*. That word keeps only its algebraic senses: a group
generator, the Lie generator `ξ` of a helix, a generating function. Lean and Rust names change
when the rebuild reaches them. A navigator acts on Holons; its adjoint `Ĝ*` acts on coholons, `⟨Ĝ*Ȟ|H⟩=⟨Ȟ|ĜH⟩`, and the learning
covector travels along that adjoint. A helix is circle + carry (`PhaseCarry`: winding cocycle). A
**fractal navigator** is a family of maps with parameters, restriction maps, composition order,
scale square `r∘T_fine=T_coarse∘r` and first-arrival populations of one full recurrence
(`FractalPacking`, `HolonicRecurrentEcology.FirstArrival`); an ordered source word is its
**address** (`SourceMoment`: identity advance merges permutations, as a restriction word cannot
collapse to a multiset). Recursive description and branch/address information are separate
compression operands. A navigator runs until its receiver face is within tolerance
(`ReceiverRelease.Releasable`, `Standing.Extinct`); then it is released and a new one is founded.
Holonic Compression couples a fractal navigator's resonating modes with terrain
([the line](plans/THE_REBUILD.md#the-line-the-rebuild-serves)).

[established-bounded; source-inspected] The source-neutral continuation contract is a chart of
Navigator and Receiver operations, not a new elementary object. A running continuation receives a
registered face under its current codec; each codec records the face that caused its mounting. A
receiver may return an advance, rest or a reflection request. A reflection snapshots the current
codec and instruction. A returned revision resumes
that same continuation at the same instruction only when the new codec names the reflected codec
as a parent; unchanged resumption keeps the codec and instruction. The environment returned by
the executor remains with the continuation throughout. `Transport/ReflectiveContinuation.lean`
states these transitions and success laws. The Rust chart is
`holonics::navigator::reflection::ReflectiveRuntime`; its executor-specific semantics, atlas limits and remount
validation are outside this formal contract.

<a id="the-swing"></a>
#### The Swing: the navigator's elementary motion

[project-postulate] Brandon's most primitive concept is the **Swing**: the primitive act of
situated relating and transport. A body swings past an anchor, under a contemporary constraint, on
a board that every motion of the system leaves invariant. The Swing is harmonic conjugation,
`(A,A';B,D)=−1` with anchor `B` and board `D`; in the chart sending the anchor to `0` and the board
to `∞` it is negation (`Geometry/Swing`).

[proved-derived; formal-checked] Freezing the board puts it at infinity, and the Swing becomes the
point reflection, a half-turn `e^{iπ}` about the anchor (`Geometry/AffineSwing`):

```text
S_a x = 2a − x          S_a x − a = e^{iπ}(x − a),   S_a S_a = 1,   S_a a = a
S_b S_a x = x + 2(b − a)                  two Swings compose to a translation
S_b S_a − S_a S_b = 4(b − a)              and do not commute
```

An odd word of Swings is a Swing and an even word is a translation; that `ℤ/2` grading is the
orientation class (`Geometry/Navigation`). The Swing's charts are:
- **projective:** harmonic conjugation (`Geometry/{Swing,SwingBridges}`);
- **affine:** the point reflection above;
- **pantographic:** `Q−O=s(P−O)` about the anchor `O`, whose scale `−1` is the Swing and whose
  serial passages multiply scales (`Geometry/HolonicPantographicSwingJets`);
- **clocked pantographic** (`Geometry/HolonicClockedPantographicSwing`): a **tick** is an oriented
  crossing of a declared oscillator section, a clock ratio is carried by integer quotient and
  remainder (the remainder is within-cycle phase), and one coarse Swing keeps the complete fibre of
  its inner Swings with their individual clock passages. Placement on apparatus is a separate
  receiver (`HolonicClockedPantographicSwingApparatus`).

Rebasing the observation, receiver and navigators through a Swing preserves every possible future
face, and in a normed chart the Swing carries a declared tolerance exactly (`Geometry/SwingPotential`).
With a subspace for its anchor, the Swing is `R_D=2P_D−I`: it splits one current into two shares and
recombines them, conserving the joint norm ([receiver atlas](RECEIVER_HOLARCHY.md#the-reflection-algebra-shared-by-seam-and-swing)).
A fold is that reflection applied to one side of a crease (§6).

[project-postulate] **The Swing is the navigator's elementary motion.** A navigator's advance
relates what moves to an anchor on a board; its word, clock and carry are how its Swings compose.
Navigating is choosing that word, and landmarks are where the words' paths converge.
[proved-standard] A translation is two point Swings, and every Euclidean isometry is a word of
reflections about hyperplanes (Cartan–Dieudonné).

[proved-derived; formal-checked] **Conservation of faces.** Carrying material to another phase
conjugates it, `M ↦ S⁻ᵈMSᵈ`, so every class function of the material is a face conserved along the
winding: its determinant, its trace sequence `tr(Mᵏ)` and its transfer determinant `det(1−T·M)`
(`Transport/GeneratorTraceFaces`: `carried_material_conserves_{determinant,trace_sequence,transfer_determinant}`;
[winding guide](WINDING_CARRY_AND_PLACEMENT.md) §3). For independent sites the transfer
determinants multiply, `det(1−T·⊕M_g)=∏(1−a_gT+q_gT²)`, and the trace sequences add. **Energy
conservation is one conservation of faces:** storage and flow exchange along a mode while the mode
energy is conserved (`Objects/Parametron.modeEnergy_conserved`), and the Cayley step of a skew
transport preserves its norm (`Holon/Cayley.cayley_isometry`; Rust chart `holonics::navigator`). Trace faces are invariants, not a complete
action certificate: `I₂` and `[[1,1],[0,1]]` share them, and the receiver `(1,0)` after one step
from `(0,1)` separates them.

### 4. Pair contact

[definition] The **helical pair contact** joins two navigators with configurations:
`Δ=x_a(s)−x_b(t)`, `Q=⟨Δ|Δ⟩`, slip `J=[v_a|−v_b]`, `DQ=2J*Δ`, contact material `M=Σw J*DJ`. It is
the constitution restricted to relative motion: it slips, dissipates and addresses. A no-slip lock
`q·v_a=p·v_b` has a Farey address; the mediant is the cheapest lock between neighbours
(`PairResonance`). The contact is a resistive element on relative slip: flow `f=Jv`, effort
`e=−Df`, power `⟨e,f⟩=−⟨Jv,DJv⟩≤0` for `D⪰0` (`Holon/Conformance.pairContact_resistive`). An ordered family of
`SituatedScrew`s is a serial chain whose Jacobian columns are recharted Lie generators and whose
contact rows are pair contacts (`SerialScrewChain`). Owners: Lean `Transport/{HelicalPairInteraction,
HolonicInteraction,HolonicChain,SerialScrewChain}`, `Geometry/PairResonance`; Rust
`holonics::geometry::screw::{ScrewPair,PairQuadranceJet}` for the pair geometry. The prototype adapter
and chain at `13f8c734` ([`helical.rs`](https://github.com/brandonrdug/holonics/blob/13f8c734/crates/holonics-cuda/src/holonic_interaction/helical.rs),
[`serial.rs`](https://github.com/brandonrdug/holonics/blob/13f8c734/crates/holonics-cuda/src/holonic_chain/serial.rs)) are the port sources for
`holonics::holon::contact`.

### 5. Parametron

[definition] The **complex parametron** is the ring: oriented incidence `B`, storage `M_C` and flow
`M_L`, complex modal transport, a time-periodic pump, damping and basin selection, a receiver, and
an optional two-sheet quotient. Its phase carrier is `e^{iθ}`; the half-turn `e^{iπ}=−1` exchanges
the two locked sheets, to which the pump is blind; on those sheets coupling `−w cos(θ_i−θ_j)` is
exactly the Ising pairing `−w σ_iσ_j`. A **perceptron is one receiver face of a coupled parametron
population**: fixed couplings, locked sheets, threshold readout. Storage and flow exchange at
`ω=1/√(LC)`; a section crossing of the ring is a clock tick. Owners:
`Physics/{PhaseCarrier,CoupledIncidence,HolonicMeasuredParametron}` and the torus realizations; the device refinement at `13f8c734`
([`complex_parametron.rs`](https://github.com/brandonrdug/holonics/blob/13f8c734/crates/holonics-cuda/src/cuda_refine/complex_parametron.rs)) is a port
source for `holonics::holon::parametron`. Joined in `Objects/Parametron`: the LC and generalized-mode
energy exchange, the ring's owner crossings as `RationalClockPassage` ticks (`d ≥ 2`), and the
threshold unit as the energy-minimizing locked sheet with a witness that equal perceptron outputs
carry different phase energy and quadrature. Open: pump/Floquet locking dynamics; the continuous
crossing of `A cos(ωt+φ)` equal to the micro-step ring.

### 6. Tube and tower

[definition] A **tube** is the longitudinal clocked span of transports between cross-sections; a
**tower** is the transverse restriction across grains, whose compatible sections are the continuing
object and whose gluing is unique, plural or obstructed. Holonomy lives only on declared circuits.
A **world tube** adds membrane ingress, outward restriction, lawful silence (nonzero interior in the
kernel of the outward map), return and the causal adjoint into the constitution. Integration by
reflection eliminates an interior to its boundary: the Schur complement is the discrete
Dirichlet-to-Neumann map `Λ_DN`.

[project-postulate] Brandon, September 18–19
([tube plan](https://github.com/brandonrdug/holonics/blob/13f8c734/docs/plans/THE_TUBE_CARRIES_RELEASE_THROUGH_NECKS_FOLDS_AND_JUNCTIONS.md#the-governing-statements)):
**prediction is figuring out when tubes will transport, and why**, for neural data, a Rubik's cube,
a chess game or an observer planning travel by the stars: the map dictates the plan. The tube is
the general object; a tower is what one instantaneous frame of it shows, and a **staircase** is its
passage between grains or difference orders. The structure is **a chain of necks and media** with
parametric orientation, crossing the axes of time and entropy. A **neck** is a pinhole where flux
converges from one medium and diverges into the next, as light through the lens of an eye onto the
retina; a **medium** is an intermediary lattice `H_int` with its constitution and contact faces.
Without joints a channel is a linear tube and computes trivially; the computational stress is at
junctions and at comparisons that must occur.

[project-postulate] **Identity belongs to an occurrence. Persistence belongs to lineage. Sameness
belongs to a receiver. Potential belongs to a family of future interactions. Memory belongs to
standing** (the retained quotient). `4` and `2^2` agree under `eval` and differ as expressions; the
equality belongs to the scalar receiver. `Foundation/RelationLadder` orders these rungs partially,
and no rung below identity entails it (`no_rung_below_identity_entails_identity`).

[definition] **Generation is a tube whose cross-section changes:** `F_{k+1} = T_{g_k}(F_k) ∩ C_k`,
with `T_g` a Swing, edit or transport and `C_k` a newly admitted constraint
(`Transport/ArtifactRelease.{step,stepMulti}`). **Release** is the station where the section is a
point at the receiver's grain while plural inside, `∀ a,a' ∈ F_k: π_B(a) ~ π_B(a')` (width zero).

[proved-derived; formal-checked] **Necks.** Under a positive constant flux a narrower section
carries a faster density, and a point focus keeps its angular spread while its width is zero; a bundle
of positive phase area keeps that area through any unimodular station (`Transport/Neck`).
In a chain the neck is `rank A_↗`, the rank of the cross block between consecutive media: every
upstream-to-downstream transfer `C(sI−A)⁻¹B`, at each `s` off the joint poles, has at most that rank, rank one is the pinhole, and a
closed neck zeroes every Markov parameter (`Transport/HolonicChain`). The conservative coupling
returns with a half-turn, `Ω_↘ = e^{iπ}Ω_↗ᵀ`, the dissipative one with none, `M_↘ = M_↗ᵀ`.

[project-postulate] **Folds and junctions.** Brandon: a joint is equivalently a fold, and a split
intersects planes, not only lines (the Möbius shorts). [proved-derived; formal-checked] A **fold**
is the reflection about a crease
applied to one side: two-to-one off the crease (`fold_fibre`), with one side bit as the residual
that reopens it (`reopen_apply_fold`). A relabelling of cells preserves Betti numbers
(`fold_preserves_betti`), a cut changes them, and the two-to-one quotient is a separate theorem
(`Transport/Fold`). A **junction** is a station of valence at least three. Its law is `d` and its
metric adjoint at the interface: tangential agreement `[[ι*u]]=0`, normal balance `[[n·flux]]=σ`
(that is `δf=σ`, with Tellegen as its energy ledger), and, for pieces of `χ=−1` glued along
circles, one unit of Euler characteristic per junction
(`Transport/JunctionLaw.each_junction_costs_one_euler`). The metric is the constitutive law; the
entropy condition belongs to the `(junction, direction)` pair. [definition] On the staircase a joint
is a spline knot whose order is the lowest derivative that jumps; `Transport/JetStaircase` states
the jet ladder that reading uses, and the spline families were the prototype's
[`jet_staircase.rs`](https://github.com/brandonrdug/holonics/blob/13f8c734/crates/holonics-cuda/src/jet_staircase.rs).

[proved-derived; formal-checked] **Placement.** With `Ω = e^{iπ/2}H`, `H` Hermitian, the chain's
infinitesimal generator is `A = (e^{iπ/2}H + e^{iπ}M)G`. For `G ≻ 0`, `M = M* ⪰ 0` the conservative
part places spectrum on the imaginary axis and the dissipative part on the nonpositive real line, a
quarter-turn apart; their sum lies in the closed left half-plane. [interpretation] A `G`-skew
operator has spectrum symmetric under `λ ↦ −λ̄`, the finite form of `ξ(s)=ξ(1−s)`; a lossless chain
is a Foster reactance, and turning `M` on is the finite analogue of the de Bruijn–Newman flow (`Zeta/FosterTanks`).
[proved-standard] For indefinite nondegenerate `G` with `κ` negative squares, at most
`min(κ, n−κ)` eigenvalues of a `G`-skew operator lie in the open right half-plane (Pontryagin;
`G=diag(1,−1)`, `A=[[0,1],[1,0]]` attains it; Lean lift #54). This conservative bound is not
asserted for an arbitrary mixed dissipative generator with indefinite storage. [interpretation] **`M_contact` and Hodge:** `M_contact = Σ w_f J_fᵀD_fJ_f` is the upper
term `d*⋆d` when the slips are the coboundary; harmonic classes also need `d_{k−1}d_{k−1}*`, so a
rigidity kernel is not by itself homology.

[definition] **The tower** `z = i^{i^{i^{⋰}}}` is the constraint `z = i^z = e^{(iπ/2)z}` on the
principal branch, `z = (2i/π)·W(−iπ/2)`, an attracting fixed point (`(π/2)|z| < 1`), never a float.
`arg z = (π/2)·Re z` and `|z| = e^{−(π/2)·Im z}`: the real part turns and the imaginary part
contracts, the same quarter-turn split between circulation and dissipation.

Owners: Lean `Transport/{ContinuingTube,WorldTube,Neck,Fold,JunctionLaw,JetStaircase,HolonicChain,ArtifactRelease}`,
`Foundation/{ContinuingTower,IwasawaTower,RelationLadder,ReceiverRelease}`,
`Physics/HolonicSnellInteraction`, `Geometry/HolonicInteractionExterior`; Rust
`holonics::holon::restriction::{tube,tower}`, `holonics::receiver::release`. Open joins: #5, #27, #32, #54.

### 7. Relative completeness (globe)

[definition; agent-inferred] A region `Ω` with closed boundary `∂Ω` and boundary map
`β : interior → boundary data` (its `Λ_DN`, Schur complement or outward restriction) is **relatively
complete** for a declared exterior receiver family `R` when:

1. **coupled** — the boundary datum depends on the interior state; coupling through a conserved
   charge counts (Birkhoff, Gauss), so `β` may be constant along the interior motion;
2. **not determined** — the interior dynamics are not a function of the boundary history: the
   fibre of `β` over every admitted exterior future is nontrivial and carries nontrivial internal
   evolution (lawful silence with motion, `WorldTube.IsLawfulSilence`);
3. **closed** — `∂Ω` is the boundary of the interior (a globe), rather than opening onto
   longitudinal ends (a tube); a cycle that bounds nothing does not qualify.

The interior motion in clause 2 must persist: a fibre that contracts or is quenched to a fixed
point is not motion (a decaying interior fails).

Completeness is always relative to `R`; no object is complete absolutely. Only a relatively complete
region can be identified as one structure with complex dynamics, and only over such a region does a
coholon orient a Holon (object 1). Instances: Birkhoff's theorem (the vacuum exterior of a spherically
symmetric body depends on its mass alone while the interior may move — coupled through `M`, not
determined by it); Gauss/ADM mass read on a bounding sphere. The band-limited **relevance theorem**
(`NavierStokesBandLimitedRelevance`) is *not* an instance at a band-limited instant: there the band
and the far tail are decoupled, so clause 1 fails; the join needs a persistent frontier current
into a declared exterior shell (open). A cold lattice with no interior motion fails (2); a ferrimagnetic rod
that transports spin along its length is a tube, failing (3).

[proved-derived; formal-checked] `Objects/RelativeCompleteness` states the three clauses — coupling
over admitted states, non-determination with persistent (exactly recurrent) motion in the fibre, and
a membrane bounding the region's interior chain — and proves the linear criterion: coupled ⇔ `C≠0`;
not determined ⇔ some `u ∈ ⋂ₖ ker(CAᵏ)` with `Au≠0` and `(1+A)ⁿu=u`. Witnesses: a quarter-turn
globe read through a conserved charge (Birkhoff type) is complete; a cold lattice, a quenched or
decaying (Ricci-type) interior, a fully observable interior, an open tube and a hollow loop each fail;
refining the receiver removes completeness. Open: approximate recurrence for quasi-periodic
interiors, the join of `β` to the membrane's faces, and the Λ_DN join.

[open] The **relative completeness theorem** is to be derived by pairing the Einstein lifts
(`HolonicCurvedArcEinstein`, `Ricci`, `HolonicFieldTheoryPassage`, `CurvatureAndGap`) with the
complex Euler/Navier–Stokes current laws: a criterion for when a globe exists as a potential, stated
as interior↔exterior entrance/escape currents through `∂Ω`, including how the bounding radius
scales with dimension (hypersphere boundaries). It joins the relevance theorem. Owed in #62; nothing
here asserts it.

### 8. Deposition

[definition] **Deposition** is the only law by which a constitution changes. A covector that has
actually arrived at a locus changes that locus's constitution:

```text
Θ_(t+1)|_U = Θ_t|_U + Γ_U(j_t|_∂U, dφ_t|_∂U)      only covectors that reached U's interface
```

The normal law `H += w |f⟩⟨f|` is one instance; `HolonicWorldReturnDeposit` proves that a route
deposits only at its ends. `Objects/Deposition` proves locality, the Joule/Tellegen ledger, that a
deposit bends the next current split (1/3 → 5/16 on two parallel edges), that the constitution is a
sufficient retention for every solver while the last flux is not, and that the constitution is
**not minimal**: `(1,1)` and `(2,2)` have identical futures. Retention is therefore the
future-sufficient **quotient of the constitution** (`Standing.standingLaw_exists_iff_future_factors`),
never a record of the fluxes that shaped it. One law covers both of Brandon's physical pictures:

```text
flux from constitution    j = ⋆_Θ dφ,  ∂j = σ                               JunctionLaw, HodgeReceiver
constitution from flux    Θ ← Θ + Γ(j)                                       deposition
next growth               ∝ |⟨dφ, e⟩|^η on frontier cells e                  dielectric breakdown [standard]
```

Lightning: breakdown raises conductance on grown edges (the leader is a spanning tree), attachment
adds a chord, the return stroke re-solves the first line on the changed `Θ`, and the new potential
sets the next growth measure — a return stroke bounds the next. Water and canyon: the flow carves
through deposition (Exner) and the carved constitution directs the flow. The chain is Markov on
`(Θ, φ)`, not on events. Joule heating is `⟨dφ, ⋆dφ⟩`; induction is the coexact part.

### 9. Ratio

[definition] **A ratio is "one per two" before it is a number.** `1/2` means one per two, and in
the same chart the float `0.5` names the same relation. The ratio keeps its two comparands, their
units and its presentation. Its arithmetic includes the operations that reading `0.5` erases:
- **Division with remainder** `a=bq+r` keeps divisor, quotient and remainder. Modulo is the
  residue face, and winding/carry is the lift. `Geometry/Farey` and `Geometry/PhaseCarry` own
  these today.
- **Inversion** keeps its nonunit/zero fibre instead of inventing a reciprocal
  (`Foundation/TransportLift`).
- **Jets** are its rates of change: a ratio of differences is a derivative.

Exactness is the default; nothing here is an approximation that destroys information.

[proved-derived] **Radix division carries a remainder and emits digits** (Brandon, September 25:
"`3 % 8` … the return is defined simply as `3`, it doesn't seem right to me … there are directions to
it that you have to choose as an operator"; audited by Sol).
- For `a ≥ 0`, `b > 0` and base `β ≥ 2`, write `a = bq₀ + r₀` with `0 ≤ r₀ < b`. Then
  `βrₙ = b·dₙ₊₁ + rₙ₊₁`, with `0 ≤ dₙ₊₁ < β` and `0 ≤ rₙ₊₁ < b`. At every depth,
  `a/b = q₀ + Σ_(j≤N) dⱼβ^(−j) + r_N/(bβ^N)`.
- The digit is that step's quotient (the carry); the remainder is its residue face.
  `3/8 = (0.375)₁₀ = (0.011)₂` is exact finite-radix notation.
- `3 mod 8 = 3` reports the remainder correctly. The typed division also keeps the divisor `8`, the
  quotient `0`, the operand direction and the reconstruction equation
  (`Foundation/EuclideanResidueTransport`).
- The remainder navigator is multiplication, `r ↦ βr mod b`, not the addition odometer of
  `Geometry/PhaseCarry` (`+1` with an upper carry). In base 2, `3/8` runs `3 → 6 → 4 → 0`: not
  invertible, so no conjugacy to the odometer exists in general.
- **Termination and period** (on the reduced denominator). Reduce to `a′/d` with
  `d = b/gcd(a, b)`, and split `d = d∥·d⊥`, where `d∥` holds the prime powers whose primes divide
  `β` and `gcd(d⊥, β) = 1`.
  - The expansion terminates exactly when `d⊥ = 1`. The preperiod is
    `max_(p | d∥) ⌈v_p(d)/v_p(β)⌉`.
  - If `d⊥ > 1`, the eventual period is `ord_(d⊥)(β)`, the multiplicative order of `β` modulo `d⊥`.
  - `3/6 = 1/2` terminates in base 10 although `3 | 6`. `1/7` repeats with period 6 in base 10.

[proved-standard] **Euclid supplies one directed address.**
- Repeated floor division of a positive rational gives its regular continued fraction, whose
  quotients are the run lengths of its Farey/Stern–Brocot word (`Geometry/Farey`,
  `navigator::LockAddress`). That word's lock denominator is distinct from a radix expansion's
  multiplicative-order period.
- Bézout: `aℤ + bℤ = gcd(a,b)ℤ`, the smallest additive subgroup containing both. For reduced
  denominators `b, d`, `(1/lcm(b,d))ℤ` is the coarsest grid carrying both fractions.
- The rounding rule chooses a different descent:
  - floor gives the regular continued fraction;
  - nearest, with a declared tie rule, gives the nearest-integer continued fraction. The lattice
    split (Decision 22) uses nearest rounding but constructs no such word.
  - ceiling gives the negative, Hirzebruch–Jung, expansion `x = b₁ − 1/(b₂ − …)` with `bᵢ ≥ 2`.
    For the cyclic quotient surface singularity of type `1/n(1,q)`, the expansion of `n/q` gives the
    minimal resolution's chain of rational curves with self-intersections `−bᵢ`.

[interpretation; design obligation] **Where the word is kept.**
- Carry a reduction as a directed navigator word when an admitted receiver can distinguish its
  operands, rounding rule, quotient sequence or reconstruction fibre.
- When every admitted future reads only the rational value, a canonical representative suffices,
  once the action is shown to descend through that quotient.
- In the Rust core, `ratio::Presentation` keeps the undivided pair, while `Rat` is a reduced scalar.
  The hot paths carry integers over a shared denominator and reduce once per entry.

[definition] A **ratio** compares two Holons, two coholons or two transports and always has
types/units: it says "this happens as it relates to that happening". It is carried as the undivided
pair (`CrossRatio`), or as a lift fibre when the denominator is not a unit (`TransportLift`). Every
ratio is both an instantaneous reading and a continuing calculus over its classes:

```text
ratio          R = Ĝ_(T←H)
log            ℓ = log R, winding as the branch            Turn, PhaseCarry, Zeta/Winding
first order    R⁻¹dR (Maurer–Cartan; pure gauge g∂g⁻¹)      HolonicGaugeCovariance, CellHolonomy
jet            (ℓ, dℓ, d²ℓ, d³ℓ, …): velocity, acceleration, jerk, snap, crackle, pop   JetStaircase
projective     Schwarzian (second-order invariant of the cross-ratio) [standard]
```

**Loss is the ratio of the produced and target Holons**: `ℓ=log Ĝ_(T←H)`, with the lifted complex
cross-entropy (`InformationDifference`) as its face reading and `R⁻¹dR` as the learning covector.
`Objects/Ratio` proves: `exp ℓ_i = z^T_i/z^H_i` with `ℓ_i` in the ratio's lift fibre (a `2πiℤ`-torsor);
the lifted cross-entropy excess `= (2/ln2) Σ T_i ℓ_i`; the logit derivative of its real part
`= (H_j−T_j)/ln2 = (2/ln2) Σ T_i Re(R_i⁻¹∂_jR_i)`; the winding shift of the imaginary part; the
log-derivative product law as a gauge transform; and the second-order jet with its lattice form.
`Objects/RatioPhase` and `Objects/RatioBlock` add the phase covector, continuous-lift existence, `det(exp A)=exp(tr A)` with
`tr log R` in the determinant's lift fibre, and the Schwarzian's Möbius invariance. **Descent reads the magnitude:** the
real part (KL) is already a nonnegative cost; the imaginary part is an oriented displacement, so learning descends
`½Σ_c q_c Δ_c²`, `Δ_c = φ^T_c − φ^H_c + 2πn` (winding-aware), and the signed phase excess is reported, not descended
(ruling of September 22 after a signed push produced a −17,534-bit excess).

### 10. Receipt

[definition] A **receipt** is a field of readings over a partition of the complex, each region in
its own frame and clock. There is no global scalar and no global gradient: a region's readings and
its deposition respond only to action that actually propagated to its interface, transported into
its frame (a comparison across regions carries the clock-rate ratio at the interface, as a
gravitational redshift does). Each region reports the distribution and variability of its readings
over its own ticks — as heart-rate variability reads a cardiac oscillator's tick intervals — joined
to the flux measured along its interface. Owners: Lean `Foundation/{PresentationCost,SituatedInformationRate}`
(Pareto frontier of presentations, rate laws); Rust `holonics::{ratio::work::ExactWork,ratio::surprisal}`;
history [`presentation_cost.rs`](https://github.com/brandonrdug/holonics/blob/13f8c734/crates/holonics-cuda/src/presentation_cost.rs) (energy and
erasure axes owed) and [`landauer.rs`](https://github.com/brandonrdug/holonics/blob/13f8c734/crates/holonics-cuda/src/landauer.rs) (erasure only).

[definition] **To receive is to measure and compare.** The receiver is a *role* played by a
participating Holon at a port. It has its own material, current, frame, clock and next state.
Reception is an interaction:
`I_C(|H_S⟩,|H_R⟩)=(|H'_S⟩,|H'_R⟩,f_R)`
It changes both participants and returns the face `f_R` with its receipt: source, receiver,
locus, frame, clock, grain and unresolved fibre. Every returned value is received this way, and
is dilated to what witnessed it. A moving receiver adds its own variation term
(`D_Rρ·X_R` beside `D_Sρ·X_S`). `Ratio::between` compares two receipts only after their common
transport, keeping both operands and the winding. The present `HolonLaw::receive` is the passive,
zero-storage specialization of this operation.

[definition] **Measurement conventions**
([history](https://github.com/brandonrdug/holonics/blob/13f8c734/docs/DEVELOPMENT.md#performance-and-information-measurements)). A timing, rate or
energy reading is an exterior face of a receipt: it is recorded and compared, and it is never a
coefficient of a law. Exact resource vectors (`ExactWork` with its `WorkBudget`) and a device's
capacity census are owner operands at their stated scope. This is not a ban on measuring or
optimizing performance.
- A **face delivery** completes a requested receiver output (a rendered image, a decoded text
  section, a solved family). An **owner update** completes one admitted successor at its
  continuing owner. They are the scoped analogues of frames and ticks. A device launch, a symbol,
  a source observation and a successor are different counts, and a forecast can deliver a face
  without advancing its body.
- Rates are counts over an interval `dt > 0` of a named clock, `N_face/dt` and `N_update/dt`. Disjoint
  serial windows aggregate as `ΣN/Σdt`, never as a mean of reciprocal latencies. Under `t'=at+b`,
  `a>0`, a rate becomes `r/a`; reversing a clock flips an oriented quotient and reverses no
  dissipation.
- Over one occurrence family, `bits/s = occ/s × bits/occ`. A code reading is
  `Σ_k −log₂ q(y_k | conditions_k) / dt`, and, for an expected finite positive-distribution
  reading, its expected form is `r·H(p,q) = r·H(p) + r·D(p‖q)`.
  An event rate alone is not a cross-entropy. The alphabet, conditioning, probability receiver and
  log base are kept; an observed event of zero code probability costs infinitely or returns a
  missing code, never a finite substitute.
- **A missing counter is unknown, not zero.** Code lengths, phase differences, joules and
  coordinate time are distinct quantities until a constitutive map joins them; bits per joule need
  an energy receiver with its sampling interval and baseline. A timeout records an unfinished run
  at its deadline, not infeasibility.

[proved-derived; formal-checked] `Foundation/SituatedInformationRate` proves the clock transport, the serial composition, the
factorization `bits/s = occ/s × bits/occ`, the entropy/KL rate split and the resource ceiling
`N·w_min ≤ W ≤ B·dt ⇒ N/dt ≤ B/w_min` for positive `dt, w_min` (a workload bound, not a universal speed).

### 11. Holarchy

[definition] A **Holarchy** is a Holon perceived as a compound of distinct Holons, always in a
context (Brandon, September 23). Its decomposition is spatial; its parametric orientation carries
its aeons (§12), which it decomposes in time the same receiver-relative way. It is what
`Holon::interconnect` returns: the joined whole
together with its retained constituents, incidence, typed gluing and restrictions. When the join
does not close, `interconnect` returns a typed gluing defect. Its constituent family may be
implicit or recursively generated, carried by a constituent navigator. Gluing retains namespaced
port and cellular interface maps, navigator provenance and child-scoped restrictions. A port join
checks units and cancels equal-effort/opposite-flow interface power; cellular maps commute with
boundaries and respect oriented connection transport. Pumps join only under declared compatible
joint-clock maps.

[definition] **A Holarchy's quantities belong to the receiver.** It has no fixed count, mass or
category. `view(receiver, grain, clock)` returns the constituent faces, interface flux and
unresolved classes that the receiver distinguishes at that grain. One grain counts continents,
another islands, another molecules: a telescoping coarse-graining. `count` requires a finite,
exhaustive, disjoint and distinguishing partition certified by that receiver; otherwise it remains
unresolved. `refine` passes between grains through the tower's restrictions and returns a commuting
scale square or its defect, including a reading that separates a merged fibre. A shared physical
flux cancels once on every joined face, whatever the grain
(`smoothSolutionOn_twoCell_sharedFace_gluing`). The whole can receive, act and compose with other
Holarchies. Formal ingredients are `Foundation/{HodgeReceiver,IwasawaTower,FractalPacking}`: a
count can be stable while its representative changes, and a quotient's cardinality depends on the
restriction.

### 12. Aeon, epoch and cycle (the passage of time)

[definition] Brandon, September 24 ([record](../research/records/2026-09-24_THE_AEON_EPOCH_AND_CYCLE_STANDARDIZE_THE_PASSAGE_OF_TIME.md)). These three terms are the standard
vocabulary for time.
- **Aeon:** an arbitrary container of causality in time, part of a Holarchy's parametric
  orientation. It is the stretch of the motion between two occurrences: a 1-chain in the lift of
  the navigators' joint clock torus, retaining winding. It is not an interval of a privileged
  clock.
- **Epoch:** a division of an aeon. A receiver ticks when the motion crosses its section `Σ_R`,
  and those ticks partition the aeon into epochs at that receiver's grain. Coarsening merges
  epochs: the first return to a sub-section, or the Odometer's carry.
- **Cycle:** a closed loop, meaning completeness rather than a duration. Its readings are whole
  windings, gauge-free and conserved.

[definition] **Elapsed time is a pairing:** `t_R(γ) = ⟨ω_R | γ⟩ = n_R + r_R`.
- `ω_R` is the receiver's clock, a closed 1-form: `dθ_R`, or the observer covector `−U_μdx^μ`.
- `n_R` is the whole windings (the quotient) and `r_R` the open phase (the remainder).
- No frame is privileged. The rate between two receivers is the ratio of their readings.
- Readings add under concatenation, with the carry cocycle.
- Epoch ticks count the flux of the motion through `Σ_R`.
- Across grains, the mean number of fine epochs per coarse epoch is the section-measure ratio
  (Kac, under its hypotheses).
- Two clocks lock at their Farey address, where every `q`-tick aeon is a cycle. Otherwise their
  natural epoch grains are the continued-fraction convergents of their frequency ratio.
- An aeon boundary is where the future-sufficient quotient is taken.

"Session", "episode", and counters named `epoch`/`cycle`/`generations` that serve as one global
clock are retired as terms for time.

[definition] The record states the general objects built on these terms:
- **A1:** the aeon groupoid, with clocks as time connections;
- **A2:** Hodge-decomposed time. State time is exact and boundary-read, winding time is
  harmonic and cycle-read, and production time is coexact curvature;
- **A3:** the asymptotic cycle;
- **A4:** entropy under a change of clock (Abramov/Kac);
- **A5–A6:** production as the positive non-closed clock, with `σ(γ) = D(P_γ‖P_{Rγ})`;
- **A7:** the first law of learning, cross-entropy change split into exchange and deposition;
- **A8:** the dynamical zeta, the machine's trace faces;
- **A9:** spectral placement ⇔ reversibility;
- **A10:** the production functional, zero on the distinguished cycles;
- **A11:** the singular aeon.

The record also gives their graded Hodge, spectral and Navier–Stokes instances, and the Lean and
Rust obligations in construction order.

## Keys, locks and navigation

[definition] Brandon's Enigma/Bombe reading, September 21: the rotor is a parametron ring whose
stepping is a winding with carry (`Odometer`); the plugboard and reflector are fixed material and a
boundary involution, and a passage returns through the producing operands (`A⁻¹FA`); the key is the
**initial configuration** of the navigators; the Bombe infers that configuration from pairwise
**loop closure** over the menu of admitted contacts (`HelicalPairInteraction.menu_loop_closure`: a closed menu path closes
exactly when the stage word fixes its boundary image).

[project-postulate] Every action is a key: an action expression and its antecedents, placed against
a constitution (the lock), induce a consequence as flux only when they fit. Walking, typing a
command, tying or untying a knot, a word that eases or wounds a listener, solving a puzzle — each is
finding a configuration under which already-present navigator relations become relevant. A dormant
mode is available but inactive until an antecedent that fits it arrives. **Learning is locating
keys**: inferring the configuration and gauge of relevant navigators from loop-closure constraints,
which prunes the search (compression) and yields the route (navigation). Teaching supplies keys;
a name is a key to a person; a coordinate is a key to a cell. The inference is general; this
repository's applications are language, mathematics, code, perception and motor control, and no
cryptanalytic application is pursued.

## Emanation and resonance

[proved-derived; formal-checked] A drive splits uniquely and `C`-orthogonally into its component in
the constitution's mode space at the drive's eigenvalue and the complement
(`Compression/Core/Resonance`). The resonating part (RIDE) needs zero effort and keeps the mode
energy's exchange law (`modeEnergy_conserved`). The emanating part (FOUND: off-resonance, or founding
a new mode) always needs nonzero effort, but the work it exchanges, `dE/dt = ⟨f, ẋ⟩`, can be zero:
a clamp holds without exchanging energy. "Emanating costs effort" is the law; a fixed work price is
not. Stored energy in the constitution is stored (held, not propagating), with inertia `E/c²`;
propagating current is emanation; the LC exchange converts one into the other while conserving
energy. The physical floors are Landauer (erasure only), Margolus–Levitin (operations per unit
energy) and Bekenstein (stored bits per energy × radius). They are floors, not an exchange rate,
and the repository refuses a fixed mass per bit.

[definition] π and `e` are constraint identities; the identity is the navigator and carries no
error. Digits are a receiver face (`RadixWindowReceiver`), and error enters only in how a face is
attained. π's base-16 digits are its address word under `x↦16x mod 1`, the same address map as the
source moment. Digit extraction jumps to position `n` by the navigator power `Uⁿ` (repeated
squaring): O(log n) space, still about `n log n` time. **Partial navigators** are the compiled
binary-splitting blocks `(P,Q,T)`, composing associatively (`RatioSeriesTransport.Block.compose`)
and sufficient for every continuation; they are extendable where stored digits are not. In Levin's
`Kt=|p|+log t`, a window at offset `k` costs about `2 log₂ k` against `ℓ log₂ b` for the literal. The
optimal plan is a Pareto frontier over (description bits, work, time, peak space, erasures, energy)
under a random-access deadline; no single optimum is proved, AGM is `O(M(N) log N)`, the only proven
lower bound is Ω(N), and base-10 log-space extraction is open.

## The targets

[project-postulate] RH, Hodge, complex Euler/Navier–Stokes and BSD are targets of compression and
landmark discovery ([the line](plans/THE_REBUILD.md#the-line-the-rebuild-serves)), not a
separate category. Their joins to the objects:

[definition] Navier–Stokes: velocity is a coholon, vorticity `du♭`, pressure the exact part,
Kelvin circulation a holonomy pairing, the Lamb term the cross-current. Hodge classes: which harmonic
coholon classes are realized by actual Holon cycles. Spectral placement: `FosterTanks` reads zeros as
LC tanks and `ZeroPairLock` gives lock ⇔ `σ=½` ⇔ positive Foster inductance — a parametron
condition. Whether the relevance theorem yields relative completeness in the spectral chart is open:
it needs a persistent frontier current (see §7).
