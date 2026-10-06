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

[definition] **The law and its motion are one statement.** `H` is the law and its ports; the ket
`|H⟩` (§1) is a **motion admitted by `H`**: flows and efforts in `𝒟` satisfying `𝓔` along the
navigators' clocks. A state is a point on that motion, and a trajectory is the motion read over an
aeon. This guide owns the statement; [THE_MACHINE](THE_MACHINE.md), [HOLON](HOLON.md) and
[HNN_FORMULA](HNN_FORMULA.md) cite it. Receivers are Holons
joined at ports; a passive coholon is the zero-storage limit that reads an effort. Interconnecting
Holons through their ports yields a Holon, which is the recursion. Passivity is a proved property,
never assumed: learned or nonlocal relations enter with their actual power term. Linear SSMs,
diffusion, Maxwell (Stokes–Dirac on the de Rham complex) and Euler/Navier–Stokes (Lie–Poisson plus
viscous resistance) are specializations; the occurrence Holon of `Foundation/Holon.lean` is its event
chart. The Lean foundation is `Holonics.Framework.HolonObject` (`Holon/{Port,Dirac,Complex,Element,
Navigator,Restriction,Law,Conformance}`); the Rust core `holonics` mirrors it facet by facet, and every
later owner implements or charts it.

<a id="operator-contract"></a>
[definition] **Operator contract** (source/consumer status reconciled October 6;
[the rebuild](plans/THE_REBUILD.md)).
Each object's operations and their owners are listed below. The *current* column is the
source owner; a receipt establishes only its declared consuming checks. The *target* column is
its home in the main `holonics` library and the
Lean `Holonics` library in the rebuild. A target name is not importable until its owner is
built. Each rebuild step updates this table in the same commit.

| Object | Operations | Current owners | Target |
|---|---|---|---|
| Ratio | `present`, `compare`, `compose`, `invert` (nonunit fibre), `div_rem`, `residue`, `lift`, `jet`, `log` with branch | Lean `Objects/{Ratio,RatioPhase,RatioBlock}`, `Foundation/TransportLift`, `Geometry/{PhaseCarry,CrossRatio}`, `Geometry/Farey`; Rust `holonics::ratio::{Rat,Presentation,ExactOrdering}` (the undivided pair, compared by cross-multiplication), `holonics::ratio::linear` (inversion with its fibre), `holonics::geometry::winding::Odometer`, `holonics::navigator::address::LockAddress`, `holonics::ratio::ring::{ExactRing,ModularWords}`, `holonics::ratio::exponentiated::RatioFamily`, `holonics::ratio::surprisal`, `holonics::holon::contact::Alignment` (the undivided squared-cosine face); `holonics::ratio::exponentiated::CarriedPower` (`2^(n + k/L)` as a carry and a phase in `ℚ(θ)`, Lean `Objects/Ratio/CarriedPower`); `ratio::linear`'s integral chart (products summed over integers and reduced once per entry; a fraction-free inverse) | `holonics::ratio`; `Holonics.Objects.Ratio` |
| Complex, frame, clock, carry | `boundary`, `transport`, `transport_rate`, `join_axes` (commuting square or defect), phase lift | Lean `Holon/Complex`, `Geometry/*`; Rust `holonics::geometry::complex`, `holonics::navigator::Clock`, the frame carriers `holonics::geometry::{RatVec3,RatMat3,AffineMap3,Axis}` over `holonics::ratio::Rat`; block transports in `geometry::complex::ConnectionIncidence` (Lean `Holon/Complex.{blockIncidence, blockWalkRead_incidence, block_cell_curvature, block_flat_closed}`) | `holonics::geometry`; `Holonics.Geometry` |
| Swing (motion) | `move` (`x ↦ Mx + b`: its multiplier, pivot and kind), `split` (turn and boost against a receiver's metric, with the energy law), `compose`, `kind` (turn, boost, free fall, half-turn with a boost; `tr²/det`), `factor` (turn · boost · shear), `half_turn`, `pantograph` (a scalar move about an anchor), `tick` (oriented section crossing), inner fibre of a coarse move, `junction_scattering` (`2P_D − I`) | Lean `Geometry/Motion` (the split, the three kinds, the Iwasawa factors, pivots, the multiplier as a cross ratio, the path jets), `Geometry/{AffineSwing,SwingPotential}` (the half-turn), `HolonicsResearch/Zeta/Seam` (ξ is invariant under the half-turn about ½), `Foundation/FractalPacking.reflect_eq_swing`, `Geometry/{Swing,SwingBridges,Navigation,HolonicPantographicSwingJets,HolonicClockedPantographicSwing,HolonicClockedPantographicSwingApparatus}`, `Compression/Landmark/FixedPoint` (Möbius pivots and multipliers), `Physics/Spacetime/{Boost,Wigner}`; Rust `holonics::geometry::swing` (`half_turn`, `composed_translation`, `pantograph`, `harmonic_conjugate`, `swing_pair`) over `ℚ^d` anchors (`RationalPoint`), which the HNN junction's scattering calls (`hnn::propagation::scattering_about`, about the participation anchor); `holonics::geometry::motion` (`Move`: the move pair `(v, v′)` over `ℤ[i]` carried undivided, its `kind` decided without division where a velocity vanishes, the traction disk, the power and the signed turn), which the chase's traction law, slip test and viable tube read (`holarchy::terrain::{chase, pursuit}`); `holonics::navigator::trace::SiteKind` (the projective kinds) | `holonics::geometry`; `Holonics.Geometry` |
| Pair and tube charts | `screw_pair` (two motions, relative jet), `tube` (longitudinal transfer), `restrict` (transverse, gluing unique/plural/obstructed), neck, fold, junction | Lean `Transport/{HelicalPairInteraction,ContinuingTube,WorldTube,Neck,Fold,JunctionLaw,JetStaircase}`, `Geometry/PairResonance`, `Foundation/{ContinuingTower,IwasawaTower}`; Rust `holonics::geometry::screw`, `holonics::holon::restriction::{tube,tower}` | `holonics::geometry`; `Holonics.Geometry` |
| Pair contact | `slip` (`J=[v_a\|−v_b]`), `quadrance` (`Q`, `DQ=2J*Δ`, `D²Q`), `material` (`M_contact=ΣwJ*DJ`), `power` (resistive element on slip), `lock_address` (Farey), `chain` (serial screw words and contact rows) | Lean `Transport/{HelicalPairInteraction,HolonicInteraction,HolonicChain,SerialScrewChain}`, `Geometry/PairResonance`, `Holon/Conformance.pairContact_resistive`; Rust `holonics::geometry::screw::{ScrewPair,PairQuadranceJet,SituatedScrew}` (the pair geometry), `holonics::holon::contact` (`PairContact`, `ContactMaterial`, `Alignment`, `SerialChain`), `holonics::navigator::address::LockAddress` | `holonics::holon::contact`; `Holonics.Holon` |
| Parametron | `store`/`exchange` (`C`, `L`, `ω=1/√(LC)`, mode energy), `pump` (a periodic modulation of the constitution: a declared schedule, or one modulated by the crossing cells), `floquet` (the monodromy of one period, the multipliers' placement about a circle, the certificate `M_TᵀGM_T ⪯ ρ²G` by inertia, the exact decision passive/edge/growing, the consumer's bound), `lock` (half-turn sheets, phase-sensitive amplification, the Ising site's exchange polynomial and logistic face, coupled locks), `tick` (section crossing), `read` (the perceptron face; the bank's relative-phase class), `hear` (modal coupling; dormancy) | Lean `Objects/{Parametron,ParametronLock}`, `HNN/{Ring,Floquet}`, `Physics/{PhaseCarrier,CoupledIncidence,HolonicMeasuredParametron,HolonicTorusParametronRealization}`; Rust `holonics::holon::parametron` (`Parametron`, `Carrier`, `Population` (a coupled parametron population), `pump_storage`, `ring_crossings`, `SymmetricQuartic`, `LoadedParametron`, `PeriodicDomain`, `PeriodicLock`, `MountedParametron`), `holonics::holon::law` (`ReferenceHolon::advance`, explicit `Scheme::QuarticKickDrift`), `holonics::hnn::ring` (`PumpSchedule`, `ResonatorOperands::scheduled`, `Floquet`, `attain_metric`, `FloquetCertificate`, `FloquetReading`, `FloquetBound`, `lock`, `ReceivingBank`, `BankReading`) and the pumped-LC witness of `holonics::holon::conformance` | `holonics::holon::parametron` (the storage, the pump, the period map and the lock: the library spine's S1; `hnn::ring` keeps only the ring's loaded port); `Holonics.Objects.Parametron` |
| Navigator | `configure` (initial configuration: the key), `advance` (own clock, carry), `restrict` (scale square), `address` (source word), trace faces and the dynamical zeta, lock address, scale zeta and complex dimensions, `release` at tolerance | Lean `Holon/Navigator`, `Foundation/{FractalPacking,FractalString,NavigatorInference}`, `Transport/{NavigatorTraceFaces,SourceMoment,ReflectiveContinuation}`; Rust `holonics::navigator` (`Navigator`, `Transport`, `Clock`, `PhaseLift`, `address`), `holonics::navigator::trace::{SiteFactor,Machine}`; `holonics::navigator::Transport::Map`, a finite-order port map on `ℤ/d` with `order` and `compose` (Lean `Holon/Navigator.{map_pow_mod_order, map_turn_lossless, map_compose_order_pos, map_compose_order_dvd, mapRotor_order}`) | `holonics::navigator`; `Holonics.Holon.Navigator` |
| Holon | `advance` (state, bond, energy balance), `interconnect -> Holarchy`, `contact` (a pair contact as element), `continue` (through a tube), `restrict`, `depose`, `pullback` | Lean `Holon/{Law,Port,Dirac,Element,Navigator,Restriction,Deposition,Reaction,Cayley,Conformance}`, `Foundation/{Holon,Lineage,ConnectionLineage}`, `Objects/Deposition`; Rust `holonics::holon` (`law`, `port`, `dirac`, `element`, `restriction`, `deposition`, `conformance`, `contact`, `parametron`; `reaction` retired September 28), `holonics::navigator` | `holonics::holon`; `Holonics.Holon` |
| Receiver and receipt | `interact`/`receive -> InteractionReturn` (both participants' next states, face, receipt, boundary currents, power balance, unresolved fibre); `Ratio::between(receipts)`; `width`, `release` (the one decision law: threshold commit, certified draw `draw` at tolerance zero, probe with its `ProbePartition`, typed refusal; caller-declared decision and tolerance checks); `chord` (transfer object; Lean only, its Rust realization retired at U3, history at `c10acca9`, its laws in [RECEIVER_HOLARCHY](RECEIVER_HOLARCHY.md#the-causal-chord)); `heard`/`null`/`listened` (face, grain and reached action) | Lean `Holarchy/{Reception,Receipt,Hearing}`, `Foundation/{Receiver,ReceiverRelease,Standing,CausalChord,ReceiverAtlas,PresentationCost,SituatedInformationRate}`, `Transport/ChangingReceiver`, `Objects/Pairing`; Rust `holonics::receiver::reception` (`JointLaw::interact -> InteractionReturn` on the solved joint step, `ReceiverFace` and its three-term `FaceMotion`, `JointLaw::of_holarchy`; `HolonLaw::receive` is its zero-storage specialization `JointLaw::reading`), `holonics::receiver::receipt` (`Receipt`, `ReceiptLaw`, `ReceiptRatio::between` and `follow`, with `ratio::Presentation::follow`), `holonics::receiver::face` (faces and passive law; the face read at a grain, `GrainCell` and `grain_exponent`), `holonics::receiver::release` (the chaser's certified capture and probe return through it: `receiver::population::chaser`), `holonics::ratio::work::ExactWork`; history [`presentation_cost.rs`](https://github.com/brandonrdug/holonics/blob/13f8c734/crates/holonics-cuda/src/presentation_cost.rs), [`landauer.rs`](https://github.com/brandonrdug/holonics/blob/13f8c734/crates/holonics-cuda/src/landauer.rs); guide [RECEIVER_HOLARCHY](RECEIVER_HOLARCHY.md); the generic `receiver::reception::InteractionReturn<Fw, Pb, Dp, Ph, Rc>` of `Component`s and `receiver::release::DecisionRule` (the data form of `DecisionLaw`) | `holonics::receiver` (release operations); `Holonics.Receiver` |
| Egg population (the receiving role's mixture over candidate families; a composition, [the egg](#the-egg-a-generator-read-as-a-whole)) | `receive` (Bayes, the discrete replicator; death at zero likelihood, an exchange that keeps the seed), `face`, `code` and `receipt` (the likelihood telescope, enclosed), `found`/`refound` (birth from reserved mass), `birth` (a reached covector closed under the admitted transports founds a family: `E T_a = U_a E`), `compose` (a keystone's port, the chain rule), `dormancy` (a silent layer held through its aeon, the fixed share), `evolved` (the prior over identities across aeons), `collapse`/`split` (species relative to the admitted future), `merge` (a release or a priced merge); the byte-tree text line's operations (`receive_partitioned`, `select_family`, `release_response`) retired September 30 ([laws kept](RECEIVER_HOLARCHY.md#the-retired-byte-tree-text-line)) | Lean `Compression/Landmark/Context/{Population,Composition,Dormancy,Evolution,Merge,Birth}` over `Computation/HolonicAdjointNormalization.{bayes_eq_face, bayes_eq_discrete_replicator, replicator_eq_zero_iff}`; Rust `holonics::receiver::population` (`Population`, `Family`, `Survivors`, `KeyFamily`, `Work`; `families` (`RotorKeys`, `GratingParity`, `GratingSheet`), `birth` (`Closure`, `FoundedFamily`, `TransportBirth`, `SectionFounding`), `dormancy`, `composition`, `evolution`, `species`, `merge`, `chase` (`ChaseFamily`), `chaser` (`MachineChaser`)). `holon::parametron::Population` is a different object, a coupled parametron population | `holonics::receiver::population`; `Holonics.Compression` (`Landmark/Context`) |
| Holarchy | `interconnect -> Holarchy` (typed port/cellular gluing); `whole`, `view(receiver, grain, clock)`, `count` (receiver-certified finite partition), `refine` (commuting square or defect), `parametric` (the aeons' clock lift) | Lean `Holarchy/{Join,View,Receipt,Reception,Globe}` (`Constituent`, `interconnect_ok_iff`, `power_balance`, `shared_face_cancels`, `Holarchy.parametric`, `HolarchyGlobe`); Rust `holonics::holarchy` (`Holon::interconnect -> Result<Holarchy, GluingDefect>` over a `Gluing` checked against both Holons' own units, complexes and pumps, navigators joined; `Holarchy::{whole, interface_fibre, power_balance, flux, pump_lock, parametric}`), `holonics::holarchy::view` (`Holarchy::{view, count, refine, block_boundaries, interface_flux}`); Rust has no globe consumer; `Holarchy` keeps its constituents, gluing and layout and assembles its whole only when read (block-local certification) | `holonics::holarchy`; `Holonics.Holarchy` |
| Terrain (the cells a declared Holarchy emits, with its exact truth) | `Draw` (the seeded Weyl draw) and each terrain's `draw` (its cells beside their exact truth: keys, constitution, rate and key description); `emit`; the moiré's `parametric` (the rings' joint clock) and pair locks; the tree source's `passage`, `weighting_bound` and `recovery`; the chase's `traction_bound`, `fibre` and `futures`, and the pursuit's viable tube | Rust `holonics::holarchy::terrain` (`Draw`; `moire` (`Moire`, `MoireFamily`), `source` (`TreeSource`), `crib` (`RotorCrib`), `switching` (`Switching`), `chase` (`Chase`), `pursuit`; the arithmetic terrains were retired September 29 with the arithmetic eggs, history at `1b374d46`); its Lean joins are the owners it reads: `Aeon/Clock/{CarryWord,Epoch}`, `Compression/Landmark/Context/Standing.leaf_standing`, `Geometry/Motion` (the traction disk) | `holonics::holarchy::terrain` |
| Aeon, epoch, cycle | `reading(clock, aeon) -> (windings, phase)`, `concat` (with carry), `reverse`, `epochs(receiver, grain)`, `carry_word` (the epochs of a rate clock at another clock's sections; recurs iff the joint clock has a cycle), `coarsen` (induced section), `is_cycle`, `rate`, `hodge_split`, `production`, `zeta` | Lean `Aeon/Clock/{Groupoid,Reading,Winding,Lock,Epoch,CarryWord}`, `Aeon/Production/{HodgeTime,Kac,PathReversal,Zeta,FirstLaw}` over `Geometry/PhaseCarry`, `Transport/CellHolonomy`, `Objects/Pairing`; Rust `holonics::aeon` (`Aeon`, `Cycle`, `ClockLift`, `reading`, `rate`, `Epochs`, `EpochTower`, `TwoClocks`, `hodge_split`, `MarkovChain`, `learning_balance`; `zeta` retired September 28, Lean `Aeon/Production/Zeta` holds it); `aeon::EnclosedLedger` (the enclosed first law, Lean `Aeon/Production/FirstLaw.{ledger_telescopes, ledger_is_first_law, enclosed_contains, enclosed_telescopes}`) and `ClockLift::forward` | `holonics::aeon`; `Holonics.Aeon` |
| Physical instances | fluid `face_flux`/`advance`; wave `propagate`/`interfere`; thermal `exchange`/`diffuse`/`entropy_production`; spacetime `einstein_residual`/`observer_current`; information `apply` | Lean `Physics/{Fluid,Wave,Thermal}/*` (cells reflect/join, control volume, complex fluid, singularity flows, closed bodies; interference, telegrapher cone, radiation; two-cell exchange, viscous port, Schnakenberg, chain axes), `Physics/Spacetime/{Boost,Einstein,NonClosedClock,StressEnergy,Wigner}`, `Physics/Information/{ClockJoin,CrossEntropyRate,PortWork}`, `Physics/*`, `Holon/Conformance`, `Fluid/{NavierStokesLambCurrentCell,NavierStokesCurvedTransport}`; Rust `holonics::physics::{fluid,wave,thermal,spacetime,information}`, `holonics::aeon::join_axes` and `holonics::holon::conformance`; missing: fluid time `advance` with its pressure solve, many-cell `diffuse`, and K4's owed list (#62) | `holonics::physics`; `Holonics.Physics` (K3 #74, K4 #75, done) |
| Compression and landmarks | `kernel` (relevance kernel; its quotient is retention), `cokernel` (the residual to emanate or retain, with its horizon), `resonate`/`emanate` split, `cost` (description + work against the literal), `infer` (loop closure: the reflector machine's stepping stages, and the turn menu, whose stage is the rotor's own turn and whose fibre is read from the menu relation's cycles and cosets), `repair` (the located pair read the other way: a damaged passage's compatible family restricted from both sides, `f` from the antecedent and `f⁻¹` from the consequent, released at width zero or held with its plural family, and priced as the key plus the Fold's side residual), `local` (a key that is not global, read as a section over a cover: the turn menu per region, the keys glued on the overlaps through the rotor gauge in the tower's trichotomy, and the repair run per glued region only through its located key; a plural glued region keeps its fibre and restricts nothing), site kinds (rotation, null, boost; reflection, degenerate), fixed-point landmarks, identity atlas (checked coverage), constraint-identity windows, primitive cycles, the shift navigator's landmarks (the receiving tree: context-tree weighting over typed addresses, each pruned tree a candidate standing and the weight their mixture, a node's arrivals the epochs of its section, its register capped by a carry, stored where paths part) | Lean `Compression/Core/{FaceMap,Resonance,Cost,Keys}`, `Compression/Landmark/{SiteKind,FixedPoint,Identity,ConstraintIdentity,PrimitiveCycle}`, `Compression/Landmark/Context/{Tree,Standing,Epoch,Address,Carrier,LocalWeighing,ConvergenceFounding,Compaction,Capacity}` (joined to `Foundation/Standing` and `Aeon/Clock/Epoch`) over `Foundation/{CausalRelevance,ReceiverHistoryCompression,NavigatorModeQuotient,ReceiverCodeCost,NavigatorInference}`, `Geometry/TwoSidedIdentityAtlas`, `Mathematics/{RatioSeriesTransport,RadixWindowReceiver}`; target joins in `HolonicsResearch/Landmarks`; Rust `holonics::compression` (`resonance_split`, `CompressionCost`, `Menu`, `TurnMenu`, `keys::{repair, local}`, the windings law `keys::generator`; the face map is Lean's; the turn menu's fibre law, the repair's projection law and the glued region's projection law are owed in #62) and `holonics::compression::landmark`, with `compression::landmark::context` (`Landmarks`, `IdealLandmarks`, `StopPrior`, `Capacity`, `LetterFamily`, `Window`; the online context baselines `context::baseline`; it reads no `hnn` owner) | `holonics::compression`; `Holonics.Compression` (#145) |
| HNN | field law, source moments, adjoint, deposition return, execution port | Rust `holonics::hnn` (rebuild steps 4–5, campaigns 1–2, #73/#76): `field` (closing rotor rings, pair contacts, the lift point `Current`, selective stepping on the encoding's classes), `moment` (`SourceMoment`, capacity `n*`; the open reads the whole offset moment, no window), `encoding` (Holonic Encoding: a passage chart's minimal realization founded through `birth::Closure` on its declared transports, its squares and separator, U6; the one source type `Encoded`, a passage of `PortCell`s injecting into every source ring's ports with `D`, its Preimage Fibre, the boundary's labels and the located advances' digits, built only by `Encoded::identity` from a terrain's `KnownTruth` (`holarchy::terrain::known`) and by `Encoded::through` from a chart the field's own key location built (`PassageChart::located`, read in the receiving cells), THE_MACHINE guard 9; the field's entries (selective step, moment ingest, the port, the keys) take only it, a located class stepping the rings by its digits plus the carry with `D E = ρ` and `E T_a = U_a E` checked at the step, and the codec's residue port chart is deleted, October 5; the passage-founded port chart was retired September 29), `propagation` (junction scattering, element, contact two-port, global power, path attenuation), `word` (`Word`), `receiving`, `ratio` (`HolonRatio`, `RatioCovector` in the odometer chart, reading faces through `ratio::exponentiated::CarriedPower`), `pending`, `constitution` (`Constitution`, `NormalLaw` at its certified step, the certified storage growth, the carrier lattice), `retention` (the diamond and the aeon collapse), `keys` (the closing crib's key location), `port` (`ExecutionPort`) and `reference` (`Reference`, `expose`), `ring` and `contact` (campaign 2 storage/transfer laws), `chart` (the lattice word's certified inverse charts), `executed` (the located pair's deposit through `holon::deposition::CertifiedStep` and the contact slip the release reads, S2; U6's executed comparison and its certified descent move retired October 5 into key location (`keys`) then deposition, source at [`9078f103`](https://github.com/brandonrdug/holonics/blob/9078f103/crates/holonics/src/hnn/executed.rs)), `prediction` (`generate_by_bank`, the one release owner, reading `FieldMaterial` alone, guard 18) and `realization` (co-present host regions under the hardware law); the receiving parametron's storage is the compacted receiving tree `compression::landmark::context`, read by `receiving` (one family of [the receiving storage](#the-receiving-storage)); the CUDA `hnn::Resident` realizes the word and tree with return parity; `ring` joins the loaded resonator forward/adjoint/deposition; Lean `HNN/{Word,Propagation,Moment,Encoding,Normal,LatticeDeposit,LatticeWord,Ratio,Retention,Keys,Ring,Contact,ContactBreak,ModeQuotient}` (a loaded ring's future quotient, campaign 3's first construction, is Lean's alone since U2) and the rest of `HNN/` gathered by `Holonics.HNN` in the `Framework` (the diamond theorems on an abstract block operator; the concrete-tick bridge owed in #62). The prototype is in history ([`native_ecology/constitutive_fibre/field`](https://github.com/brandonrdug/holonics/tree/13f8c734/crates/holonics-cuda/src/native_ecology/constitutive_fibre/field), [`hnn`](https://github.com/brandonrdug/holonics/tree/13f8c734/crates/holonics-cuda/src/hnn)) | law and port in `holonics::hnn`; resident realization in `holonics-cuda::hnn`; `Holonics.HNN` (rebuild steps 4–5) |

The restructure's detailed contracts are in history at
[`13f8c734`](https://github.com/brandonrdug/holonics/blob/13f8c734/docs/plans/THE_REPOSITORY_RESTRUCTURE.md).

[established-bounded; source-checked] **Current HNN consumers and their remaining joins.**
These qualify the table's HNN, receiver, navigator, parametron and compression rows; they add no
new owner or general theorem. The checked source is
[`3c67beee`](https://github.com/brandonrdug/holonics/commit/3c67beee7f656798f912c974f12c482ea12c5e42).

| Operation and existing owner | Consuming relation and evidence | Remaining acceptance |
|---|---|---|
| Source admission and transport: `hnn::encoding::Encoded`, `Field::selective_step`, `SourceMoment::ingest`; CUDA `hnn::moment` and `hnn::port` | The producing chart carries classes, decoder `D`, labels, fibre and conduct. The located step reads `a_g(c)` plus carry and checks its chart squares at the consumer; identity input reads its declared lock fits. [Encoding and device-ingest receipt](../research/records/2026-10-05_THE_FIELDS_ENTRIES_TAKE_ONLY_THE_ENCODED_SOURCE.md), atlas `hnn.encoded-source-type`, `hnn.card-located-source-ingest`. | Equal class counts do not identify producing charts or clocks. Erased cells do not determine their located advances. Repair must consume the supported chart and source-time relation, or return the typed obstruction before opening the word. |
| Received source and physical word: `hnn::word::SourceOpeningReceipt`, `WordOpening::Received`, reception carry and paired pullback | [Source-entrance tests](../crates/holonics/tests/source_entrance.rs) exercise actual source material, offsets and continuing physical words. The [carry receipt](../research/records/2026-10-03_THE_RECEPTION_CARRIES_THE_INTERIOR_CHANGE_THE_SOURCE_PORT_IMPOSES_THE_MOMENT_AND_REST_IS_COMPLETE_ABSORPTION.md) states the chained balance and its boundaries. | Useful learned physical repair must join the source entrance to the reached comparison, learned receiving material and decoded boundary. A closed component balance or next-cell score is narrower evidence. |
| Retain and cold-mount: host `Resident::continuing_state`, `Reference::mount_continued`, `reference::passage` | Retain the contemporary constitution, carry, lift, optional moment, aeon, balance, kept charts, address-reader kinds, declaring phases, handles and arrived comparison. [Cold-restore tests](../crates/holonics/tests/resident_cold_restore.rs) and [PR #384](https://github.com/brandonrdug/holonics/pull/384) check the subsequent host receipt/state relation without borrowing live predecessors; atlas `hnn.resident-passage`. | Carry alone omits charts the word reads. Card passage restore, shared-clock rekey/capacity and the general action-sufficient adaptive quotient keep their own consumers and obligations in #73, #76 and #62. |
| Nonlinear pump/lock: `holon::parametron::{PeriodicDomain,PeriodicLock,MountedParametron}`, `ResonatorOperands::mount_periodic` | The existing [executed-domain and carried-cycle receipt](../research/records/2026-10-05_THE_LOADED_COMPONENT_CARRIES_ITS_ADMITTED_PUMP_CYCLE.md) is the component's claim. | The ordinary rounded word, whole nonlinear interconnection and generic asymmetric/adaptive material are separate consuming joins. |
| Release and decoding: `hnn::prediction`, physical receiving material, producing `Encoded::decoder`, `receiver::release` | `D E = ρ` is the producing reconstruction square (or its retained defect); the learned receiving map needs its own joined comparison and reconstruction relation. A reading keeps its receiver's grain, carry, phase class and remainder. [Foundation supplement](plans/HNN_ATHENA_FOUNDATION.md). | No meaningful autonomous physical-repair output or Athena product acceptance is inferred here. #148 requires the actual output, compatible fibre/keys, health, atomic transition and cold continuation. |

Implementation, builds, tests, Lean integration and source integration are Codex's responsibility;
Claude contributes architecture, derivation and review. #73 routes the host coordinator and physical
repair consumer; #76 routes the CUDA consumer and common build queue; #62 retains formal scope;
#63 and [THE_REBUILD](plans/THE_REBUILD.md) own program order. The
[comma/ghost record](../research/records/2026-10-05_THE_GHOST_LIVES_IN_THE_GAP_THE_JOINTS_OF_THE_LENS.md)
joins ratio nonclosure, turn/boost normality and six owed statements. Recursive coarse-graining and
the RH source-law join remain target work alongside Hodge and complex Euler/Navier–Stokes;
they are not a proved RH consequence of the component receipts.

[definition; agent-inferred from the consuming relations above] **Next physical-learning receipt.**
The Codex HNN coordinator owns its source/acceptance integration; the physical source/receiver
consumer joins the charted source-opening and receiving-error pullbacks to the reached deposit;
the CUDA consumer owns matching parity through the common build queue. The opening receipt
`E_after − E_before = imposed − absorbed` is an energy reading, not that complete adjoint join.
The next receipt keeps the producing chart, clock, clamps, damaged-cell partition, cohort, seed
and mechanism fixed across its declared comparison and names each contemporary constitution and
its producing covector. It reports which distinguishing
relations changed after deposition and which persist through cold continuation. A common-class
majority or a total assembled from different cohorts cannot establish acquisition. The
[pair-gain regressions](../research/records/2026-10-05_THE_PAIR_GAIN_IS_THE_JOINED_BANKS_LOG_DETERMINANT.md)
and [reflection repair](../research/records/2026-10-05_REPAIR_BY_REFLECTION_THE_LOCATED_PAIR_RESTRICTS_THE_ERASED_CELLS_FROM_BOTH_SIDES.md)
keep their separate claims. #62 retains formal source/receiver squares; #73 consumes the native
learning relation; #76 consumes its device equivalent; #148 requires the actual useful boundary.

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

[proved-derived; source-checked] **A nonlinear Lock needs the executed domain.** The loaded quartic branch shares its element relation and mixed kick/drift with the generic `ReferenceHolon::advance`. Positive quartic storage and signed energy-accounting closure do not establish a bounded step: `u ↦ u−u³` carries `2 ↦ −6` while its balance closes. `PeriodicDomain` checks the actual finite-map Jacobian, Hessian variation, cyclic positive metrics and centre residuals; `PeriodicLock` reads a separated sheet and an amplitude-square enclosure only from that certificate. Its phase class is the declared material period index, not the source navigator's whole phase-lift class. `MountedParametron` now consumes a declared primitive pump `Cycle` and carries the exact component state and work through successive admitted windings; a single tick may expand while the checked composition contracts. The native component entry is `ResonatorOperands::mount_periodic`. It does not certify the ordinary rounded Word or whole-field Holarchy mount: charted solves, rounding/remainder fibres, generic nonlinear interconnection and full pump/cycle consolidation remain owed. See [the executed-domain derivation](../research/records/2026-10-05_THE_QUARTIC_STEP_NEEDS_AN_EXECUTED_DOMAIN_BEFORE_A_LOCK.md) and [the continuing cycle consumer](../research/records/2026-10-05_THE_LOADED_COMPONENT_CARRIES_ITS_ADMITTED_PUMP_CYCLE.md).

## The objects

Each object comes with its dual. A reading is always a pairing of the two, and orientation exists
only in that pairing.

### 0. Complex

[definition] Oriented cells with boundary `∂`, `∂²=0`: the incidence on which everything is
placed. Owners: `Geometry/ExteriorBoundary`, `Holon/Complex`, `Foundation/Holon.BoundaryHolon`,
`Foundation/AperturedGradedComplex`; Rust `holonics::geometry::complex`.

### 1. Holon and coholon

[definition] A **Holon** `|H⟩` is a motion admitted by a Holon's law `H`
([the Holon as one object](#the-holon-as-one-object)): a continuing current, flux or motion on the
complex, carried through the law's oriented ports. It is not produced by a computation. Its admitted motions — including the
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
covector travels along that adjoint. A helix is circle + carry (`PhaseCarry`: winding cocycle); at a real rate its carry word is the
epoch reading of its clock at another clock's sections (§12, `Aeon/Clock/CarryWord`). A
**fractal navigator** is a family of maps with parameters, restriction maps, composition order,
scale square `r∘T_fine=T_coarse∘r` and first-arrival populations of one full recurrence
(`FractalPacking`, `HolonicRecurrentEcology.FirstArrival`); an ordered source word is its
**address** (`SourceMoment`: identity advance merges permutations, as a restriction word cannot
collapse to a multiset). Recursive description and branch/address information are separate
compression operands. A navigator runs until its receiver face is within tolerance
(`ReceiverRelease.Releasable`, `Standing.Extinct`); then it is released and a new one is founded.
Holonic Compression couples a fractal navigator's resonating modes with terrain
([the line](THE_MACHINE.md#the-line-the-rebuild-serves)). [definition; agent-inferred] For a
self-similar navigator with ratios `r_i` its resonating modes in scale are its complex dimensions, the roots of `Σ_i r_i^ω=1`
(`Foundation/FractalString.selfSimilarZeta_eq`): the real part is a dilation, the imaginary part a
rotation in the log chart (Cantor: `log 2/log 3 + 2πik/log 3`; the golden string: `2^(−ω)+2^(−φω)=1`).
[proved-derived; formal-checked] The zeta's denominator is the transfer determinant of the
navigator's epoch return map in the scale chart, the face `Aeon/Production/Zeta` and
`Transport/NavigatorTraceFaces` own: for `N` equal ratios `r` it is `det(1 − T·[N])` at `T = r^s`
(`equalRatioZeta_eq_transfer`; Cantor's two-hand map `[2]`, `cantor_complex_dimensions_transfer`),
for unequal ratios the weighted `det(1 − [Σ_i r_i^s])` (`selfSimilarZeta_eq_transfer`). For
graph-directed words the transfer determinant times the zeta series is a polynomial, as formal
power series (`transferDet_mul_graphDirected_zeta`); that the complex dimensions lie among the
zeros of `det(1 − r^s M)` is [proved-standard] and owed in Lean (#62).

[established-bounded; source-inspected] The source-neutral continuation contract is a chart of
Navigator and Receiver operations, not a new elementary object. A running continuation receives a
registered face under its current codec; each codec records the face that caused its mounting. A
receiver may return an advance, rest or a reflection request. A reflection snapshots the current
codec and instruction. A returned revision resumes
that same continuation at the same instruction only when the new codec names the reflected codec
as a parent; unchanged resumption keeps the codec and instruction. The environment returned by
the executor remains with the continuation throughout. `Transport/ReflectiveContinuation.lean`
states these transitions and success laws. No Rust chart consumes it: the unused runtime
`navigator::reflection` was retired on September 28 (it is at
[`2d34b819`](https://github.com/brandonrdug/holonics/tree/2d34b819/crates/holonics/src/navigator/reflection.rs)).

<a id="the-swing"></a>
<a id="motion"></a>
#### Motion: the turn, the boost and free fall (the Swing)

[project-postulate] Brandon's most primitive concept is the **Swing**, the one move: a pivot held
by a grip, momentum carried through it, and free fall between grips (July 14: "modulating their
inertia and pivoting"; August 6: the pivot's "invariant 'grip'"; September 28: "the motions are the
turn and the boost, it's about pivoting and free-falling"). The [motion record](../research/records/2026-09-28_THE_SWING_IS_A_MOVE_ABOUT_A_GRIP_A_GRIP_TURNS_A_PUSH_BOOSTS_AND_A_FREE_BODY_FALLS.md) derives what
follows, with its checks and GPT-6 Astra's corrections.

[proved-standard; formal-checked] **Three kinds of motion.** A quadratic motion of one degree of
freedom, `H = ½(αp² + 2βpq + γq²)` with `α = 1/m` the inverse inertia, has the generator
`X = [[β, α], [−γ, −β]]` with `X² = −(det X)·I`:
- `det X > 0`: a **turn**, an oscillator's exchange of storage and flow;
- `det X = 0`: **free fall**, a shear; for `β = γ = 0` a step is `(q, p) ↦ (q + hp/m, p)`, inertia alone;
- `det X < 0`: a **boost**, a squeeze.

Every `M ∈ SL(2)` factors uniquely as a turn, a boost and a shear (Iwasawa, `KAN`), exact in the
extension carrying `r² = a² + c²`; the Lorentz group factors into rotations, boosts and null rotations.

[proved-standard] **Power decides turn or boost.** An effort that does no work turns and one that
does work boosts: for a point mass, `Ė = m|v|² Re(v⁻¹v̇)` and `θ̇ = Im(v̄F)/(m|v|²)`. A stationary
ideal grip turns. A moving grip (power `−λ∂_t f`), a push along the motion, a pump (through the
storage's own motion) and friction boost. **Free fall** is motion under inertia alone, the geodesic
`∇_u u = 0`, with gravity the connection; inertia is the kinetic constitutive relation, not all
storage.

[proved-derived; formal-checked] **A receiver's reading.** Against a receiver's energy metric `G`, a
linear rate splits uniquely as `A = T + B`, with `T` `G`-skew (the turn) and `B` `G`-self-adjoint (the
boost), and `Ė = xᵀGBx + ½xᵀĠx + xᵀGf` for `ẋ = Ax + f`. Recharting moves neither part; a different
receiver's metric can. The spectrum, each mode's `λ = β + iθ`, is the conserved face, and the split
agrees with it when `A` is `G`-normal. In the Holon's quadratic chart `ẋ = (J − R)Qx + Bu` the turn is
`JQ` and the boost `−RQ`. With the interval as metric every Lorentz move is skew: the rotation/boost
split needs an observer. A complex channel `ż = (β + iθ)z` carries its turn as its frequency and its
boost as its growth.

[proved-standard; formal-checked] **A move has the pivot it holds.** `x ↦ Mx + b` pivots about
`O = (I − M)⁻¹b`; when `M` fixes directions semisimply it moves about the invariant set
`O + ker(I − M)` with free fall `b_∥` along it (a screw: a helix is a turn about an axis with free
fall along it); a shear has no such split. What a move holds invariant is its **grip**: a turn holds a
distance, a positive scalar dilation a bearing, a Möbius move every cross ratio. For
`m(z) = (az + b)/(cz + d)` with pivots `z₁, z₂` and `μ_i = cz_i + d`,

```text
(m(z) − z₁)(z − z₂)·μ₁ = μ₂·(z − z₁)(m(z) − z₂)      K = μ₂/μ₁ = m′(z₁),     K + K⁻¹ + 2 = tr²/det
```

so the multiplier is a cross ratio of the two pivots, the body and its image (Brandon's cross-ratio
swing), and `tr²/det` classifies the move projectively as `navigator::trace::SiteKind` does: a turn
(Rotation), a boost (Boost), free fall (Null), a half-turn with a boost (Reflection). A physical grip
is a constraint with its reaction, supplied by the constitution; a fixed point alone is kinematic.

[proved-derived; formal-checked] **Along a path.** The velocity `v` is the carrier. Where it does not
vanish, `ẇ = v⁻¹v̇` is the boost rate plus `i` times the turn rate, and
`x^(n+1) = v·Y_n` with `Y_0 = 1`, `Y_(n+1) = Ẏ_n + ẇ·Y_n` (the complete Bell polynomials): every higher
derivative of motion is `v` times a polynomial in the jets of `ẇ`. `v⁻¹v̇` is the ratio's `R⁻¹dR`
(§9) evaluated on a clock.

[definition; agent-inferred] **The Swing and its older charts.** The Swing is the move about a grip,
as a passage: grip, swing, release (the commit), free fall, and catch (reception at a new contact).
Its earlier charts are particular moves, each kept with its owner:
- **the half-turn** `S_a x = 2a − x` (`Geometry/AffineSwing`), multiplier `−1`: a proper continuous
  motion in the plane and in any complex chart, and parity in an odd real dimension. Words of
  half-turns have linear part `±I`, so they compose only translations and half-turns, and any map is
  pointwise a half-turn about `(x + T(x))/2`: a half-turn explains a motion only with its anchor's law;
- **harmonic conjugation** (`Geometry/{Swing,SwingBridges}`): a projective involution (trace zero),
  Möbius-conjugate to a half-turn;
- **the pantograph** `Q − O = s(P − O)` (`Geometry/HolonicPantographicSwingJets`): the move about `O`
  with a scalar multiplier;
- **the clocked pantograph** (`HolonicClockedPantographicSwing`): the turn's lift, each tick an
  oriented section crossing, the windings its quotient and the phase its remainder, with the fibre
  of inner moves; placement on apparatus is a separate receiver
  (`HolonicClockedPantographicSwingApparatus`);
- **junction scattering** `R_D = 2P_D − I`: a lossless junction splits one current into two shares
  and recombines them, conserving the joint norm and doing no work, with determinant `(−1)^codim`
  ([receiver atlas](RECEIVER_HOLARCHY.md#the-reflection-algebra-shared-by-seam-and-swing)). A fold is
  that map applied to one side of a crease (§6).

Rebasing the observation, receiver and navigators through a half-turn preserves every possible future
face, and in a normed chart it carries a declared tolerance exactly (`Geometry/SwingPotential`); a
coordinate rebase is not a physical intervention.

[project-postulate] **Motion is the navigator's elementary act.** A navigator advances in free fall
along its clock, and turns and boosts at the grips it meets; its word, clock and carry are how its
moves compose. Navigating is choosing the moves, and landmarks are where their paths converge.

[proved-standard; formal-checked] The completed zeta is invariant under the half-turn about ½,
`ξ(S_½ s)=ξ(s)` (`Zeta/Seam.completedRiemannZeta_swing_half`, through the derived join
`combReflection_eq_swing`); the critical line is the fixed set of `s ↦ 1 − s̄`, the half-turn after
the conjugation mirror, not of the half-turn alone, which fixes only ½. Integration by reflection over
the fractal packing uses the same half-turn on `[0,1]`: the map conjugating the two Cantor maps is
`S_½` (`Foundation/FractalPacking.reflect_eq_swing`). [proved-standard; interpretation] Mellin's ½ (a
half-density weight) and spin's ½ (a half-angle) are different halves; an intertwiner, not a shared
numeral, would join them ([record](../research/records/2026-09-25_THE_MUSIC_IS_IN_THE_HOLES_HEARING_MULTIPLIES_BY_ZETA_AND_A_QUASICRYSTAL_IS_A_HELIX_THAT_NEVER_LOCKS.md#4-the-half-and-the-pivot-three-different-halves)).

[proved-standard; formal-checked where named] **The lifts** ([record §5](../research/records/2026-09-28_THE_SWING_IS_A_MOVE_ABOUT_A_GRIP_A_GRIP_TURNS_A_PUSH_BOOSTS_AND_A_FREE_BODY_FALLS.md#5-the-lifts)):
- **Lattices and crystals.** A turn holding a lattice has integer trace, so its order is `1, 2, 3, 4`
  or `6` (Niven); `SL(2, ℤ)` is the lattice's turns, shears (its free fall) and boosts; the golden
  boost `[[2, 1], [1, 1]]` holds `x² − xy − y²`, and its expanding direction cuts the Fibonacci
  quasicrystal. A crystal's turn closes; a quasicrystal's never does.
- **Hypergeometry.** Monodromy is a group of moves: the `(2, 3, ∞)` triangle group is the half-turn,
  the third-turn and the cusp's shear; the egg's Legendre period has the shears of `Γ(2)`.
- **Induction and cross-entropy.** `E` boosts a charge and `B` turns it; vacuum Maxwell is
  `i∂_t F = ∇ × F` for `F = E + iB`, a turn, and a current's `J·E` is the push. For a linear field the
  turn and boost are Helmholtz–Hodge (coexact and exact), and vortex stretching is strain boosting
  vorticity. Relaxation lowers the divergence to the stationary face (a boost), and the arrow that
  survives at stationarity lives on cycles (`heat.chain-no-arrow`, `heat.ring-current-affinity`).
- **Einstein.** Free fall is the geodesic; two boosts leave a turn (`Physics/Spacetime/Wigner`); tidal
  curvature and frame dragging are the Weyl tensor's strain and rotation parts.
- **The quantum.** Unitary evolution is a turn and imaginary time a boost
  (`quantum.evolution-kinds`); the Wick rotation exchanges them; energy is a turn rate, `E = ħω`.
- **Transcendentals are constraints.** A move is carried by its algebraic data; `e^(2πi) = 1` is the
  condition that a turn closes, `e^(iπ) = −1` the half-turn, and `e` the boost that is its own rate.

[proved-derived; formal-checked] **Conservation of faces.** Carrying material to another phase
conjugates it, `M ↦ S⁻ᵈMSᵈ`, so every class function of the material is a face conserved along the
winding: its determinant, its trace sequence `tr(Mᵏ)` and its transfer determinant `det(1−T·M)`
(`Transport/NavigatorTraceFaces`: `carried_material_conserves_{determinant,trace_sequence,transfer_determinant}`;
[winding guide](WINDING_CARRY_AND_PLACEMENT.md) §3). For independent sites the transfer
determinants multiply, `det(1−T·⊕M_g)=∏(1−a_gT+q_gT²)`, and the trace sequences add. **Energy
conservation is one conservation of faces:** storage and flow exchange along a mode while the mode
energy is conserved (`Objects/Parametron.modeEnergy_conserved`), and the Cayley step of a skew
transport preserves its norm (`Holon/Cayley.cayley_isometry`; Rust chart `holonics::navigator`). Trace faces are invariants, not a complete
action certificate: `I₂` and `[[1,1],[0,1]]` share them, and the receiver `(1,0)` after one step
from `(0,1)` separates them. A move's multiplier is such a face: every frame agrees on it, though the
identity (rest) and a shear (free fall) share it.

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

[definition; re-derived from its constitution, September 29
([record](../research/records/2026-09-29_THE_PARAMETRON_RE_DERIVED_THE_PUMP_READS_RELATIVE_PHASE_AND_THE_FLOQUET_CERTIFICATE_DECIDES_THE_LOCK.md));
Brandon: "please do not restrict us to clearly partially implemented constructs"] The **complex
parametron** is the ring: oriented incidence `B` with its storage, a pump that modulates its
constitution periodically, the Floquet monodromy of one pump period, the bifurcation where that
monodromy starts to grow, two half-turn sheets past it, and its lock read as an Ising site. Its
phase carrier is `e^{iθ}`; the half-turn `e^{iπ} = −1` exchanges the sheets, to which the pump is
blind; on locked sheets the coupling `−w cos(θ_i − θ_j)` is exactly the Ising pairing `−w σ_iσ_j`.
Storage and flow exchange at `ω = 1/√(LC)`, and a section crossing of the ring is a clock tick. The
objects, each with its equation:

```text
storage        C = BᵀW_C B,  K = BᵀW_K B on node amplitudes z = x + iy;  E_Q = ½⟨w, Cw⟩ + ½⟨u, Ku⟩;  Kv = ω²Cv
pump           K_t = K + ⊕ −2p R_(ψ_t),  R_ψ = [[cos ψ, sin ψ], [sin ψ, −cos ψ]], the reflection across ψ/2
               ½ zᵀ(−2pR_ψ)z = −p Re(z² e^(−iψ)): the doubled phase, blind to the half-turn
schedule       one carrier e^(iψ_t) a tick of the period T: declared a²s^t, or modulated by the crossing cells, (a²s^t)·c_t
tick           x′ = T_t x on x = (u, w),  T_t = [[I − h²X_tK_t, 2hX_tC], [−2hX_tK_t, 4X_tC − I]],  X_t the executed solve
monodromy      M_T = T_(T−1) ⋯ T_0, the holonomy of the pump's cycle
certificate    G ≻ 0 and M_TᵀGM_T ⪯ ρ²G  ⇒  E_G(M_T^m x) ≤ ρ^(2m) E_G(x);  decided by In(G) and In(ρ²G − M_TᵀGM_T)
placement      #{|μ| > r}, #{|μ| = r} = the half-plane counts of (1 − s)^n χ(r(1 + s)/(1 − s))
consumer       E_Q(x_(τ+s)) ≤ (γ_hi/γ_lo) ρ^(2m) (max_t σ_t²)^(s − Tm) E_Q(x_τ),  γ_lo Q ⪯ G ⪯ γ_hi Q,  T_tᵀGT_t ⪯ σ_t²G
axes           K_ψ a = (k − 2p) a,  K_ψ(ia) = (k + 2p)(ia),  a = e^(iψ/2);  standing bifurcation k − 2p = 0
amplification  in-phase [[0, 1], [κ², 0]]: (1, κ) grows at +κ, (1, −κ) squeezes at −κ, read by κu_∥ + w_∥;  the quadrature turns
sheet          σ = sign(κu_∥ + w_∥) of the seed: sign cos(φ_in − ψ/2) for a seed on the displacement
relative       R_ψR_χ = the turn by ψ − χ,  tr = 2Re(e^(iψ)e^(−iχ));  Re(z_a z̄_b) even under the half-turn, every linear reading odd
lock           Π(a) = 1 + a/K,  θ = aΠ′/Π = a/(a + K),  a∂_aθ = θ(1 − θ) ≤ ¼;  N locks: Π = ∏_i(1 + a/K_i), pivots a = −K_i
capacity       S = Π(a₂)/Π(a₁) = ∏_i (a₂ + K_i)/(a₁ + K_i), strictly between 1 and (a₂/a₁)^N
carry          (2πi)⁻¹ ∮_(|a| = r) Π′/Π da = #{i : K_i < r}
coupled        two locks: Π = a² + 2ya + 1;  y = 1: (1 + a)²;  |y| < 1: both zeros on |a| = 1, off the real axis
hearing        c_v = ⟨s, Mv⟩⟨r, v⟩ = 0 exactly when one coupling vanishes; a constitutive change can reopen it
```

- **The pump is a periodic modulation of the constitution.** [definition] An element relation with
  its power (the Holon's `𝓔`): its work at a switch, `½⟨u, (K_t − K_(t−1))u⟩`, is a term of the
  executed balance (`HNN/Ring.ring_tick_executed_energy_balance`). It retains nothing, so it is not
  deposition. Its schedule is declared, or supplied at its port by the cells crossing the ring's
  section, one tick a crossing.
- **The Floquet monodromy and its certificate.** [proved-derived; formal-checked, implemented-exact]
  The executed tick is linear in the state, and one period composes the monodromy. A metric `G`,
  attained by any exterior means, is certified inside by Sylvester inertia, and the energy then grows
  by at most `ρ²` a period (`HNN/Floquet.{floquet_energy_step, floquet_energy_iterate,
  floquet_passive}`). The multipliers are placed exactly about any circle through the Cayley map
  and the half-plane count, so a growth is enclosed with exact endpoints. **Its consumer** is the
  constitution's certified step: through a ring not certified passive (a pump, or a signed
  stiffness) every gain but the readout's reads the medium's span factor
  `F(s) = ∏_r max_(s′ ≤ s) reach_r(s′)` term by term (`floquet_span_reach`,
  `Holon/Deposition.{station_tick_gain, entry_span_gain, pumped_span_factor}`; Rust
  `hnn::ring::FloquetBound::reach`, `hnn::constitution`, "The pumped medium's reach"), the ring's
  own gain families held. A step through it is refused (`UncertifiedGain`) only where its decided
  certificate is. The driven ring's loop within a span (the port's feedback) is owed in #62.
- **The bifurcation.** [proved-derived; formal-checked] A standing pump's tick has the multiplier one
  exactly where the pumped stiffness is singular (`standing_fixed_point_iff`): on the in-phase axis,
  at `k − 2p = 0`. Below it the storage form is itself the certificate at `ρ = 1`
  (`storage_form_certifies_passive`, from `ring_tick_port_balance`). The three kinds of the Swing
  are its three sides: below, a damped turn; at it, a shear (the edge); past it, a boost. A rotating
  pump resonates parametrically: [measured] the quarter-turn pump grows at strengths the standing
  pump leaves passive, its growing multiplier negative (a half-turn with a boost, the subharmonic
  lock); the half-turn pump's perpendicular axes cancel, and it stays passive past the standing
  bifurcation. Its tongue boundaries are owed (#62).
- **The two sheets and phase-sensitive amplification.** [proved-derived; formal-checked in the
  continuous chart, implemented-exact in the executed law] Past the bifurcation the in-phase axis
  boosts: its phase plane holds the growing quadrature `(1, κ)` and the squeezed `(1, −κ)`, and the
  node plane's quadrature turns (`pumped_inphase_axis`, `inphase_growing`, `inphase_squeezed`,
  `quadrature_turns`; the Cayley tick keeps each axis with the multiplier `(2 + hλ)/(2 − hλ)`,
  `cayley_tick_eigen`). The envelope chart's "amplify the in-phase component, squeeze the
  quadrature" is this boost read in the frame that rotates with the ring. The sheets are the two
  rays `±v₊` of the growing Floquet mode; the pump cannot choose between them, and the seed's growing
  coordinate does (`inphase_growing_coordinate`; Rust `hnn::ring::lock`).
- **The locked-sheet face and the relative phase.** [proved-derived; formal-checked; measured] The
  perceptron, the threshold of a local field, is the locked sheet's linear face: linear, then
  threshold, and odd under the half-turn of its input. A relative phase `Re(z_a z̄_b)` is even under
  the half-turn, so no linear reading followed by a threshold reads it
  (`no_linear_threshold_reads_relative_phase`). The law's quadratic place is the pump. When the
  crossing cells modulate the pump's carriers, the monodromy composes their reflections, and at
  second order in the pump carries the turn by their relative phase (`reflection_mul_reflection`,
  `reflection_pair_trace_carriers`): the **square law**. The bifurcation is the **threshold**. A
  **bank of receiving parametrons at declared pump phases** (member `j`: axis `1`, step `i^j`, its
  carriers `(c_e, i^j c_l)`) locks at the one member whose declared phase aligns the two cells, and
  every other member is certified silent: the lock pattern is the relative phase's class, decided by
  the Floquet certificate (Rust `hnn::ring::{ReceivingBank, BankReading}`; the record's counts).
  Retired: the reading of the linear lock as a square-law reading of relative phase.
- **The bank reads a superposed passage.** [proved-derived; formal-checked in the kicked chart,
  implemented-exact; September 29,
  [record](../research/records/2026-09-29_THE_BANK_READS_A_SUPERPOSED_PASSAGE_THE_LOCKS_CONTINUE_A_SPECTRAL_LINE_AND_THE_ORDER_TWO_TERRAIN_STAYS_AT_THE_MARGINAL.md)]
  The receiving ring holds the passage superposed through the source port; as it turns, each node
  crosses the section and pumps every member at its placed amplitude, and the passage's monodromy is
  the ordered product over one turn. Two crossings separated by the ring's transport compose to the
  turn by their relative phase less the transport, `R_u Rot_v R_w = Rot(u v̄ w̄)`; one crossing more
  pairs with every earlier one; at a whole turn the second order's trace is the passage's power
  spectrum, `2 Re Σ_t w_t conj(Σ_(s<t) w_s) = |Σ w|² − Σ |w|²` (Lean `HNN/FloquetPassage`). The growth
  is enclosed exactly on either side of one by the Schur–Cohn test (Rust
  `hnn::ring::{ReceivingBank::read_turn, Growth}`). [measured] On a spectral line the lock pattern
  names the class (the half-turn partner certified silent), and with a crossing open the candidate
  completing the line reads the strictly largest joint growth: the lock's flip continues a line
  (`hnn::prediction::generate_by_bank`). A declared bank reads the passage's own lines; which relative
  phase at which lag a continuation keeps is a key the bank does not yet learn: its reading enters no
  comparison.
- **The lock is an Ising site.** [definition; proved-derived; formal-checked] A two-sheet lock under
  the bias `a` has the exchange polynomial `Π = 1 + a/K` (its partition function read at the resting
  sheet) and the logistic face `θ = a/(a + K)`, whose susceptibility is at most `¼`
  (`Objects/ParametronLock.{lockFace_logistic, lock_susceptibility_le_quarter}`); the threshold is its
  face at zero temperature. [interpretation] Reading a pumped ring's basins under noise as this face at
  a declared temperature is not proved.
- **Capacity is the lock count, not the coordinate count.** [proved-derived; formal-checked] Each
  factor of the selectivity is the cross ratio of the two biases about a pivot and `∞`, so `N` locks
  separate two biases by at most `(a₂/a₁)^N` (`selectivity_lock_count_bound`). [proved-standard] A
  bank of `N` members, each locking on an arc of relative phase, cuts the circle into at most `2N`
  classes.
- **The winding is the carry.** [proved-standard; formal-checked] On `|a| = r` the argument of `Π`
  winds once for each pivot inside (`winding_is_carry`): as the bias's magnitude passes a pivot, one
  more lock has flipped.
- **Coupled locks (Lee–Yang).** [proved-derived; formal-checked] A ferromagnetic coupling moves the
  pair's double pivot off the negative real axis onto the unit circle
  (`coupled_zeros_leave_the_axis`): the coupled-sheet parametron.
- **Modal hearing is dormancy.** [proved-derived; formal-checked] A mode is silent exactly when its
  source or its receiver coupling vanishes, and a constitutive change can reopen it
  (`modal_silent_iff`, `dormant_mode_reopens`). A bank's silent members are dormant: the
  modulation that aligns a member's pump reopens it, and it locks.

Owners: Lean `Objects/{Parametron,ParametronLock}`, `HNN/{Ring,Floquet,FloquetPassage}`,
`Physics/{PhaseCarrier,CoupledIncidence,HolonicMeasuredParametron}` and the torus realizations; Rust
`holonics::holon::parametron`, `holonics::hnn::ring` (the device refinement at `13f8c734`,
[`complex_parametron.rs`](https://github.com/brandonrdug/holonics/blob/13f8c734/crates/holonics-cuda/src/cuda_refine/complex_parametron.rs),
is a port source). `Objects/Parametron` joins the LC and generalized-mode exchange, the ring's
crossings as `RationalClockPassage` ticks (`d ≥ 2`), and the threshold unit as the
energy-minimizing locked sheet. [open] The rotating pump's tongue boundaries and its subharmonic
multiplier below `−1`; a saturation (the law is linear, so a locked amplitude grows until a
certified step or a declared saturation bounds it); the continuous crossing of `A cos(ωt + φ)` as
the micro-step ring; the executed law's second order through a passage (the kicked chart's is
proved); the covector of the lock's decision reaching the members' pumps (reaching the placement's
`E` it was `hnn::executed`'s, September 30, retired with the descent move October 5 at
`9078f103`; the bank's face, which read the decision at a declared temperature, is retired, batch
H).

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
never a record of the fluxes that shaped it.

[proved-derived; GPT-6 Astra, September 27, [record](../research/records/2026-09-27_THE_LEARNER_MUST_MOVE_A_CHASE_TERRAIN_DATA_AS_PARTICLES_WITH_FLUX_AND_RELEASE_AS_A_THRESHOLD_COMMIT.md#14-gpt-6-astras-review)]
**For an acting receiver, the admitted future includes its actions.** A passive quotient can merge
two constitutions that emit alike under every action taken so far and differ under a probe. Where
actions are admitted, retention is the **action-sufficient** quotient: `h ∼ h'` exactly when, for
every admitted action word `a₁…a_m` and admitted receiver, the future faces under `do(a₁…a_m)` agree.
In a linear chart this is `ker E ⊆ ker ρ` and `T_a ker E ⊆ ker E` for every admitted `a`: the
decoding and continuation squares quantified over controls. Predictive-state representations
(Littman, Sutton and Singh, 2001) are the established construction. Lean owed in #62.

<a id="the-retention-contract"></a>
<a id="collapse-relative-to-the-admitted-future"></a>
[definition; agent-inferred, U2 of [the rebuild](plans/THE_REBUILD.md#u2-one-retention-contract-and-f0s-memory), September 28]
**The retention contract.** Every collapse the machine takes is an instance of one law,
`Standing.standingLaw_exists_iff_future_factors`: a retention is lawful exactly when every admitted
future face, under every admitted action word and deposit, factors through it. No dense global
representation is forced on a collapse. Each certifies the factorization through its own carrier
and keeps its own recoverability condition. This section owns the contract; the owners cite it.

A retention quotient is taken at an aeon boundary against the receivers and actions admitted
there (GPT-6 Astra's review of September 28). A later aeon may admit more: a receiver grows its
receivers ("Keys, locks and navigation" below). Neither "the admitted future only shrinks" nor "it
may always grow" is a law. What a collapse survives depends on its **recoverability hypothesis**: a
collapse can be reopened for a wider admitted future exactly when what it retained (seeds, shares,
residuals, declarations) suffices to rebuild every member the wider future separates. That
reopening material counts toward memory. The collapses built differ here:

| Collapse | Carrier and certificate | Its standing law | Recoverability |
|---|---|---|---|
| The HNN's structural collapse (`hnn::retention::collapse`) | the time-indexed causal diamond on the field's sparsity: a locus outside every admitted receiver's diamond is released whole, becoming the zero map with its statistics dropped | `HNN/Retention.fieldStanding` (generators ingest, locate keys, refine and deposit), on the abstract block operator; the concrete-tick bridge is owed in #62 | none: no later deposit resurrects a released locus (`release_structural`); the collapse suffices for every later family contained in its own (`admitted_nonincreasing`), a family that adds a receiver can read a released locus (`admitted_growth_reads_released`), so the aeon's close refuses a growing family (`contained`) and every pending ratio whose receiver still hears a released locus (`separator`, Hearing's `heard_not_listened_refutes_standing` on the diamond) |
| Species collapse (`receiver::population::Population::{collapse, split}`) | each key's exact signature over the admitted future (its emitted word, or its rotor's transition table) | `Context/Evolution.species_collapse_standing`, over every cell word, so over every word a release commits | the receipt keeps every member's seed and share; a cell past the certified future is refused; `split` restores the members exactly (`species_split`), and a wider future collapses again |
| The receiving tree's storage (`compression::landmark::context`) | a chain of nodes with one reached child each, stored where paths part: its nodes route one set of arrivals until an arrival parts them | `Context/Standing.address_standing` with `Context/Compaction.compacted_is_the_full_tree` and `Context/Tree.release_rule` | a parting arrival splits the chain from its register, its chart and the declared rungs (`Compaction.chain_split`) |

A merge of receiving-tree contexts beyond these is a collapse of the same kind. Equal present
faces, or equal code on validation cells, do not make it lawful
(`Context/Merge.equal_present_faces_do_not_merge`): the decoding and continuation squares must hold
under every admitted action and every admitted deposit. The tree's owner derives, for its declared
receiver, exactly which merges and releases qualify ("Which merges and releases are
future-sufficient"): beyond the chains, only the readings kept beside the state and the contexts no
continuing address reaches. A declared coarser receiver (a depth, a founding rule, a merge of
contexts) is a separate law priced by its code-length pair (`Context/Merge.coarsening_within_margin_iff`),
never retention.

<a id="affirming-extinction"></a>
[proved-derived; Lean owed in #62] **Affirming extinction.** `Standing.Extinct` quantifies over every
navigator word, so an enumeration to a horizon can only refute it. It is affirmed by a **contraction
certificate** on a linear navigator family: a declared chart `C` of coordinates that every navigator
keeps (`A[i][j] = 0` for `i ∈ C`, `j ∉ C`), each of whose rows sums to at most `λ ≤ 1` in absolute
value, with every reading supported on `C` at gain `γ = max_i Σ_(j∈C) |R[i][j]|`. Transport is
linear, so `|ρ(T_w x) − ρ(T_w z)|_∞ ≤ γ λ^|w| ‖(x − z)_C‖_∞ ≤ γ ‖(x − z)_C‖_∞` for every word, and
the difference is extinct at tolerance `ε` whenever `γ ‖(x − z)_C‖_∞ ≤ ε`. Its Rust realization
(`receiver::standing::extinction`, at commit `1bdacc8f`) was retired at U2 with no consumer.

One law covers both of Brandon's physical pictures:

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
    split of the deposition (`HNN/LatticeDeposit`) uses nearest rounding but constructs no such word.
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
log            ℓ = log R, winding as the branch            Turn, PhaseCarry, Zeta/LocalArgumentPrinciple
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

[definition] **Release is one decision law** (`receiver::release`, Lean `Foundation/ReceiverRelease`).
Every emission is a `ReleaseReturn` of it: a **threshold commit** (a width over a compatible fibre
inside a declared tolerance), a **certified draw** (a declared key's inverse-CDF class, emitted only
when every compatible face selects it), a **probe** (an offered observation) or a **typed refusal**
(the fibre held, a key left unresolved with its draw mass, or no admitted continuation). A draw and a
commit are different acts, joined by the one law: the draw is the commit at tolerance zero on the
key's class reading
(`Compression/Landmark/Context/Population.{certified_draw_is_released_at_zero_tolerance, plural_draw_is_held}`).

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

[definition; formal-checked where named] **Hearing, listening and nullity** ([record](../research/records/2026-09-25_THE_MUSIC_IS_IN_THE_HOLES_HEARING_MULTIPLIES_BY_ZETA_AND_A_QUASICRYSTAL_IS_A_HELIX_THAT_NEVER_LOCKS.md#7-hearing-listening-nullity-and-response-typed)).
A difference is **heard** by a receiver when its current face separates it (`F_now δ≠0`). It is
**null** to that receiver at its grain when the face cannot separate it; nullity is always relative
to a declared receiver, grain and admitted future, and `ker F_fut ⊆ ker F_now` when the current
receiver is among the admitted ones
(`Holarchy/Hearing.futureNull_le_ker_present`, over
`Foundation/CausalRelevance.futureCollapsed_le_presentCollapsed`). It is **listened to** when a
reached-action map `A_R` carries it into a locus's retained state (constitution entries, carried
remainders, clock) (`Holarchy/Hearing`: `Heard`, `Null`, `Listened`, `HearingLaw`);
heard-but-not-listened is `ker A_R ∖ ker F_now`. The HNN's deposit is the instance: an update below
half the locus's fine grain is reported exactly and released whole, leaving that entry of the
constitution unchanged (`HNN/LatticeDeposit.carry_entry_below_grain`,
`below_grain_heard_counted_not_deposited`), while the locus's clock
still counts the nonzero deposit, so the difference is counted, not deposited; the grain refines as
the locus ages (`listening_grain_refines`). What changes no retained state cannot change a response:
equal standing forces every admitted future face to agree
(`Foundation/Standing.StandingLaw.futureAgreement_of_retain_eq`; `Holarchy/Hearing.futureNull_of_retain_eq`),
and a reached action is a lawful standing exactly when every unlistened difference is future-null
(`act_is_standing_iff`). The coholons a face pulls back are exactly those annihilating its nullity
(`mem_pulledBack_iff`, from Mathlib's `LinearMap.range_dualMap_eq_dualAnnihilator_ker`). The zero-storage receiver hears at zero power and stores no
energy (`zero_storage_receiver_hears_without_storing`).
[proved-standard; formal-checked] Hearing a string of holes multiplies its face by ζ,
`ζ_ν=ζ·ζ_ℒ`, and the full count is inverted exactly by Möbius (`Foundation/FractalString`).
[proved-standard] The zeros of ζ are the dimensions at which the asymptotic receiver cannot hear a
geometric oscillation (Lapidus–Maier 1995).

[definition] **Measurement conventions**
([history](https://github.com/brandonrdug/holonics/blob/13f8c734/docs/DEVELOPMENT.md#performance-and-information-measurements)). A timing, rate or
energy reading is an exterior face of a receipt: it is recorded and compared, and it is never a
coefficient of a law. Exact resource vectors (`ExactWork`, ordered exactly by `order_against`) and a device's
capacity census are owner operands at their stated scope. This is not a ban on measuring or
optimizing performance.
- A **face delivery** completes a requested receiver output (a rendered image, a decoded text
  section, a solved family). An **owner update** completes one admitted successor at its
  continuing owner. They are the scoped analogues of frames and ticks. A device launch, a symbol,
  a source observation and a successor are different counts, and a forecast can deliver a face
  without advancing its body.
- Rates are counts over an interval `dt > 0` of a named clock, `N_face/dt` and `N_update/dt`. Over
  disjoint successive intervals they aggregate as `ΣN/Σdt`, never as a mean of reciprocal latencies.
  Under `t'=at+b`, `a>0`, a rate becomes `r/a`; reversing a clock flips an oriented quotient and
  reverses no dissipation.
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
- [proved-derived; formal-checked] **The carry word is the epoch reading of two clocks**
  (`Aeon/Clock/CarryWord`, [record](../research/records/2026-09-25_THE_MUSIC_IS_IN_THE_HOLES_HEARING_MULTIPLIES_BY_ZETA_AND_A_QUASICRYSTAL_IS_A_HELIX_THAT_NEVER_LOCKS.md#5-quasicrystals-a-helix-that-never-locks)). A clock of
  rate `α` read at the unit clock's sections carries `s_n=⌊(n+1)α+ρ⌋−⌊nα+ρ⌋ = windings α +
  carry(nα+ρ, α)`, and its epochs count its windings (`epochOf_carrySection`). The word recurs
  exactly when the joint reading closes, `IsCycle(jointReading α T)` (a crystal, the lock, with
  period `q` at `p/q`); at an irrational rate the joint clock has no cycle and the word never
  recurs (`never_locks_iff_irrational`): a one-dimensional quasicrystal. Its faces are the
  cut-and-project tube and window (`mem_tube_iff`, `physicalSite_succ_sub`), balance, the mediant
  cost of a lock, and at the golden rate the Fibonacci approximants against the golden clock
  residue. Rust `holonics::aeon::TwoClocks` owns the joint reading and its cycles; the word itself
  has no runtime consumer yet.
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

[project-postulate] **Inference targets the generator, not the key** (Brandon, September 27: "we're
talking about intelligence"). Every product was made by a generator of finite description drawn
from finitely many families with characteristic groups. That holds for a cipher's machine and its
operator's habits, a language's grammar and its speakers, a password and the person who chose it.
Intelligence does not enumerate keys:
- **It searches generator families by constraint.** Each face the product shows is a receiver: a
  guessed fragment (the Bombe's crib, drawn from the operators' habits), a structural property (the
  reflector: no letter enciphers to itself), a side channel, the author's patterns. Loop closure
  over a menu of such faces kills whole families at once.
- **It grows its receivers.** Every new face shrinks the kernel: the differences no admitted receiver
  distinguishes. An interior is recovered up to its species relative to the receivers admitted. No
  interior is sealed in principle; one whose faces have not been received is only not yet read.
  An event horizon is read the same way, through the interior's exterior faces.
- **It founds from its residual** ([proved-derived; formal-checked], the
  [learner record's §14.1](../research/records/2026-09-27_THE_LEARNER_MUST_MOVE_A_CHASE_TERRAIN_DATA_AS_PARTICLES_WITH_FLUX_AND_RELEASE_AS_A_THRESHOLD_COMMIT.md#141-birth);
  Lean `Context/Birth`, Rust `receiver::population::birth`). With the admitted transports `T_a` of a
  finite chart known, a reached covector `λ_r` that the held forms do not contain (the comparison
  pulled back through the coupling's adjoint) is closed under the adjoints,
  `V_(n+1) = V_n + Σ_a T_a* V_n`. The closure stops within `d − dim V₀` strict steps, its stable rung
  is the least invariant space containing the opening, and a basis `φ_i` of it gives
  `E T_a = U_a E` with `E x = (φ_i(x))_i`: the chart of the family born from the reserve. It
  constructs an observable transport representation. It infers no unknown transport: a residual
  excludes families and does not specify the replacement.
- **It forgets no failure.** Every contradiction is a death with a receipt, and the seeds of the
  eliminated families stay in the declaration. Across aeons the population's prior over families
  learns from its own deaths and selections. This is the evolved ability: a family that keeps
  winning is founded sooner, and one that keeps dying later. It is a retention of selection counts
  over families, never a tape of attempts (built: `receiver::population::Selections`, the Dirichlet
  face of each identity's selections at a pseudo-count its deaths thin, Lean `Context/Evolution`).
- **It encodes by the same law.** Communication between intelligences is a shared generator whose
  faces only a receiver of the right standing decodes: keys that move with their holders, not
  static ones.

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

### The egg: a generator read as a whole

[definition; agent-inferred] Brandon's **egg** is a composition of the objects, not a new object. It
is a navigator with its initial configuration, the constitution it runs in, and the receiver
family that reads its faces, read together as one generator of faces.
- **Its genome** is the navigator's initial configuration and its self-delimiting description.
- **Its phenotype** is the faces it emits.
- **A species** is the class of eggs that every admitted future receiver reads alike. It is the
  face map's quotient over generators (Lean `Compression/Core/FaceMap`), the retention quotient
  taken over generators instead of states, and one collapse of [the retention
  contract](#the-retention-contract). Collapsing a population's species relative to the admitted future
  changes no code over it, and the members' seeds let a species split when the future grows
  (`receiver::population::Population::{collapse, split}`, Lean `Context/Evolution.species_collapse_code`).
- **A population** is a receiver's mixture over candidate eggs. It is updated by Bayes, which is the
  discrete replicator with the likelihood as fitness, and a translation in the ratio's additive
  chart. The receiving tree's mixture over candidate standings is its first instance
  (`Compression/Landmark/Context/Standing.mixture_over_leaf_standings`). Its owner is
  `receiver::population::Population`. The name `holon::parametron::Population` is a different
  object: a coupled parametron population (sites, weighted edges and drives, whose locked-sheet
  face is the perceptron, §5).
- **Birth** is founding (FOUND, from a cokernel residual), with a declared prior and its description
  cost: a newborn draws its mass from the population's reserved mass, abstained before its birth
  and pays its charge once (`receiver::population::Population::found`).
- **Dormancy** holds a silent layer's key through its aeon: the ring's clock keeps winding, its key
  is filtered only where its layer sounds, and a switch of activity is priced by the fixed share
  (Lean `Context/Dormancy`). Death is reserved for keys contradicted while active.
- **Death** is zero likelihood or a lawful release. A poor positive likelihood only loses weight.
  A death is an exchange, never a deletion: the dead mass passes to the survivors, whose total gain
  it is (`Population.death_is_an_exchange`), attributed to each in proportion to its posterior (a
  declared attribution: Bayes fixes only the total), and the dead family keeps its seed, the keys
  it held, which can be re-founded from the reserved mass (half the reserve at each birth) when their face becomes relevant again.
- **Generation is egg packing.** The requested consequence is packed into the keys, and the native
  transport emits it: `decode(T_native(encode x)) = T(x)`.
- **Keystones and their maintenance** (Brandon, September 27: some functions may need energy spent
  "to maintain the resonance", like "certain stars and black holes … for orbits to stabilize";
  nothing in a configuration is unrelated to the rest). [agent-inferred] Eggs compose at ports, a
  Holarchy of eggs. A **keystone** is a constituent whose presence conditions the others' faces. The
  name is borrowed from the keystone species of an ecosystem and from the stone that holds an arch.
  - Composition is the population's own operation (`receiver::population::Composed`, Lean
    `Context/Composition`): `P_(A⊳B)(x | past) = Σ_a P_A(a | past) P_B(x | past, a)`, a face
    wherever the constituents' are, whose code is the chain rule along the keystone's surviving
    keys, `code(A⊳B) = (log₂ |K_A| − log₂ #S_A) + code(B | A)` (`chain_rule`).
  - A keystone's value is read as the joint code with it against without it, not as its own bits.
    An example is a moiré's ring stepped by a clock's carry: at the ring's unheld port the sheet
    meets the gratings' prior at every tick, and held it is located, decided cheaper
    (`receiver::population::composition_tests`). The first example, the arithmetic terrain's record
    clock, was retired September 29 with the arithmetic eggs as catered machinery (history at
    `1b374d46`; notebook README, "Eggs composed at ports").
  - A dense basin is a landmark with heavy traffic: a region where many families' paths converge,
    found where it is causally attributable.
  - Holding a dormant key is free only when its ring is lossless. A mode held against dissipation
    costs its pump work every tick: the parametron's pump, charged in the word's balance.
  - The population's cost receipt therefore reports maintenance work beside description and code
    (`receiver::population::Work`: exact counts of what each family executes).

<a id="the-receiving-storage"></a>
[interpretation; GPT-6 Astra's review of September 28] **The receiving storage is the population
at the receiving port.** The machine's receiving role holds a population over candidate families.
The landmark tree, the shift navigator's landmarks (`compression::landmark::context`), was one of
them, read as a family until the byte-tree text line retired on September 30. The terrain
navigators' key and survivor families and composed eggs are others. This guide owns the statement;
[THE_MACHINE](THE_MACHINE.md) and [HNN_FORMULA](HNN_FORMULA.md) cite it. What is built, and what is
not:
- **The HNN's receiving face is the population's** (THE_REBUILD U1). Its receiving face reads the
  tree at the receiving locus (`hnn::receiving`), and scores the population at that port
  (`receiver::population::port::PortPopulation`, declared by `hnn::receiving::receiving_population`)
  over the tree's face and the combined tree-plus-wave face at ½/½, cell by cell, including the
  deposits made inside a receiving epoch. The combined face lives in `ℚ(θ)`, so it enters as its
  exact enclosure; zero is exact death (Lean `Population.population_mixture_enclosed`). The
  population carries only the priors and the likelihoods; the tree's one update is the
  constitution's landmark deposit. It replaced the carried-ratio `hnn::receiving::Mixture` (history
  at `19f1eb61`), whose codes lay within its chart's drift of the population's on the standing cut
  (`Population.executed_{face,mixture}_within_population`). Digit-local joins (`JoinTree`,
  `FaceJoins`) and whole-family Bayes are different admitted combinations of the same families: in
  general `∏_h Σ_f π_f L_(f,h) ≠ Σ_f π_f ∏_h L_(f,h)`.
- **The field is a family at its own port, dormant for text.** Its combined face is the receiver's
  population's second family at the HNN's port (U1). F2's adoption gate
  ([THE_REBUILD F2](plans/THE_REBUILD.md#f2-the-field-as-a-family-step-4-73), September 28) read
  it on fresh validation families against the population over the tree alone. There it codes
  strictly shorter, by `10` to `10 + 1/16` bits on 2,052 cells. Its work fails the budgets:
  `107 rem 21` ms a receiving epoch, where the tree's whole passage takes 432 ms. So it is not
  adopted for text, and it is kept and not run there.
- **The missing join, and its maps named** (U1; owed in #62). Neither the tree nor the population
  is yet a Holon joined at power ports. Their counts and posterior weights carry no declared
  flow/effort pair, storage or power balance, and the learned-energy balance
  (`Holon/Deposition.learned_energy_balance`) holds in its quadratic port chart, under its
  hypotheses; it assigns no energy to KT counts or Bayesian weights. What the join needs:
  - *the population*: storage the log-partition `Φ(ℓ) = ln Σ_f π_f e^(ℓ_f)` of the log-likelihoods
    (its code is `−Φ`), flow the per-cell increment `f_f = ln P_f(x_t)`, effort the posterior
    `w = ∇Φ`, and the balance `Φ(ℓ + f) − Φ(ℓ) = ⟨w, f⟩ + D(w ‖ w′)` (the Bregman remainder of
    log-sum-exp, `w′` the Bayes update): the code `−Φ` changes by the supplied `−⟨w, f⟩` less a
    nonnegative dissipation, and death is the boundary `w′_f = 0`;
  - *the tree*: a node's storage its log KT mass `ln B(a + ½, b + ½)/B(½, ½)`, its flow the unit
    count on the opened path, its effort the face's log `ln((a + ½)/(a + b + 1))`, and the balance
    the face-code telescope, lossless at the node; the weighing over pruned trees adds the
    population's remainder at each node;
  - *the joint*: a declared constitutive map from bits to the Holon's port variables (no code
    carries joules until one is stated), a Dirac structure between the receiving ring's port (the
    wave's `R P_R^(τ_R) v_R` in the field's quadratic chart) and the combined family's flow
    `ln q_C(x)`, which the softmax receiver does not give power-neutrally (a power-preserving
    receiver map, or its defect bounded), and a common clock (the receiver's epochs as an
    `aeon::Epochs` reading, built at U5: `hnn::receiving::ReceivingPhases::windows`).

  Until that join is constructed, a statistical receiver obeys its count and posterior update laws
  and its code identities, and this reading stays an interpretation.

The geometry of the population's faces is the receiver's
([RECEIVER_HOLARCHY, "Probability is a receiver geometry"](RECEIVER_HOLARCHY.md#probability-is-a-receiver-geometry)).
Records: [egg packing](../research/records/2026-09-27_EGG_PACKING_THE_MOIRE_OF_TWO_HELICES_IS_A_TORUS_KNOT_AND_THE_TREFOIL_IS_THE_HALF_TURN_WITH_THE_THIRD_TURN.md),
[the genome](../research/records/2026-09-27_THE_EGG_IS_A_GENERATORS_GENOME_SELECTION_IS_BAYES_AND_THE_FACES_OF_INTEGERS_ARE_MOIRES_OF_GRATINGS.md),
[the geometry](../research/records/2026-09-27_PROBABILITY_IS_A_RECEIVER_GEOMETRY_BAYES_IS_THE_RATIOS_TRANSLATION_AND_THE_EGGS_PERIOD_IS_HYPERGEOMETRIC.md).

## The targets

[project-postulate] RH, Hodge, complex Euler/Navier–Stokes and BSD are targets of compression and
landmark discovery ([the line](THE_MACHINE.md#the-line-the-rebuild-serves)), not a
separate category. Their joins to the objects:

[definition] Navier–Stokes: velocity is a coholon, vorticity `du♭`, pressure the exact part,
Kelvin circulation a holonomy pairing, the Lamb term the cross-current. Hodge classes: which harmonic
coholon classes are realized by actual Holon cycles. Spectral placement: `FosterTanks` reads zeros as
LC tanks and `ZeroPairLock` gives lock ⇔ `σ=½` ⇔ positive Foster inductance — a parametron
condition. Whether the relevance theorem yields relative completeness in the spectral chart is open:
it needs a persistent frontier current (see §7).
[proved-standard] Hearing the shape of a fractal string is an RH receiver: for `D∈(0,1)` the inverse
spectral problem `(ISP)_D` holds iff ζ has no zero on `Re s=D`, so RH is equivalent to every such
receiver except dimension ½ hearing the geometry (Lapidus–Maier 1995; Lean owns the finite spectral
identities in `Foundation/FractalString`, the theorem itself is owed in #62).
