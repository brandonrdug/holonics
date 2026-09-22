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

## The objects

Each object comes with its dual. A reading is always a pairing of the two, and orientation exists
only in that pairing.

### 0. Complex

[definition] Oriented cells with boundary `∂`, `∂²=0`: the incidence on which everything is
placed. Owners: `Geometry/ExteriorBoundary`, `Foundation/Holon.BoundaryHolon`,
`GradedCausalComplex`, `simplicial.rs`.

### 1. Holon and coholon

[definition] A **Holon** `|H⟩` is a continuing object on the complex: a current, flux or motion
with oriented ports. It is not produced by a computation. Its admitted motions — including the
implicit generator relations that bind a passage of writing, a gait or a knot — are already
present as potential, whether or not a receiver currently reads them. A **coholon** `⟨Ȟ|` is its
dual: a potential or receiver, with coboundary `d=∂ᵀ`. Their pairing is the face:

```text
face      ⟨Ȟ|H⟩
Stokes    ⟨dȞ, H⟩ = ⟨Ȟ, ∂H⟩                                  ExteriorBoundary.stokes_pairing
drop      ⟨φ, ∂H⟩ = φ(target) − φ(source)                     returnsBoundary ∘ stokes (join owed, #62)
gauge     classes mod d and mod ∂ pair: H_k × Hᵏ → R          CellHolonomy.cell_flux_is_gauge_free, HodgeReceiver
orient    flipping a cell negates both sides; the pairing is unchanged
```

Chain/cochain, vector/covector, ket/bra, current/potential, kernel/cokernel (the two-term case) and
cycle/cocycle/coboundary (the classes) are all this one pairing. A Holon alone is **unoriented
potential**; it becomes oriented relative to a frame when a coholon over a relatively complete
region (object 7) is paired with it. A loop along which the pairing's sign has holonomy is
non-orientable (`JunctionLaw.no_consistent_orientation_on_a_reversing_loop`).

### 2. Constitution

[definition] The **constitution** `Θ` is the declared material law on the complex that relates a
coholon to the motion of a Holon it excites. It does not create the Holon: it states which admitted
motion a given potential drives and at what cost. It has two kinds, which exchange:

```text
storage (electric, capacitive)   C = Bᵀ M_C B        energy ½⟨φ, Cφ⟩       standing
flow    (magnetic, inductive)    K = Bᵀ M_L B        energy ½⟨j, L j⟩      emanation
modes   K v = ω² C v                                                       CoupledIncidence.IsGeneralizedMode
dissipation  D ⪰ 0,  power ⟨Jv, D Jv⟩                                      HelicalPairInteraction
```

A Holon's motion decomposes into exact (potential-driven) ⊕ coexact (induced; Faraday emf is not an
exact drop, `HolonicDiscreteInduction.emf_ne_exactDrop_of_fluxDifference_ne_zero`) ⊕ harmonic
(dormant, silent at node/cell receivers, `CellHolonomy.dormant_mode_is_locally_silent`). Owners:
`HodgeReceiver`, `PositiveCellHodge`, `Physics/CoupledIncidence`, the normal law `W H=B`.

### 3. Generator

[definition] A **generator** `Ĝ` is a transport with an **initial configuration** and its own
clock. It acts on Holons; its adjoint `Ĝ*` acts on coholons, `⟨Ĝ*Ȟ|H⟩=⟨Ȟ|ĜH⟩`, and the learning
covector travels along that adjoint. A helix is circle + carry (`PhaseCarry`: winding cocycle). A
**fractal generator** is a family of maps with parameters, restriction maps, composition order,
scale square `r∘T_fine=T_coarse∘r` and first-arrival populations of one full recurrence
(`FractalPacking`, `HolonicRecurrentEcology.FirstArrival`); an ordered source word is its
**address** (`SourceMoment`: identity advance merges permutations, as a restriction word cannot
collapse to a multiset). Recursive description and branch/address information are separate
compression operands. A generator runs until its receiver face is within tolerance
(`ReceiverRelease.Releasable`, `Standing.Extinct`); then it is released and a new one is founded.

### 4. Pair contact

[definition] The **helical pair contact** joins two generators with configurations:
`Δ=x_a(s)−x_b(t)`, `Q=⟨Δ|Δ⟩`, slip `J=[v_a|−v_b]`, `DQ=2J*Δ`, contact material `M=Σw J*DJ`. It is
the constitution restricted to relative motion: it slips, dissipates and addresses. A no-slip lock
`q·v_a=p·v_b` has a Farey address; the mediant is the cheapest lock between neighbours
(`PairResonance`). Owners: `HelicalPairInteraction`, `holonic_interaction/helical.rs`,
`SerialScrewChain`.

### 5. Parametron

[definition] The **complex parametron** is the ring: oriented incidence `B`, storage `M_C` and flow
`M_L`, complex modal transport, a time-periodic pump, damping and basin selection, a receiver, and
an optional two-sheet quotient. Its phase carrier is `e^{iθ}`; the half-turn `e^{iπ}=−1` exchanges
the two locked sheets, to which the pump is blind; on those sheets coupling `−w cos(θ_i−θ_j)` is
exactly the Ising pairing `−w σ_iσ_j`. A **perceptron is one receiver face of a coupled parametron
population**: fixed couplings, locked sheets, threshold readout. Storage and flow exchange at
`ω=1/√(LC)`; a section crossing of the ring is a clock tick. Owners: `Physics/PhaseCarrier`,
`Physics/CoupledIncidence`, `HolonicMeasuredParametron`, the torus realizations,
`cuda_refine/complex_parametron.rs`. Open: pump/Floquet locking dynamics; the tick-as-clock join to
`ClockedPantographicSwing`.

### 6. Tube and tower

[definition] A **tube** is the longitudinal clocked span of transports between cross-sections; a
**tower** is the transverse restriction across grains, whose compatible sections are the continuing
object and whose gluing is unique, plural or obstructed. Holonomy lives only on declared circuits.
A **world tube** adds membrane ingress, outward restriction, lawful silence (nonzero interior in the
kernel of the outward map), return and the causal adjoint into the constitution. Integration by
reflection eliminates an interior to its boundary: the Schur complement is the discrete
Dirichlet-to-Neumann map `Λ_DN`. Owners: `ContinuingTube`, `ContinuingTower`, `WorldTube`,
`ClockedPantographicSwing`, `JetStaircase`, `Neck`, `Fold`, `JunctionLaw`.

### 7. Relative completeness (globe)

[definition; agent-inferred] A region `Ω` with closed boundary `∂Ω` and boundary map
`β : interior → boundary data` (its `Λ_DN`, Schur complement or outward restriction) is **relatively
complete** for a declared exterior receiver family `R` when:

1. **coupled** — the boundary flux depends on the interior state (`β` is not constant along the
   interior dynamics);
2. **not determined** — the interior dynamics are not a function of the boundary history: the
   fibre of `β` over every admitted exterior future is nontrivial and carries nontrivial internal
   evolution (lawful silence with motion, `WorldTube.IsLawfulSilence`);
3. **closed** — `∂Ω` bounds (a globe), rather than opening onto longitudinal ends (a tube).

Completeness is always relative to `R`; no object is complete absolutely. Only a relatively complete
region can be identified as one structure with complex dynamics, and only over such a region does a
coholon orient a Holon (object 1). Instances: Birkhoff's theorem (the vacuum exterior of a spherically
symmetric body depends on its mass alone while the interior may move — coupled through `M`, not
determined by it); Gauss/ADM mass read on a bounding sphere; the band-limited **relevance theorem**
(`NavierStokesBandLimitedRelevance`: nothing feeds the far tail but frontier currents) as the same
split in a spectral chart. A cold lattice with no interior motion fails (2); a ferrimagnetic rod
that transports spin along its length is a tube, failing (3).

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
deposits only at its ends. Standing — retention — is the constitution itself as a quotient
sufficient for the admitted future (`Standing.standingLaw_exists_iff_future_factors`), never a
record of the fluxes that shaped it. One law covers both of Brandon's physical pictures:

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

[definition] A **ratio** compares two Holons, two coholons or two transports and always has
types/units: it says "this happens as it relates to that happening". It is carried as the undivided
pair (`CrossRatio`), or as a lift fibre when the denominator is not a unit (`TransportLift`). Every
ratio is both an instantaneous reading and a continuing calculus over its classes:

```text
ratio          R = Ĝ_(T←H)
log            ℓ = log R, winding as the branch            Turn, PhaseCarry, RH/Winding
first order    R⁻¹dR (Maurer–Cartan; pure gauge g∂g⁻¹)      HolonicGaugeCovariance, CellHolonomy
jet            (ℓ, dℓ, d²ℓ, d³ℓ, …): velocity, acceleration, jerk, snap, crackle, pop   JetStaircase
projective     Schwarzian (second-order invariant of the cross-ratio) [standard]
```

**Loss is the ratio of the produced and target Holons**: `ℓ=log Ĝ_(T←H)`, with the lifted complex
cross-entropy (`InformationDifference`) as its face reading and `R⁻¹dR` as the learning covector.

### 10. Receipt

[definition] A **receipt** is a field of readings over a partition of the complex, each region in
its own frame and clock. There is no global scalar and no global gradient: a region's readings and
its deposition respond only to action that actually propagated to its interface, transported into
its frame (a comparison across regions carries the clock-rate ratio at the interface, as a
gravitational redshift does). Each region reports the distribution and variability of its readings
over its own ticks — as heart-rate variability reads a cardiac oscillator's tick intervals — joined
to the flux measured along its interface. Owners: `PresentationCost` (Pareto frontier; energy and
erasure axes owed), `landauer.rs` (erasure only), `SituatedInformationRate`, `hardware_cover`.

## Keys, locks and navigation

[definition] Brandon's Enigma/Bombe reading, September 21: the rotor is a parametron ring whose
stepping is a winding with carry (`Odometer`); the plugboard and reflector are fixed material and a
boundary involution, and a passage returns through the producing operands (`A⁻¹FA`); the key is the
**initial configuration** of the generators; the Bombe infers that configuration from pairwise
**loop closure** over the menu of admitted contacts (`menu_loop_closure`: a closed menu path closes
exactly when the stage word fixes its boundary image).

[project-postulate] Every action is a key: an action expression and its antecedents, placed against
a constitution (the lock), induce a consequence as flux only when they fit. Walking, typing a
command, tying or untying a knot, a word that eases or wounds a listener, solving a puzzle — each is
finding a configuration under which already-present generator relations become relevant. A dormant
mode is available but inactive until an antecedent that fits it arrives. **Learning is locating
keys**: inferring the configuration and gauge of relevant generators from loop-closure constraints,
which prunes the search (compression) and yields the route (navigation). Teaching supplies keys;
a name is a key to a person; a coordinate is a key to a cell. The inference is general; this
repository's applications are language, mathematics, code, perception and motor control, and no
cryptanalytic application is pursued.

## Emanation and resonance

[definition] Driving a mode at an eigenfrequency of its constitution `(K, C)` sustains existing
motion at minimal work — **resonating** (RIDE). Driving off-resonance, or founding a new mode, costs
work — **emanating** (FOUND). Stored energy in the constitution is standing, with inertia `E/c²`;
propagating current is emanation; the LC exchange converts one into the other while conserving
energy. The physical floors are Landauer (erasure only), Margolus–Levitin (operations per unit
energy) and Bekenstein (stored bits per energy × radius). They are floors, not an exchange rate,
and the repository refuses a fixed mass per bit.

[definition] π and `e` are constraint identities; the identity is the generator and carries no
error. Digits are a receiver face (`RadixWindowReceiver`), and error enters only in how a face is
attained. π's base-16 digits are its address word under `x↦16x mod 1`, the same address map as the
source moment. Digit extraction jumps to position `n` by the generator power `Uⁿ` (repeated
squaring): O(log n) space, still about `n log n` time. **Partial generators** are the compiled
binary-splitting blocks `(P,Q,T)`, composing associatively (`RatioSeriesTransport.Block.compose`)
and sufficient for every continuation; they are extendable where stored digits are not. In Levin's
`Kt=|p|+log t`, a window at offset `k` costs about `2 log₂ k` against `ℓ log₂ b` for the literal. The
optimal plan is a Pareto frontier over (description bits, work, time, peak space, erasures, energy)
under a random-access deadline; no single optimum is proved, AGM is `O(M(N) log N)`, the only proven
lower bound is Ω(N), and base-10 log-space extraction is open.

## The Millennium joins

[definition] Navier–Stokes: velocity is a coholon, vorticity `du♭`, pressure the exact part,
Kelvin circulation a holonomy pairing, the Lamb term the cross-current. Hodge classes: which harmonic
coholon classes are realized by actual Holon cycles. Spectral placement: `FosterTanks` reads zeros as
LC tanks and `ZeroPairLock` gives lock ⇔ `σ=½` ⇔ positive Foster inductance — a parametron
condition. The relevance theorem is relative completeness in the spectral chart.
