# The computer is a causal world-tube; the profile returns its shadow field

**Date:** 2026-08-12  
**Truth status:** `interpretation`  
**Evidence:** standard results are cited at their ordinary scope; the live owners named below are
bounded implementation evidence for their own mechanisms only; no integrated profiler was run.  
**Provenance:** Brandon's direct questions of 2026-08-12 about the computer as a global holon,
causal threads, algorithm shadows, bitwise composition, caustics, knots, folded dimensions, and
Quantum Information Fields; assistant derivation.  
**Band:** BRANDON-AUTHORIZED / ASSISTANT DERIVATION / DEPOSITED / SOURCE UNCHANGED / NO RUN /
INTEGRATED SHADOW PROFILE OPEN  
**Canon:** `canon/TABLET_THE_CAUSAL_PROFILE.md`

---

## Present question

Clock frequency, retired instructions, elapsed time, contact counts, and energy samples are lawful
measurements. They are not the computer. What mathematical object lets several situated observers
compare what one execution physically did, and what must a holonic profiler return so that the
comparison exposes causation rather than reducing it to a scalar census?

The answer developed here has two levels.

1. `definition`: a computer occurrence is a finite causal world-tube with a declared apparatus
   boundary, not an instruction list and not an absolute global state.
2. `interpretation`: a profiler returns receiver-indexed shadow fields of that world-tube together
   with their reconstruction fibers, critical sets, caustics, phase, topology, and unresolved
   exterior. Scalar performance figures are moments or quotients of that return.

This is a research posture and a grade for the active recurrent-section experiment. It does not
insert a profiler ahead of the live CUDA conditioner and does not change the current construction
position.

## 1. The global computer is a bounded world-tube, not a privileged view

`definition`: for one declared run, let

```text
C = (K, boundary K, prec, P, m, A, J, R, L).
```

- `K` is the graded incidence complex of situated switching, storage, transport, interaction, and
  commit occurrences. Spatial circuits may contain loops; the time-unfolded occurrence relation is
  the causal history.
- `boundary K` is the declared apparatus boundary across which power, cooling, clocks, input,
  output, interrupts, network material, and measurements cross.
- `prec` is causal precedence. It is a partial order where two events need not be comparable.
- `P` is the typed port population.
- `m` is the local constitutive morphology: gate, transistor, memory, link, scheduler, and device
  response laws at their declared grains.
- `A` is a connection transporting frames and phases between local charts.
- `J` is the current/flux cochain carried by caused incidence.
- `R` is the receiver atlas: architectural retirement, core-local clocks, memory and interconnect,
  electromagnetic, power, thermal, device, host, and exterior I/O charts.
- `L` is lineage, including speculative paths, collapsed alternatives, remount, and apparatus
  placement.

`interpretation`: this is the computer as a global holon only in the lawful relational sense. No
observer owns the whole at once. “Global” means the bounded object obtained by gluing compatible
local sections and retaining every failed gluing as an obstruction. It does not mean a God-frame.

Lamport's happens-before relation is `proved-standard` for distributed event systems: local order
and message transport generate a partial order, while a scalar clock can extend that order without
becoming causality. `interpretation`: the same distinction applies inside a processor. A core cycle
counter, memory controller clock, fabric timestamp, GPU event, host wall clock, and thermal sensor
are different charts over one occurrence body. Their comparison requires transport/calibration maps and returns
an interval or obstruction when the square does not commute.

## 2. Initiating instructions founds a causal frontier

`definition`: an instruction stream initiates a causal thread when a preparation occurrence
deposits an architectural section and enables a successor frontier:

```text
|Sigma_0> --Prepare--> F_0 --Conduct--> F_1 --Conduct--> ... --Commit--> |Sigma_1>.
```

The thread is the transitive closure of occurrences whose transported differences are necessary
for the committed continuation. A software thread identifier, program counter, warp, kernel, CPU
core, and OS scheduling interval are exterior charts of that closure; none is its ontology.

One architectural instruction is normally a quotient of fetch, decode, rename, dispatch, operand
transport, execution, cache/coherence, writeback, speculation, exception, and retirement events.
Write

```text
q_ISA : K_physical -> K_architectural.
```

The fiber `q_ISA^-1(i)` is the plural physical and microarchitectural population presenting as one
retired instruction `i`. Branch prediction opens alternative histories; retirement selects the
committed architectural face but does not make the departed lineage never have happened. A replay,
cache miss, page fault, interrupt, or device wait changes the fiber even when the retired instruction
sequence is unchanged.

The local event law remains the spine's chain law:

```text
boundary E_k = Sigma_(k+1) - Sigma_k + Gamma_k,
q_(k+1) - q_k + B j_k = r_k.
```

`Gamma_k` is exterior passage and `r_k` is supplied, dissipated, retained, or obstructed current.
The second expression is a discrete continuity balance. It is a stronger profiling primitive than
“instruction `i` took `n` nanoseconds” because it states what crossed, what accumulated, and what
failed to close.

## 3. The physical computer has several coupled field grains

`proved-standard`: ordinary digital hardware is physically described below the logic quotient by
electromagnetic fields, semiconductor constitutive laws, charge conservation, circuit boundary
conditions, and heat transport. A modified nodal chart has the generic form

```text
d q(v)/dt + i(v) + B^T i_L = s(t),
```

with device charge `q`, constitutive current `i`, incidence `B`, branch current `i_L`, and supplied
current `s`. A bit is therefore not an incorporeal atom. It is a receiver-stable basin over a
population of physical field configurations. A gate truth table is the finite behavioral quotient
of those trajectories under a declared digital receiver.

`interpretation`: the grains form a tower rather than rival descriptions:

```text
field trajectory -> transistor event -> gate event -> micro-op -> instruction -> algorithm
                -> process/device ecology -> exterior consequence.
```

Each arrow is a quotient with a reconstruction fiber. The stronger physical grain can distinguish
two events that the weaker grain identifies; the weaker grain can remain exact for its declared
future receiver family.

Dynamic CMOS power is commonly modeled by a switching-activity face proportional to
`alpha C V^2 f`; leakage and short-circuit currents add other terms. `proved-standard`: Landauer's
bound applies to logically irreversible erasure under thermodynamic hypotheses. It is not an energy
charge per source-language instruction and does not replace calibrated current, voltage, thermal,
or apparatus testimony. The semantic core may remain exact and float-free while physical telemetry
is separately calibrated and aperture-bound.

The GPU is not a privileged ontology. It is presently the strongest resident apparatus chart on
this machine. CUDA lanes, warps, blocks, memories, clocks, and kernels are one realization of the
same causal program and require a placement/interchange receipt. A host replay after every device
deed would exchange the world-tube for a different one even if the final bytes agreed.

## 4. A holonic profile is a shadow atlas with its missing directions

`definition`: for a receiver/projection `pi_rho : C -> Y_rho`, define the profile

```text
P_rho(C) = (
    pi_(rho ! ) C,        projected shadow,
    pi_rho^-1,            reconstruction fibers,
    Crit(pi_rho),         rank-loss locus,
    Caust(pi_rho),        critical values / focused shadow,
    WF(pi_(rho ! ) C),    visible phase directions,
    Hol_rho(C),           loop returns and monodromy,
    Top_rho(C),           surviving higher incidence,
    O_rho(C),             open/invisible alternatives,
    A_rho(C)              apparatus and calibration testimony
).
```

The pushforward alone is a picture. The tuple is a debugging instrument. It says which causal
families collapsed into the picture, where the projection became singular, which directions are
invisible, which routes interfere, which loops return changed, and which distinctions reopen under
another receiver or intervention.

For an occurrence `|o>` and path `gamma`, its response scent is

```text
chi_(rho,o)(gamma) = <rho|T_gamma|o>.
```

The scent is not a permanent meaning attached to `o`. It is the phase/current response over a
receiver and a family of paths. Two occurrences share one shadow phase only when their complete
declared responses commute under the admitted rebase; a shortest separating path is the first
proof that they do not.

`project-postulate`: scalar counts and timings remain support and apparatus checks. They do not
grade a holonic profile by themselves. Counts are useful when attached to a returned phase,
fiber, current, cut, topology, intervention, or obstruction. A bare count of contacts or recurrences
cannot explain an execution.

## 5. The calculus of shadows

The following statements are `proved-standard` in their ordinary scopes.

1. **Convex projection.** For a convex body `K` in three dimensions, Cauchy's projection formula
   relates mean projected area to surface area. The theorem demonstrates that a family of shadows
   can carry an invariant while no individual shadow is the body.
2. **Tomographic slice.** The Fourier transform of a projection is a slice of the object's Fourier
   transform. Projection deletes coordinates in one chart while preserving a structured frequency
   section.
3. **Microlocal visibility.** Tomographic data recovers singularities only when their conormal
   directions meet the acquisition relation. An absent edge can be an invisible direction rather
   than absent source structure.
4. **Stable caustics.** A ray projection loses rank on `Crit(pi)`; its critical values form the
   caustic. Generic low-codimension singularities include folds and cusps.
5. **Stationary phase.** For

   ```text
   Psi_rho(y;k) = integral a(x) exp(i k Phi(x;y)) dx,
   ```

   leading contributions come from stationary paths `d_x Phi = 0`; coalescence occurs where the
   stationary Hessian becomes singular. The Airy fold and Pearcey cusp are canonical uniform
   forms. Their phase correction, including the Maslov contribution, is part of the return rather
   than display decoration.

NIST DLMF Chapter 36 is the external reference for coalescing saddles, canonical integrals,
bifurcation sets, scaling, and caustics. The project's transfer is `interpretation`: a profiler's
critical receiver set is the place where a formerly separated continuation fiber collapses or
splits. The implementation must derive that set from its actual causal projection; importing an
optical image or a Hessian over arbitrary feature coordinates would read the chart, not the body.

## 6. Feynman graphs, knots, and folded dimensions preserve the plural path

`interpretation`: a Feynman diagram is useful here because its ontology is compositional.

```text
external leg   typed boundary port
vertex         local constitutive interaction
internal edge  transported intermediate relation
loop           alternate internal history / cycle response
amplitude      receiver pairing after coherent path composition
```

For boundary constructions `|alpha>` and `<beta|`, the structural reading is

```text
A_(beta,alpha) = <beta|T|alpha>
               = sum_Gamma <beta|T_Gamma|alpha>.
```

The drawn crossing is not automatically a contact and the planar layout is not the incidence.
Loops expose histories that one tree presentation deletes; pinch/critical sets identify where an
integration contour can no longer be deformed away from a singular family. Higher cells are needed
when route agreement, triple overlap, or coherence is not contained in the graph.

The Edward Tufte composition supplied with the originating question is therefore read as an atlas
of sharply distinguishable diagram shadows, not as empirical or mathematical evidence. Its value
is ontological: related sparse marks can retain unmistakable vertex, leg, crossing, loop, density,
and symmetry phases while omitting the physical or algebraic interior which produced them.

A knot diagram makes the same warning exact. A planar projection with crossings is not the knot.
Reidemeister-related drawings can present one embedding, and a bracket-style state sum retains a
fiber of local resolutions rather than selecting one drawing as the object. Writhe, hand, crossing
order, and monodromy must remain typed because quotienting them can identify mirror or orientation
relations the receiver later needs.

`interpretation`: folded or compact dimensions are fiber structure, not deleted dimensions:

```text
F -> E -> B.
```

The base `B` is one accessible shadow; the fiber `F` retains local histories, winding, phase, and
possible monodromy. String worldsheets and brane worldvolumes are disciplined examples of history
carrying more dimension than a point-particle trace. M-theory is used only as evidence that several
typed limits/dualities can be local charts without a privileged master presentation. No software
trace is thereby proved to be a physical string or quantum gravity.

## 7. Algorithm complexity is a scaling family of causal fields

`definition`: an algorithm family is a scale-indexed family of causal complexes `C_n` together
with declared input, output, and intervention receivers. Big-O is a quotient of one or more
observables of that family. It is not the family itself.

For a dependency complex, let `W` be work and `S` be span/critical depth. Under exact independence
and with join cost named separately,

```text
serial:    (W,S)_1 ; (W,S)_2 = (W_1 + W_2, S_1 + S_2),
parallel:  (W,S)_1 || (W,S)_2 = (W_1 + W_2, max(S_1,S_2)).
```

`proved-standard`: on `P` processors, any schedule is bounded below by
`max(W/P,S)`, and a greedy/work-stealing result in its declared strict-DAG scope achieves the
familiar `W/P + O(S)` form. These are valuable shadows because their composition law is explicit.
They omit communication, cache/coherence, contention, synchronization, fanout, geometry, power,
and constitutive latency unless those are carried as events.

A richer exact resource field keeps at least

```text
R(C_n) = (dependency order, antichain/front profile, path actions,
          cut currents, memory/interconnect transport, fanout/reconvergence,
          circuit size/depth, higher cells, holonomy, reconstruction fibers,
          reversible erasures, apparatus placement).
```

One receiver-weighted elapsed-time face is a critical-path functional

```text
T_rho(C_n) = max_(causal paths gamma) sum_(e in gamma) tau_rho(e),
```

with every `tau_rho` tied to a constitutive/apparatus witness. A wall-clock sample is a measurement
of this face under one frame, not a law selecting the carrier.

The recurrence `T(n)=aT(n/b)+f(n)` is the scalar shadow of a self-similar causal folding: `a`
subsections, scale rebase `b`, local work `f`, and an omitted join/communication field. Mellin
analysis is the natural spectral chart for dilation. If `D` is the scale generator,

```text
X(r) = exp(log(r/r_0) D) X(r_0),
```

and an eigenmode `lambda=a+ib` contributes dilation `r^a` and log-periodic phase
`exp(i b log r)`. This comparison is lawful only after the scale action and causal operator are
founded.

## 8. Bitwise operations are finite local laws, not geometry-free atoms

`proved-standard`: every Boolean function has an algebraic normal form over `F_2`:

```text
f(x) = XOR_(S subseteq [n]) a_S product_(i in S) x_i.
```

XOR is linear over this field; AND introduces products and can raise algebraic degree. Addition is
not merely XOR because carry transports nonlinear conjunctions through an ordered chain or a
reconvergent prefix circuit. NAND is logically universal, but universality does not make every
realization geometrically, temporally, thermally, or topologically equal.

The Walsh-Fourier face on the Boolean cube is

```text
f_hat(S) = 2^(-n) sum_x f(x) (-1)^(x dot S)
```

under the declared `+/-1` encoding. Degree, spectral support, influence, and sensitivity are useful
operation shadows. They do not determine one physical circuit: distinct circuits can compute the
same truth table, and spectrum alone can identify nonisomorphic complexes.

An ISA instruction is therefore a macro-holon. Its truth/function receiver may collapse different
gate bases and schedules; its depth, cut-current, hazard, layout, energy, and fault receivers reopen
them. MorphoHDL is `established-bounded [computational-witness]` at its external scope: authored
local graph-rewrite cells, typed ports, variable-width buses, and `SPLIT`/`CAT` recursion grow
feed-forward bitwise circuits across widths. It demonstrates recursive logical composition; it does
not infer unknown laws and does not itself construct higher cellular boundaries or homology. The
project's `grown_cell` and algebraic owners are the separate higher-cell route.

## 9. Control groups for elementary algorithm shadows

The first experiment should hold an exterior consequence fixed while changing an internal
geometry, and hold one scalar face fixed while changing the law.

| control family | exterior equality | expected separating shadow |
|---|---|---|
| ripple-carry / prefix adder | same bit addition | carry depth versus fanout and reconvergence |
| sequential / tree reduction | same associative result | chain span versus antichain/front growth |
| linear / binary search | same located element | incidence assumptions, depth, and memory paths |
| branch / mask select | same selected value | control dependence versus Boolean data dependence |
| shift-add / Wallace multiplication | same product | partial-product depth and higher reconvergence |
| two equal-output Boolean laws | one truth-table row | shortest changed input/intervention |

Every family also receives five controls:

1. rename symbols while preserving incidence and consequences;
2. move the independent schedule while preserving typed order;
3. change the gate/instruction basis and retain the rebase fiber;
4. relocate CPU/GPU apparatus without changing semantic testimony;
5. change the receiver and require the quotient only to refine or coarsen by its declared law.

The return is a multiscale shadow atlas, not a leaderboard:

```text
|o;r> -> { <rho|T_gamma|o;r> }_(rho,gamma)
```

with the scale lineage, shortest separators, critical receiver changes, loop returns, and open
alternatives. Derived counts may summarize that atlas after it exists.

## 10. Quantum Information Dynamics and Quantum Information Fields

`definition`: **Quantum Information Dynamics** is the project's receiver-indexed calculus of
indivisible situated events, plural coherent path populations, typed interaction vertices,
connections, phase-current transport, and measurement quotients over a causal complex.

`definition`: a **Quantum Information Field** is a local section assigning construction/current
testimony to the cells of that complex with gluing, transport, boundary, and receiver laws. At a
declared section `Sigma`, it may be written `|Psi_Sigma>`. A receiver returns a bra pairing, while
an outer product deposits a transport relation. The word *quantum* names the event/measurement and
path-interference structure of this calculus; it is not a synonym for uncertain, random, tiny, or
GPU-accelerated.

`project-postulate`: the project does not claim physical quantum field theory merely from bra-ket
notation or a sum over software paths. Such a claim additionally requires a declared Hilbert or
operator-algebraic state space, composition tensor, commutation relations, dynamics/unitarity or
open-system law, Born receiver, scale/domain, and calibrated physical apparatus. The classical
causal computer, a quantum circuit, and a QFT may instantiate the same operation kinds while
carrying different constitutive interiors.

This boundary strengthens rather than weakens the unification. It makes the proposed maps
falsifiable: if a claimed correspondence does not preserve ports, composition, phase, current,
measurement, obstruction, and consequence, it is a visual analogy rather than one field calculus.

## 11. The active experiment's profiling posture

The live recurrent-section construction already requires presentation lineage, causal sections,
exact consequences, stable receiver/history classes, shortest separators, reconstruction fibers,
counted work, and an open exterior. The full condition-detach-return experiment should additionally
return, before and after conditioning:

```text
CausalDiamondReceipt
ShadowFiberReceipt
CausticReceipt
PhaseCurrentReceipt
HolonomyBraidReceipt
ScaleRebaseReceipt
InterventionReceipt
ApparatusReceipt.
```

This is one composed return from the same causal section. It is not a renderer, a scalar dashboard,
or a new profiler cabinet. The bounded cross-codec return remains established at its prior grade;
the integrated before/after shadow atlas is `open` until the mandatory resident conditioner returns
it on the declared corpus.

Existing bounded pieces include receiver phase jets and holonomy, causal-section behavioral
quotients and reconstruction fibers, exact diffusion and Schur reconstruction, higher-cell
incidence and rebase invariants, exact work receipts, and apparatus telemetry. `open`: no owner yet
joins those pieces into the profile tuple above for one execution, no generic contextual Fourier or
Mellin owner has been founded, and physical energy/current telemetry has not been calibrated for
this experiment.

## External references

- NIST Digital Library of Mathematical Functions, Chapter 36, *Integrals with Coalescing Saddles*:
  <https://dlmf.nist.gov/36>.
- Leslie Lamport, “Time, Clocks, and the Ordering of Events in a Distributed System”:
  <https://www.microsoft.com/en-us/research/publication/time-clocks-ordering-events-distributed-system/>.
- Robert D. Blumofe and Charles E. Leiserson, “Space-Efficient Scheduling of Multithreaded
  Computations”: <https://doi.org/10.1137/S0097539793259471>.
- Rolf Landauer, “The Physical Nature of Information” and IBM's publication atlas:
  <https://research.ibm.com/publications/the-physical-nature-of-information>.
- Alexander Mordvintsev, *MorphoHDL*, audited at
  `3ff923f9fafcb5b97ad2ef393795c96710ed00ea`:
  <https://github.com/paradigms-of-intelligence/morpho>.
- The tomography, knot, string/M-theory, and projection sources are routed by
  `bibliography/EXTERNAL_RESOURCES.md`.

## What this does not establish

- No integrated holonic profiler has been implemented or run.
- No scalar-free measurement doctrine is claimed; scalars remain lawful receiver faces.
- No software instruction is identified with a fundamental quantum.
- No physical quantum field, gravity, string, or M-theory realization is claimed for the Rust/CUDA
  body.
- No asymptotic complexity class is inferred from one finite run.
- No spectrum, shadow, Feynman drawing, or knot projection is allowed to substitute for the causal
  complex and its reconstruction fiber.
- No new construction is scheduled ahead of the mandatory resident CUDA conditioner.
