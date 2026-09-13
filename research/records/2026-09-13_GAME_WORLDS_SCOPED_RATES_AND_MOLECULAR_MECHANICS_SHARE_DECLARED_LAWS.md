# Game worlds, scoped rates and molecular mechanics share declared laws

[project-postulate] Brandon's September 13 request asks whether any elementary notion of
intelligence/learning still needs definition, connects game worlds and tensor checkpoints,
requests consumer-hardware and benchmark consolidation, and returns double helices, molecular
mechanics and Millennium mathematics to substantive attention alongside Athena. It authorizes
bounded parallel synthesis and implementation. This record begins at `2ad5f20c`, following
the prediction/output correction; it does not reopen that correction.

## The operational account is enough to proceed

[definition] Prediction release is output of the generated face `y = rho_F(G_Theta(s,c))`.
The same relation can rearrange known pieces, fill an unknown coordinate, return an algorithm
or produce a continuation. Comparison, coefficient formation, retained state and later
re-entry have their own supplied laws. None creates a separate faculty that first makes y
output. "Learning" and "intelligence" remain useful programme/application terms where wanted;
they supply no extra acceptance condition.

[project-postulate] The engineering assessment is to proceed from equations and returned
results. The relevant remaining questions are such things as `W[S;C]=Y`, transport of the
statistics `H=sum uu*`, `B=sum vu*`, and which generator representation realizes a requested
future. The earlier vague requirements about "actual", "complete" or "sufficient" mechanisms
are replaced by those relations. Understanding the codebase assigns responsibility for
recovering and composing them; it does not give an agent authority to invent a qualitative
intelligence standard.

## A saved world and a checkpoint

[definition] A common executable account is

`x_(k+1) = T_Theta(x_k, u_k; c_k)`, `y_k = rho_F(x_k)`.

Here x is the continuing state, Theta the retained generator/parameters, u the incoming
occurrence, c its relevant conditions, and rho the requested receiver. Disk serialization is
an exterior chart of some of these quantities. The running process supplies the operations.
Neither useful inference nor a game update must write to disk every cycle.

| Declared use | Retained generator/state | Requested face and necessary continuation |
|---|---|---|
| Procedural world | Seed, generator/version, coordinate/condition maps and changed state | A finite region, with overlap and future boundary dependencies |
| Static map | Asset geometry/materials, incidence/spatial structure and dynamic deltas | Render, collision, audio or simulation output through its own receiver |
| Parameter checkpoint | Tensor contents plus the architecture and execution conventions that interpret them | Forward output; training resume additionally needs the optimizer/schedule/random state required by that training law |
| Native HNN rest/application | Retained morphology/generator, current/condition fibres and pending returns required by the admitted continuation | The same public generated-face and successor owners |

[established-bounded; source-inspected] Safetensors stores named tensor data with shape/dtype
metadata and supports selective/lazy access. Its file format is not an architecture or a
complete training algorithm. Which state is actually saved determines what can be resumed.
See the [format source](https://github.com/huggingface/safetensors) and
[selective loading documentation](https://huggingface.co/docs/safetensors/main/en/index).

[definition] The organism/mechanism distinction is likewise a choice of boundary and
continuing responsibilities. An enzyme reaction, a game subsystem or a mathematical automaton
can be a constituent of a larger ecology; that does not make every constituent an autonomous
organism. Identify the exchanged currents, state and boundary before applying the label.

## Demand, visibility and world generation

[proved-derived] The existing future-relevance construction permits condensation when every
admitted future receiver factors through the retained representation. In the dynamic case,
`q T_i = U_i q` transports that representation through each generator. For a requested window
R, the relevant source is the dependency closure of R under the chosen continuation, or an
equivalent boundary/generator description. The proof does not require materializing an
unbounded ambient world.

[definition] Visibility, simulation activity, contact and storage are different receivers.
An offscreen source may still affect shadows, sound, collisions, agents, pressure or a later
query. A loading radius is a declared approximation unless the actual dependency relation
closes inside it. Cut-scene prefetching and coarse geometry can hide or reduce latency, but
their mathematical contract is unchanged. A finite pixel raster bounds output samples;
it does not by itself bound the computational complexity of finding each sample.

[interpretation] The game-to-HNN map sends chunk/window addresses to situated source/receiver
addresses, simulation updates to admitted generators, generated tiles to delivered faces,
and cached interior state to a generator/quotient plus required residual. Its preservation
condition is the future receiver equation above. A pair of equal cached faces with different
admitted future outputs falsifies the proposed cache quotient. This is a concrete test of
representation, not a requirement to keep all earlier states.

[established-bounded; source-inspected] Existing owners already supply relevant parts:
`world.rs` has `ExactEventLaw` and atomic `CausalWorld::receive/receive_through`;
`contact_chart.rs` has declared contact schedules; `dilation.rs` retains finite horizon and
frontier; `streamed_standing.rs` owns pooled staging/transfer. Their apparatus or schedule
roles are not silently promoted into a terrain generator. `Foundation/CausalRelevance.lean`
and `Transport/WorldTube.lean` retain future scope and addressed chronology.

[established-bounded; source-inspected] [InfiniteDiffusion](https://arxiv.org/html/2512.08309v4)
constructs seed-consistent local queries through finite overlapping denoising windows and
weighted accumulators. Its appendix derives query-order consistency in deterministic exact
arithmetic; fixed query size, bounded overlap and fixed diffusion depth give a bound on model
calls independent of absolute location. That cost model treats other operations as free.
The implementation uses tiled noise, cached/persistent windows and coarse-to-fine terrain
decoding. Learned geographic appearance is not a calibrated tectonic/erosion trajectory.
Its documented coarse-scale and scattered-query limitations matter to that application.
The [repository](https://github.com/xandergos/terrain-diffusion) supplies the engineering source.
The inspected revision is `e8dcb4b1a834ab2f6b1a6f5256ed7c9f2f3e8230`:
[`world_pipeline.py`](https://github.com/xandergos/terrain-diffusion/blob/e8dcb4b1a834ab2f6b1a6f5256ed7c9f2f3e8230/terrain_diffusion/inference/world_pipeline.py)
owns the tile seed, overlapping stages and decoder;
[`evaluation/latency.py`](https://github.com/xandergos/terrain-diffusion/blob/e8dcb4b1a834ab2f6b1a6f5256ed7c9f2f3e8230/terrain_diffusion/evaluation/latency.py)
measures first/second tile delivery. The external `infinite-tensor` package is not vendored
here; the paper's deterministic construction is not a bitwise GPU implementation certificate.

[definition] Unbounded indexed generation and finite materialization are compatible. The
harder geographic task is choosing source laws/models that give the desired multiscale
structure, locality and consistency at affordable cost. Calling this cartography identifies
its application; it does not remove the learned parameters from a diffusion generator.
In floating-point implementations, mathematically commutative sums also need a numerical
ordering/tolerance contract before claiming bitwise query-order identity.

## The four supplied papers have different receivers

[established-bounded; source-inspected] The following table records the inspected source
scope and the resulting application map; it does not identify their different game notions.

| Primary source | Inspected construction | Consequence for this work |
|---|---|---|
| [Dayanikli and Lauriere, network formation](https://arxiv.org/html/2508.03847v1) | Agents control pair-indexed weights; `Z_i=integral w_i(j) E[X_j] dj`, `dX_i=a_i(Z_i-X_i)dt+sigma_i dW_i`. A finite-group specialization supplies forward/backward equilibrium conditions. | A strategic interaction model supplies an explicit graph/control law. Its Nash equilibrium and its temporal source are different from a render loop or physical contact. |
| [Benatti and Costa, Simple Games on Complex Networks](https://arxiv.org/html/2406.15636v1) | Five two-team movement/strategy rules on four graph families; game duration and outcome statistics compare their dynamics. | Topology, occupancy, move rule and interaction events must remain separate inputs to any adapter. A graph count alone does not predict play. |
| [Tariono et al., Enhancing Cross-Regional Multiplayer Gaming: Implementing Client-Side Prediction to Reduce Network Latency](https://doi.org/10.1016/j.procs.2025.08.300) | Procedia Computer Science 269 (2025), 474–484. Bibliographic/indexed abstract scope only; full publisher text was inaccessible. | A locally predicted face precedes server confirmation; a later discrepancy is a returned difference. No uninspected algorithm or timing result is adopted as Holonics evidence. |
| [Klein et al., Variable Frame Timing](https://arxiv.org/html/2306.01691v1) | Controlled display-timing variations changed perceived smoothness; their matched-smoothness aiming task did not show an additional significant performance effect. | Preserve latency distributions, input/render/display boundaries and receiver conditions. A mean FPS does not determine perception. |

[established-bounded; source-inspected] The frame-timing PDF's first-page timeline was rendered
and inspected: render completion, VSYNC repetition/drop and VRR display intervals differ.
That is a direct reason to keep native work, output delivery and physical display clocks
separate. These sources motivate the measurement design; they do not measure our runtime.

## Local clocks, information and performance

[definition] A frame-like event is one completed requested face delivery. A tick-like event
is one completed admitted update at a specified continuing owner. The definitions permit
nested and overlapping receiver families; there is no privileged global frame. A kernel
launch is counted as a launch, not silently as either event. A read-only prediction already
delivers output without implying an owner update.

[proved-derived; formal-checked] The existing
`Foundation/SituatedInformationRate.lean` now also proves:

`r_F = N_F / dt`, `r_T = N_T / dt`,

`r_(1+2) = (dt_1*r_1 + dt_2*r_2)/(dt_1+dt_2)`,

`t' = a*t+b  =>  r' = r/a`,

`information/time = occurrence_mass/time * information/occurrence_mass`.

The serial law combines disjoint observation windows. Concurrent intervals cannot simply
be added. A signed reversal gives a negative oriented quotient; positive elapsed throughput
uses positive durations. These laws do not assume time reversal of the underlying generator.

[proved-derived; formal-checked] For the same finite positive source/model distributions and
an assigned event rate, the code-rate identity is

`r H2(p,q) = r H2(p) + r KL2(p||q)`.

Expected code rate is different from rate of state updates. Actual conditional code length
is `sum -log2 q(y_k | conditions_k)`; divide by the associated elapsed interval to get bits/s.
Repeated identical faces can have different code costs under different conditions. The
existing exact prime-log owner preserves code forms while a decimal value is a display.

[definition] Time parity has several explicit maps: reversal of a clock coordinate, reversal
of a source trajectory, complex conjugation of phase, and reversal of a stochastic path law.
They coincide only under additional source identities. Existing `PhaseCarrier` distinguishes
direct `az`, reflected `b conjugate(z)` and mixed modulation; `InformationDifference` proves
phase-conjugation parity without exchanging source/model distributions. `ReceiverCodeCost`
proves detailed balance for its symmetric positive-generator construction. A dissipative
system requires reversed currents and appropriate environment conditions, not just `t -> -t`.

[proved-derived; formal-checked] `ReceiverCodeCost.edgeCodeProduction` now supplies a second
precise parity law. For positive opposite directed rates a,b in the same reference units,
`sigma_2=(a-b)*log2(a/b)` is nonnegative and unchanged when a and b are exchanged: both current
and log-ratio reverse sign. The existing Perron detailed-balance relation makes it zero.
The code-rate reading does not by itself supply a heat bath, temperature or physical entropy
production law. It connects an oriented difference to an even scalar comparison explicitly.

[proved-derived; formal-checked] If each counted event requires at least `w_min > 0` units of
one resource, and at most `B*dt` such units are available, then

`N*w_min <= W <= B*dt  =>  N/dt <= B/w_min`.

This makes a computational capacity analogy precise. CPU arithmetic, GPU work, memory traffic
and storage each have their own units and bound; use the jointly applicable ceilings. There
is no universal numerical "speed of light" here. Physical causal propagation or energy per
information additionally needs its physical source, units and boundary law.

[definition] A geometric constant is not a conservation law by itself. For example phi is
algebraic, satisfying `phi^2=phi+1`; pi and e are transcendental. An invariant receiver needs
an evolution identity such as `q T=q`. A transported face uses `q T=U q`. Neither the
algebraic classification of a constant nor dimensional notation supplies that identity.

## Molecular shape, torque and double helices

[established-bounded; source-inspected] DNA's duplex geometry joins complementary pairing,
antiparallel backbones and a helical arrangement; the original structural source is
[Watson and Crick](https://pubmed.ncbi.nlm.nih.gov/4599080/). Sequence-dependent stacking and
salt/environment alter stability, so a pairing-only account is insufficient; the
[nearest-neighbor thermodynamic study](https://pubmed.ncbi.nlm.nih.gov/9465037/) makes that
dependence quantitative. Chirality, steric constraints, electrostatics and solvent belong
in the source model rather than being inferred from a helix drawing.

[definition] A rod/duplex chart retains a centerline `r(s)` and a material frame `R(s)`.
Curvature and material twist are different derivatives of that frame. At base-pair scale,
rise/shift/slide and twist/tilt/roll provide translation and rotation coordinates. Strain
relative to a sequence/environment-specific reference couples through a stiffness law.
The topology of a closed ribbon, local elasticity and dissipative contact have different
receivers; one need not replace the others.

[proved-derived] For the elementary screw curve
`r(theta)=(R cos(theta), R sin(theta), p theta)`, `R>0`, differentiation gives curvature
`R/(R^2+p^2)` and Frenet torsion `p/(R^2+p^2)`. Changing the sign of pitch preserves curvature
and reverses torsion. These kinematics do not choose R or p: a material/energy law does.
Material twist of a framed duplex is also distinct from centerline Frenet torsion.

[definition] One periodic phase plus an open axial coordinate gives a cylindrical chart;
two independent periodic coordinates give a torus. A closed duplex adds its closure and
linking data. Non-orientability requires an orientation-reversing gluing such as a Möbius
seam; a double helix alone supplies no such seam. This separates local screw geometry,
periodic parameter space and globally knotted embedding.

[established-bounded; source-inspected] For a closed, nonintersecting duplex with a chosen
framing/closure, `Lk=Tw+Wr` separates linking number, material twist and centerline writhe.
Twist can become writhe through buckling while linking is fixed. Strand-passage enzymes can
change linking class. Experiments on
[topoisomerase II and writhe](https://pmc.ncbi.nlm.nih.gov/articles/PMC3650406/)
provide an actual controlled torsion/strand-passage source, beyond visual analogy.

[established-bounded; source-inspected] The
[protein tube model](https://pmc.ncbi.nlm.nih.gov/articles/PMC419539/)
shows how steric exclusion, directional hydrogen bonds, chain geometry and hydrophobic
interactions can produce recurring fold families. This is a coarse-grained model; a particular
sequence and environment still select its conformation and kinetics. Our existing finite
FCC-chain/ligand model similarly declares sterics, contact energy, blocked moves and marked
product emissions in the
[sequence/fold/reaction return](2026-09-10_SEQUENCE_FOLD_AND_REACTION_CURRENT_MAKE_THE_CAUSAL_THOUGHT_CHAIN_CONCRETE.md).

[definition] A finite twist/stretch energy already exposes the mechanical content of the
intuition: `E=(C*t^2 + 2D*t*e + S*e^2)/2` gives conjugate torque `C*t+D*e` and extension
force `D*t+S*e`. Equal twist does not determine torque when extension differs and `D != 0`.
The shared coefficient gives reciprocal cross response. Positive energy needs positive
semidefinite stiffness; topology alone supplies none of these coefficients.

[proved-derived; formal-checked] The new three-coordinate rod specialization in
`Physics/ConstitutiveModulation.lean` adds bending and its mixed coefficients, proves the
response is exactly the existing `coupledResponse` with identity incidence, and verifies
the finite twist/extension energy increments with their quadratic remainders. It proves
reciprocal cross response and the torque separator under nonzero coupling, equal bend/twist
and unequal extension. This is a formal constitutive construction, not a calibrated DNA run.

[definition] With contact displacement and angular motion, `delta W=f dot delta r`,
`torque=r cross f` and `P_rot=torque dot omega`. A Rayleigh law
`Phi(v)=v^T C v/2`, `C` positive semidefinite, gives heat rate `v^T C v >= 0`.
A linked pair of loops constrains possible motion; friction additionally depends on
contact, normal force, material and medium. A gyroparallelogram describes a specified
composition law; it is not enough by itself to determine those forces.

[interpretation] A useful knot map sends a molecular configuration and covalent incidence
to a framed backbone/duplex with an explicit closure and knot/link receiver. Chemically
distinct states with the same knot class but different reaction currents separate that
receiver from the complete dynamics. `HolonicTorusKnots.lean` already proves integral
winding constructions and finite-probe ambiguity. It does not turn a topological knot
into an electronic state or a complete atom.

[interpretation] The atoms-as-knots and string-theory ideas require a more specific source
map: state space, interaction/action, charges and measured spectrum/current. The current
finite quantum owners provide occupation/CAR, Hamiltonians and coherent transport;
they do not provide this molecular-to-string correspondence. Entanglement is represented
by joint quantum states/observables, not replaced by a single flux number. Evolving joint
currents are a useful question precisely when the Hamiltonian and receivers are retained.

## Formal and Millennium work keeps its own mathematical return

[project-postulate] The roadmap now explicitly gives formal/physical/arithmetic work
substantive attention alongside HNN. The same useful construction can feed several domains,
without requiring a language product to justify a theorem or a Millennium theorem to permit
a useful local algorithm. The current rate and rod work is a direct mathematical return.

| Existing line | Concrete mathematical relation to keep working | Productive connection |
|---|---|---|
| RH / Gamma / heat | Actual xi source, positive kernels, remainder and global sign/zero receiver | Analytic generators and code/phase statistics with source tails |
| Navier–Stokes / fluid current | Full source, pressure, unresolved feedback and quantitative remainder | Local domain reduction must preserve relevant nonlocal boundary effects |
| Hodge / integral topology | Cycle-class source, kernel/cokernel and realization of a specified class | A matching spectral face alone does not produce a realizer |
| BSD | Arithmetic source and L-function transport at the claimed curve/rank domain | Retain the arithmetic map behind equal numerical faces |
| Yang–Mills / quantum | Defined field/interaction, continuum and spectral-gap obligations | Molecular rod topology is a different source, though operators/transport can be shared |
| Complexity / Rubik / constrained solving | Uniform input family, generators, preprocessing, query/decoding, bit costs and representation size | Cheap reuse is valuable; its amortized construction cost remains visible |

[proved-standard] P versus NP is a uniform asymptotic decision question over encoded input
families; [Cook's statement](https://www.claymath.org/wp-content/uploads/2022/06/pvsnp.pdf)
fixes that scope. A finite Cayley graph diameter bounds shortest path length, not the cost
of finding paths over a generalized family. Counting reachable configurations, constructing
a shortest-path policy and executing a found word are three different computations.

[established-bounded; source-inspected] The consolidation corrected stale live prose in
`TABLET_THE_CHART` that treated finite exhaustion as finding/verification cost equality and
claimed a missing work vector after `ExactWork` already existed. It also repaired the nearby
false rational/integral FLT distinction: clearing denominators preserves the homogeneous
equation, so a nontrivial rational point would yield a nontrivial integral one. Those errors
would distort the requested complexity and measurement synthesis if left governing.

## Benchmark return and verification

[established-bounded; measured; computational-witness] The
[benchmark source and receipt](../experiments/native_performance_benchmark/README.md)
use existing public mathematical, wave-session and code-cost owners. The final default suite
completed in **8.692623196 seconds** on the Ryzen 9 7900X / 32 GB / RTX 4080 SUPER desktop.
It uses the current **debug binary** and ordinary workstation conditions, not an optimized
or isolated-machine calibration. The binary fingerprint, source revision, OS clock and
before/after load and GPU temperature (48 to 49 degrees Celsius) are retained in `result.json`.

| Measured operation | Repeated roundtrip rate | Median latency | p95 | p99 | Complete 128-request session rate |
|---|---:|---:|---:|---:|---:|
| Resident C5^16 applied to a supplied vector, exact returned face | 3,084.52 faces/s | 0.319749 ms | 0.352992 ms | 0.395301 ms | 308.15 measured faces/s |
| Seeded wave `receive-next-symbol`, committed observation | 422.44 updates/s | 2.312777 ms | 2.556704 ms | 2.641543 ms | 195.90 measured updates/s |

[definition] Each rate is a count divided by its stated elapsed population. Repeated request
round trips exclude setup/warmup and Python parsing between requests; complete session time
includes process creation, setup, transport and final return/checkpoint. There is one explicit
warmup per session. The wave's total epoch delta is 129, of which 128 are measured. C5 inputs
cycle over seven vectors, with every exact output and retained readback checked; this is a
timing workload rather than 128 independent generalization examples. The 128 samples support
empirical order statistics, not a certified production tail law.

[established-bounded; measured] Eight fresh processes per workload give median child wall
times about 353.17 ms (C5 construct/power/warmup/application/readback) and 350.07 ms
(seed/warmup/observation/checkpoint). Median observer-inclusive times are 373.50 and 374.06 ms.
Peak Linux child RSS across those samples is 276,676 KiB and 282,820 KiB respectively.
The fresh resource wrapper prevents an earlier child from contaminating that peak; CPU
seconds, page faults and context switches are separate returned fields.

[established-bounded; measured] The warm mathematical receipt reports **2,572 octets** peak
native payload residency, **19,564 octets** ingress, **33,088 octets** receipt egress and
**12,480 octets** section egress. Payload residency is not whole-device allocation or process
RSS. Wave-native transfer/allocator high-water and isolated kernel-event timing are not
exposed by these current receipts; they remain unknown rather than zero. The SSD's supplied
7300/6300 MB/s ratings and the 20W ideology are not measured bandwidth/energy here.

[established-bounded; implemented-exact; computational-witness] Construction work retains
separate source reconstruction, minimal-polynomial/reduced-power and rank-factorization
vectors, including 30-bit peak written rationals in the power construction. The independent
integer C5 power/application and exact `Fraction` comparison verify all measured outputs;
using integer truncation would have hidden rational errors and was repaired. Every wave
request must return a committed observation. Eight fresh code-cost runs retain exact
symbolic cross-entropy and `4/3 bits/step` stationary entropy; the numerically equal declared
cost `4/3 cost-units/step` is kept in its own unit. This does not fabricate a native code-rate
measurement from the time to run a mathematical demonstration.

[established-bounded; process-audit] Verification returned successfully:

- `bash tools/lean_check.sh ElementaryHolonics.Foundation.SituatedInformationRate`;
- `bash tools/lean_check.sh ElementaryHolonics.Physics.ConstitutiveModulation` after its shared-owner binding;
- `bash tools/lean_check.sh ElementaryHolonics.Foundation.ReceiverCodeCost ElementaryHolonics.Framework.Information` after the code-production addition;
- `cargo check -p holonic-engine --lib` for the inspected existing engine owner;
- nine Python measurement/reference tests and the complete default public-native benchmark;
- source diff review and `git diff --check`.

[definition] A broader agent-started formal build encountered an unrelated generated setup
header failure; it is not counted as a successful umbrella build. The changed-owner targets
and the Information consumer subsequently passed. No theorem uses Lean inside inference.
The initial mixed setup/warm timing artifact and subsequent measurement-review snapshots
remain recoverable in `.local`; they are not the final evidence. Duplicate printed benchmark
output was moved there, while the final raw receipt stays beside its source. Unrelated user
files, flux-lattice work and existing caches were preserved.
