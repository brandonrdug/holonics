# Fractal generators and latent reasoning

[project-postulate] Brandon's September 8 clarification treats fractals as recurring generator
laws, their causal parameters, restrictions and intersections, and the geometry these produce.
This is part of Holonics' mathematical and physical subject, not a visual style. His proposal
that elementary generator families can organize much wider phenomena remains a research
programme to construct and test. This research is folded into the active AC0–AC5 goal.

## External result and its scope

[established-bounded; source-inspected] Lai, Bao, Quinn and Gilpin's September 4 preprint,
[Fractal basins trap latent reasoning](https://arxiv.org/html/2609.04963v1), reports intricate
settling-time basins in several recurrent reasoning models. Nearby initial states can follow
different routes near saddle-like regions before settling. A training experiment links improved
solving to changed stability. The appendix distinguishes scale-invariant and slim fractal behavior.
Its probes fix a model/task, sample two-dimensional initial-state slices, use finite loop caps
and decoded-output settling, and exclude some nonsettling/multistable cases. These are bounded
empirical results, not a proof of fractality at every scale or a lower bound for all solvers.
Its finite-field linear-system task already admits Gaussian elimination; learned transient cost
cannot establish that the mathematical problem requires exhaustive candidate search. Source and
methods were read; experiments were not reproduced. The authors provide
[loopscape](https://github.com/GilpinLab/loopscape) as their probing apparatus.

[proved-standard] This is established computational mathematics territory. The
[Ercsey-Ravasz–Toroczkai 2011 work](https://www.nature.com/articles/nphys2105) maps satisfiability
to deterministic continuous dynamics and relates transient chaos to fractal basin boundaries.
It explicitly keeps the energy cost beside continuous running time. It supplies prior evidence
for treating fractal geometry, computation and physical realization together.

## Generator, population and measured picture

[definition] A generator family consists of actual maps `g_i(lambda)` on declared domains,
with causal parameters lambda and admissible compositions. An ordered word w denotes
`g_w=g_(i_k) ... g_(i_1)` with the intermediate domains and lineage retained. Geometry comes
from the resulting population, its limits, overlaps and restrictions. A rendered finite image
is a receiver of that construction. It neither defines the generator nor establishes its
infinite-scale behavior.

[definition] For a declared recurrence T and a receiver region A, the set `T^(-k)(A)` means
the complete preimage of A under k forward operations. It is not an instruction to reverse
physical time or choose an inverse. First-arrival populations remove the earlier arrivals
from that preimage. Repeated preimages and their separating histories are a precise way to
study complicated return-time geometry using the project's existing Preimage Fibre ontology.

[proved-derived] The standing `FractalPacking.lean` interval owner gives a simple exact
example. On the unit interval use inverse branches

```text
g_left(x)=x/3,      g_right(x)=(x+2)/3.
```

They are the two surviving branches of the open forward map `T(x)=3*x` on `[0,1/3]` and
`T(x)=3*x-2` on `[2/3,1]`, with escape through the middle open third. After n restrictions,
the surviving population has `2^n` separated intervals of width `3^(-n)` and total length
`(2/3)^n`. This follows by composing the two affine maps and using the owner's width and
sibling-separation laws inductively. Their nested intersection is the Cantor survivor set.
One finite generator description therefore governs unbounded refinement and arbitrarily long
finite survival. No pixel sampling is needed to state these relations.

[definition] That example specifies an operator, domain, hole and length receiver. It does
not prescribe ternary scaling, two branches or a one-dimensional topology for HNNs. In broader
families, phase, restriction maps, parameter changes and intersections can change the geometry.
Local smooth manifolds and globally fractal invariant sets are distinct descriptions; derivative
arguments retain the regularity of the chart or stratum on which they operate.

[conditional] A weak unstable direction with multiplier q>1 obeys the local linear law
`delta_k=q^k*delta_0`. Reaching a receiver radius r requires the least k with
`q^k*abs(delta_0)>=r`, for `0<abs(delta_0)<r`. With rational q, delta_0 and r, that comparison
is exact by integer/rational powers. Small delta_0 or q close to one can require many passages.
For a nonlinear system, its Taylor remainder and admitted neighborhood must also be controlled;
the linear law alone does not identify a saddle in our model.

## Consequences for current construction

[project-postulate] Brandon further proposes a lattice of transport tubes between manifolds,
with classifications informed by category and Galois theory. Towers, curved passages, polarity,
capacitating fields, leader growth and returned current belong in this construction. His quantum
interpretation concerns unresolved causal parameters and free axes. The following gives precise
existing carriers and first compositional laws for that programme; it does not found another engine.

[established-bounded; source-inspected] `tube.rs::ReceiverTube` already retains a receiver-local
star/link, transverse primitive section, projective transports and an ordered transition word.
Its change classification distinguishes deformation, refounding, rebase and retained support.
That implementation is a finite terminal/projective chart, not a general-dimensional neural
tube. The broader `HolonicSensoryWorldTube.lean::ClockedSpan` retains arbitrary typed source,
target, local-clock face, receiver and obstruction. Its pullback composition preserves those
objects through split/rejoin and refuses a missing joining occurrence. `Holon.lean` owns the
elementary addressed diagram and its Preimage Fibre.

[definition] A useful tube presentation is a family of local sections connected by addressed
transport, with internal state and boundary receivers. A tube lattice is their incidence,
branching, joining and higher comparison cells. A tower records restriction maps between
grains. For transport T and restriction r, the exact scale compatibility is

```text
r_target o T_fine = T_coarse o r_source.
```

When it fails, retain the actual difference/fibre and its future effect. A curved passage also
retains path dependence: parallel transport along two routes can differ at their common target.
For invertible passages their comparison can be expressed as loop holonomy; for general spans
the paired returned images and joining populations remain without inventing an inverse.
Restriction defect and curvature are distinct relations until a constitutive map identifies them.

[conditional] If a geometric region W has incoming/outgoing boundary inclusions
`X -> W <- Y`, a contravariant field/section construction gives
`Fields(X) <- Fields(W) -> Fields(Y)`. This is the existing holonic span in a concrete
geometric realization. Where the field theory supplies the gluing/descent law, gluing regions
corresponds to a pullback of compatible field populations. Boundary values alone are sufficient
only when that law says so; required jets, fluxes, constraints and nonlocal pressure data remain
part of compatibility. The source/target manifolds and the transported state sections therefore
have different categorical roles, with their map connecting them explicitly.

[proved-derived] The generator/observation relation admits an exact classification construction.
For parameters theta and observations o with compatibility predicate C(theta,o), define

```text
Models(O)={theta | every o in O satisfies C(theta,o)},
Consequences(S)={o | every theta in S satisfies C(theta,o)}.
```

Unfolding the definitions gives
`S subset Models(O) iff O subset Consequences(S)`, an antitone Galois connection. More actual
observations constrain the parameter family without requiring a unique member. Empty compatible
families retain an obstruction; they do not become productive omniscience through vacuous truth.
This closure is distinct from a Galois group of a field extension. The existing
`arithmetic_monodromy.rs` gives a concrete group-classification instance from witnessed prime
sections, retaining unconstrained alternatives instead of identifying root sheets by their names.

[interpretation] Category theory organizes the typed passages and their lawful composition;
group actions organize recharting and symmetries of an admitted family. Recursive generator words
then organize tubes across scale, with intersections determined by actual joining constraints.
The maps above are the proposed bridge to the current HNN: its source/current sections are the
cross-sections, its retained contact/return is the passage, and changing local morphology changes
future conduct. The first test is the scale square and the same complete return after transport.
Missing joining equality or a future separating history is a concrete falsifier. The old
three-dimensional rendering tube is not silently installed as intrinsic HNN dimension.

[proved-derived] Quantum receiver uncertainty can retain coherence that a probability face
forgets. The two matrices

```text
rho_coherent=(1/2)*[[1,1],[1,1]],
rho_mixed=(1/2)*[[1,0],[0,1]]
```

have equal diagonal readings, but their readings at the projector `P_plus=rho_coherent` are
`trace(P_plus*rho_coherent)=1` and `trace(P_plus*rho_mixed)=1/2`. This follows by matrix
multiplication. Free variables behind one receiver therefore must retain phase/coherence when
another admitted receiver distinguishes it. `HolonicPolarizedCrystalTransport.lean` already
joins complex path amplitudes before taking intensity, and the finite quantum transport
umbrella retains occupation and Hamiltonian laws. Those state, composition and receiver laws
make the quantum face precise; unspecified ignorance alone does not supply them.

[definition] Integration by reflection supplies a tube's boundary response with its interior
source/reconstruction law; the existing Schur/diffusion construction is one exact realization.
Capacities, conductances, units and field dynamics belong to a physical electrical instance.
The finite fluid/curvature owner `NavierStokesCurvedTransport.lean` retains circulation, boundary
turn and conditional covariant-source interfaces; its supplied balance and geometric hypotheses
must remain visible. This scope is reusable mathematical material without asserting that the
current HNN implements microscopic electron dynamics or a full Einstein/quantum realization.

[proved-derived] A small normalized derivative need not mean a small discrepancy. For binary
probabilities `p=(1-e,e)`, `q=(e,1-e)`, `0<e<1/2`, put `r=q-p`. Then

```text
J_p=diag(p)-p*p^T=e*(1-e)*[[1,-1],[-1,1]],
J_p*r=2*e*(1-e)*r.
```

The full r remains nonzero as e tends to zero while the Jacobian-weighted return tends to zero.
For softmax real potentials s, with q fixed, differentiation gives

```text
-d_s KL(q || p)=q-p,
-d_s (||q-p||^2/2)=J_p*(q-p).
```

The two receiver metrics therefore have different potential returns. The normalized receiver
implemented during this turn retains both r and its weighted return, together with the original
complex current reports. Neither a scalar loss nor a small pullback norm is a thought-completion
criterion. The full complex source is not replaced by its real probability face.

[interpretation] The productive question is which learned generator and retained causal path
changes a later return, and which directions the current receiver compresses. The source map
is the actual native recurrence, the receiver is its declared current/probability projection,
and the returned covector travels through the producing morphology. Repeated restriction and
rebase can make an action reusable across extents. A future separating history or a nonzero
transported remainder falsifies a proposed condensation. This connects generator geometry,
learning and compression through concrete operations, without choosing a fractal appearance.

[definition] A stability study of HNN must include the complete relevant successor, including
changing morphology and newly founded coordinates. On a fixed smooth chart the finite tangent
transport is the ordered product of the actual step derivatives; changing charts additionally
owe their transport maps. A frozen operator can answer a declared observer question, but it
does not replace the continuing learner. Basin entropy, pixel uncertainty exponents, random
initialization and loop thresholds remain exterior study choices, not native governors.

[open] No fractal basin or transient-chaos diagnosis has been established for Athena. Its
repetitive outputs may have other causes, including a wrong attracting cycle, insufficient
source organization or a missing developmental return. The paper does not make the previous
implementation churn inevitable. We must inspect the actual recurrence and returned differences.

[definition] AC1's next implementation uses the complete normalized return and its declared
metric through the producing ecology. AC1's path/reuse step now explicitly asks for generator
laws, ordered restriction/rebase and future-separating directions. If a stability or basin
probe answers a concrete failure, use exact admitted perturbations and retained full trajectories
at a stated scope; do not start a large sampling campaign merely because the paper uses one.
No new fractal subsystem or qualitative acceptance gate is introduced.
