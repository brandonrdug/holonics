# Compact fibres return charge, and the research workflow recovers its physics

[project-postulate] Brandon's latest September 13 correction requests active development of
the atomic/fundamental-force intuition, recovery of prior String/M and supergravity research,
and an assessment and repair of the agent workflow that neglected that material. This return
starts at `1a3c97dd`. It develops physics and repository guidance together; it does not replace
the physical request with a skill-writing task or restart broad language cultivation.

## The incorrect inference and the recovered source

[definition] The preceding answer inferred a broadly missing atomic/string map from a narrow
knot/biology review. The knot owner alone does not instantiate a physical atom, but the
repository already had a substantially wider connection, curvature, action, matter and
observable chain. The correct repair is to recover and compose those owners. Repeating that
an idea is hypothetical would neither answer the user nor follow the existing epistemic rule
that interpretations are active theorem-development work.

[established-bounded; source-inspected] The predecessor inspected here is
`~/Workspaces/laboratory` at `5cca1c5d910b922899c0296189a576aeb9a515af`; unrelated local changes
were preserved. Its `src/soma/PAPERS/holonics/mathematical-physics.typ`, entries H.0467–H.0468
(lines 506–603), explicitly develops worldsheet closure, supergravity and the Type-IIA circle.
Its July 17–19 duality/live-weave records and `FORMULA.md` retain the earlier M interpretation.
Current `research/papers/source/sections/03_comparative.typ` carries fibre integration and
retained compact modes. These sources were omitted from the preceding atomic assessment.

[historical] Brandon's July interpretation of M is open causal continuity: a proposed
container is itself another situated occurrence. The duality records accordingly treat local
descriptions and their overlap maps as the mathematical objects to connect. The August 15
lineage record recovers compressed crossings and retained winding. Its old universal claims
about keeping every state or the impossibility of a context window are not restored; current
continuation/receiver laws and later direct corrections govern their implementation.

[proved-standard] The recovered physical sources include worldsheet matter/ghost closure,
the leading sigma-model metric beta function, and the eleven-dimensional supergravity
multiplet. Its physical polarizations split as 44 metric plus 84 three-form modes, matching
128 gravitino modes. The associated dimensional statement has the stated supersymmetry and
spin-content assumptions. These are representation/field calculations, separate from our
eleven-dimensional quotient of a declared deformation receiver. See
[Samtleben, sections 2–3](https://arxiv.org/html/2303.12682v2).

[proved-standard] The Type-IIA circle relation retains

`R11 = g_s*l_s`,

`ds11^2 = exp(-2phi/3) ds10,string^2 + exp(4phi/3)(dy+C1)^2`.

Compactification thus contains a connection in its mixed metric components. The metric,
three-form and fermionic fields have their own reduced fields and interactions; a wrapped
M2 contributes a string worldsheet. This is the physical reduction source recovered from
[Witten](https://arxiv.org/abs/hep-th/9503124), with its supergravity formulation in the source
above. It is not a conclusion inferred from the word “membrane” in a software type.

[definition] Frame convention matters in this recovery. The displayed ten-dimensional metric
is string frame; Samtleben's equation 23 has Einstein-frame prefactor `exp(-phi/6)`.
Substituting `g_string=exp(phi/2)g_Einstein` makes the expressions agree. This comparison
retains the metric transformation rather than treating differing coefficients as a new force.

## The current force and matter chain

[established-bounded; source-inspected] The following source map is already present before
this increment. Each mathematical owner has its own hypotheses; these are composable steps,
not interchangeable objects bearing related names.

| Step | Current owner | Actual returned relation |
|---|---|---|
| Ordered edge/route transport | `HolonicComposition` | Joined connection transport, comparison of two routes and exact loop return |
| Four-cycle base and force fibres | `HolonicFourForceSectorCarrier` | Alternating six-plane current, dependent internal sectors and ordered face holonomy |
| Curvature and gauge | `HolonicConnectionCurvature`, `HolonicGaugeCovariance` | `F=dA+A wedge A`, Bianchi identity and `F(A^g)=g F(A) g^-1` |
| Nonabelian action/variation | `HolonicYangMillsEnergy`, `HolonicYangMillsDescent`, `HolonicYangMillsGaugeInvariance` | Integrated curvature energy, gauge invariance and the negative-square descent under periodic source/pairing hypotheses |
| Constitutive boundary | `HolonicMembraneActionTransport`, `Physics/CoupledIncidence` | Transported potential difference, admittance/current and simultaneous chart covariance |
| Electromagnetic propagation/energy | `HolonicMaxwellPropagation`, `Physics/MaxwellEnergyCone` | Constitutive wave propagation, energy/flux and receiver bounds |
| Matter occupation and Hamiltonian | `HolonicFermionicOccupation`, `HolonicFermiHubbard` | CAR, directed hopping, Hermitian energy and exact occupation-sector preservation |
| Time evolution/observable | `HolonicEvolutionKinds`, existing crystal/current receivers | Real-time self-adjoint evolution and its distinct probability, heat and constitutive charts |
| Exact executable gauge action | `crates/holonic-engine/src/lattice_gauge.rs` and `structure_group.rs` | Finite-group representation, plaquette holonomy, rational Wilson action and exact spectral receiver |

[definition] This is why “the knot results do not supply the map” was an incomplete answer.
The knot construction supplies an integral lift/loop. A connection assigns internal transport
to it; an action or constitutive law determines physical response; matter and the selected
receiver produce a current or spectrum. The missing part of a specific composition must be
identified at an actual arrow in this chain, not attributed to the whole subject.

## Compact momentum and winding now reach a spectral receiver

[proved-derived; formal-checked] New `Physics/CompactifiedModeTransport.lean` uses the
existing `HolonicTorusKnots.torusSlopeLift` and its endpoint-displacement theorem. An explicitly
declared circle-sector chart interprets its integer pair as momentum/winding charges `(n,w)`.
The supplied physical radius and alpha-prime define

`pL = n/R + wR/alpha'`, `pR = n/R - wR/alpha'`,

`M^2 = (pL^2+pR^2)/2 + oscillatorOffset`.

The library verifies that `R -> alpha'/R` with `(n,w)->(w,n)` fixes pL, reflects pR,
preserves mass square and preserves the product `nw` in level matching. The physical domain
uses positive radius/alpha-prime; the algebraic transport only needs them nonzero. Radius
has length units, alpha-prime length-squared, and mass square inverse-length-squared in
the stated natural-unit chart. Oscillator content remains a supplied sector coordinate.
The string source is [Tong, sections 8.2–8.3](https://www.damtp.cam.ac.uk/user/tong/string/string.pdf).

[proved-derived; formal-checked] The finite phase quotient now has a physical separator:
at unit radius/alpha-prime and zero oscillator offset, `(0,0)` and `(0,4)` have the same
modulo-four face but mass squares 0 and 16. Their integer lift cannot be erased merely
because that finite receiver closes. The observable loss is explicit.

[proved-derived] The same formula shows why “small compact direction” does not mean every
interior mode is negligible. Pure momentum contributes `n^2/R^2`; pure winding contributes
`w^2 R^2/alpha'^2`. Decreasing radius makes the former costly and the latter light. The
appropriate retained family depends on the energy receiver and admitted interactions.
The supplied circle model, not a universal dimensional slogan, determines that conclusion.

## Fixed compact momentum becomes a gauge coupling

[definition] The recovered metric contains the local cyclic kinetic block

`L = L_base + B(v+C)^2/2`,

where v is vertical velocity and C is the connection evaluated on horizontal velocity.
B retains the compact metric/dilaton factor. Its complete finite velocity increment is
`B(v+C)*delta + B*delta^2/2`; this identifies conjugate momentum `q=B(v+C)`.

[proved-derived; formal-checked] The new owner solves `v=q/B-C` and verifies the exact
fixed-momentum Routh reduction

`L_R = L-qv = L_base + qC - q^2/(2B)`.

This is an explicit compact-geometry-to-charge/action map. The retained connection term
couples to conserved compact momentum; the last term retains the compact energy. If B varies
over the base, it remains a source of horizontal force. The theorem verifies the algebra
and first-variation coefficient; the cyclic Euler–Lagrange source supplies conservation of q.
The normalization of C determines how q is expressed in electric-charge units.

[proved-derived] For a fixed Euclidean horizontal mass coefficient, static connection A and
potential `V=q^2/(2B)`, variation of `m|v|^2/2+q A_i v^i-V` gives

`m acceleration_i = q (partial_i A_j - partial_j A_i) v^j - partial_i V`.

This follows by subtracting `d/dt(partial L/partial v_i)` from `partial L/partial x_i` and
retaining the product derivatives. Time-dependent A also contributes `-q partial_t A_i`;
changing horizontal metric adds its connection/geodesic terms. The curvature/current form
therefore follows from the source action rather than being guessed from a loop picture.

## Connection phase enters the existing finite matter Hamiltonian

[definition] The inspected Fermi–Hubbard owner had unit real bond hopping, while phase/holonomy
lived in other owners. The concrete consuming extension attaches a complex link coefficient z
to the existing directed creation/annihilation product A:

`H_e(z)=z A+conj(z) A†`, `J_e(z)=i(z A-conj(z) A†)`.

The reverse coefficient must be conjugated. Weighting both directions by the same arbitrary
complex scalar would generally destroy Hermiticity. The completed weighted kinetic and full
Hamiltonian use the existing lattice, spin, interaction and chemical-potential owners; unit
links retain the prior API's result.

[proved-derived; formal-checked] The weighted bond/current, kinetic operator and full
Hamiltonian are Hermitian and preserve particle-number sectors. The default APIs now use
the shared weighted construction with unit links, and their old results are retained.
The single-bond matrix witness separates phase 1 from phase i in both energy and current
coordinates. The parallel-bond construction strengthens this to relative loop phase:
two unit links give forward hopping entry 2, while links 1 and -1 give 0. The theorem
`twoParallel_phase_contrast` proves the returned one-particle matrix elements differ.

[definition] The bond-current expression has the operator's chosen normalization. With
`H_kin=-t H_e`, the target-site number rate is `(t/hbar)<J_e>` when A moves source to target;
charge current also carries the particle charge factor. The incidence orientation fixes the
sign. A displayed matrix coefficient is not by itself an ampere measurement.

[definition] A single-bond phase can be removed by a consistent change of vertex and state
phase. A physical loop comparison retains all links and the receiver/state transformation.
Parallel addressed bonds provide the smallest relevant example: equal link magnitudes can
sum constructively or destructively according to their relative phase. A fixed-state current
comparison is an intervention in that source chart, not a proof that gauge-equivalent spectra
are different.

## What changed in the working method

[established-bounded; source-inspected] The relevant instructions already existed.
`THE_EXPLORATIVE_FAILURE.md` records repeated owner-discovery and premature-limitation errors;
`EPISTEMIC_GRADES.md` says an interpretation must be developed into a consequence; AGENTS
requires the framework's breadth and predecessor recovery. Lack of an instruction was not
the entire cause. The failure was that those instructions did not guide source selection and
the stopping decision in the preceding answer.

[definition] The organizational repair is one repository-owned, automatically discoverable
`holonics-research` skill with three conditional routes. It keeps the working method short and
points into maintained physics/mathematics/computation owners. It does not create three rival
ontologies, another roadmap, a generic theory manual or a blanket validation gate. Official
[skill discovery documentation](https://learn.chatgpt.com/docs/build-skills) supports the
repository `.agents/skills` location and progressive disclosure.

[definition] The root ignore rule previously excluded all `.agents` material. It now makes
a narrow version-control exception for this shared skill while keeping unrelated local
agent configuration ignored. The skill and three route references are repository source;
the richer scientific narrative remains in the current physical guide and this dated record.

[project-postulate] The skill activates before a missing-mechanism conclusion or resumed
derivation. It requires the actual source chain, attempts the connecting equation, retains
the requested domain and carries the current mathematical reason across handoffs. Its
computation route also prevents repeated timing/output errors: preserve exact returned values
and match count and elapsed population before reporting statistics. Ordinary edits stay small.

[established-bounded; process-audit] The skill initializer and frontmatter validator completed.
A fresh Luna agent received the skill and two realistic read-only requests without the
author's intended answer: recover compactification-to-charge, and assess floating timing
displays/throughput checks. It followed the relevant sources, recovered the compact reduction
and spectral consequence, and correctly separated observer statistics from native semantics.
It initially misattributed the seven-vector benchmark family to the wave workload; primary
review caught that, and its source follow-up corrected the population. This is retained as
evidence that a skill does not replace checking agent testimony.

[established-bounded; process-audit] A third narrow trial asked about a typo-only documentation
edit. The agent correctly declined to activate research recovery or broad verification.
These trials test routing and concrete behavior; they do not prove that the skill prevents
every future omission or measure a causal improvement against an unskilled baseline.

## Current validation and continuation

[established-bounded; process-audit] Final verification passed:

```sh
bash tools/lean_check.sh ElementaryHolonics.Physics.CompactifiedModeTransport \
  ElementaryHolonics.Computation.HolonicFermiHubbard ElementaryHolonics.Framework.Physics
python3 /home/b/.codex/skills/.system/skill-creator/scripts/quick_validate.py \
  .agents/skills/holonics-research
git diff --check
```

The Physics import completed at 9,097 Lake jobs, including replayed dependencies; this is
not a count of newly proved theorems. An initial integration attempt encountered the
parallel-bond proof while its owner was still editing it. The completed owner and consumer
were then built successfully together. The skill now explicitly waits for a changing
owner's return before final integration; no elapsed deadline becomes a mathematical gate.
No Rust/native behavior changed and no unrelated expensive benchmark was repeated.

[definition] The recovery, compactification/action extension, complex matter binding and
tested repository skill are complete at their stated source domains. The earlier atomic
paragraph, current guide, owner map, roadmap and operating entry point are reconciled.
The frozen laboratory and unrelated local work were preserved.

[project-postulate] The atomic extension proceeds through the recovered field/matter chain:
connection-dependent quantum transport, current/energy observations, retained compact modes
and source-specific representation/action laws. Existing Maxwell, Yang–Mills and frame/gravity
results are working mathematics in this construction. No blanket hypothesis label schedules
them out of the programme, and no declaration of ambition replaces a missing proof.
