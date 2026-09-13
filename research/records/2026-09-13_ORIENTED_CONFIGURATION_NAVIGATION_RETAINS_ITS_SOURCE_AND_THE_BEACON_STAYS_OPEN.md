# Oriented configuration navigation retains its source, and the beacon stays open

[project-postulate] Brandon's latest September 13 corrections clarify public sharing as a
beacon, generalize navigation through joints/modes rather than cube-piece taxonomy, reject
source-erasing magnitude/extremum drivers, and insist that forming a map/checker has a causal
cost. His subsequent bird/migration example places the continuing mode, inherited origin,
sensory redirection and next occurrence at the centre. This return starts at `4d50db9e`.

## Continuation is the primary object

[definition] A situated body has already undergone formation. Its present state can encode a
mode of continuation without encoding an explicit catalogue of every location or history.
An autonomous source law can continue with no new external input; sensory/current returns
change its conditions and conduct. Stopping or redirection is itself a consequence of the
law, boundary, internal change or an incoming occurrence. A stable locomotor mode and knowing
which destination to pursue are different receiver questions about that same continuing body.

[definition] Returning to an earlier spatial location is a new occurrence at another time,
with the retained orientation, body, environment and history-dependent conditions. Equal
position does not establish equality of the complete state. `Transport/WorldTube` and
`ReceiverPotential` already retain addressed chronology and future families; the new account
does not install another motion engine or require an archive of every past state.

[definition] “Difference of infinities” is represented here through compatible families and
their transport, rather than subtraction of infinite cardinalities. Many histories can map
to one face. A changed observation or contact can exclude some futures and introduce others;
equal cardinality does not mean the same possibilities. The actual next occurrence is
addressed relative to the current source, clock and conditions. A generator or joint
constraint can carry an infinite continuation family in a finite description where the task
admits one. This does not require a completed global atlas before motion can begin.

## What the preceding implementation actually did

[established-bounded; source-inspected] The preceding `group_navigation` implementation was
ordinary exact Dijkstra preprocessing on a finite, static group with fixed positive move
costs. Its queue orders scalar distances; the diameter takes their maximum, and solution
readout chooses one minimizing move. It retained the group, generators, costs and all
minimizing choices, so other words remain reconstructible from that source law. It did
not retain an independent winding history as part of its state, nor model changing joints,
adversarial control, contact modes or physical momentum.

[definition] Its finite results remain valid for that declared memoryless group source.
Promoting it to a public engine navigation owner was the wrong generalization. The code is
now preserved under `crates/holonic-engine/examples/support/group_navigation.rs`; the public
engine export is removed and the Rubik comparison calls that support directly. The geometry,
distance and full-state reference receipts are retained. This repairs the architectural
claim without pretending the finite mathematics itself failed.

## Magnitudes and extrema are receiver faces, not substitutes for the source

[proved-standard] The real map `x -> |x|` is noninjective: x and -x share its output. The
identity `|x|=sqrt(x^2)` describes the same folded real receiver. It does not prescribe a
unique implementation or establish a physical motion or momentum law. For complex input,
the magnitude instead uses `sqrt(z*conj(z))`; argument and winding need their own lift.
Actual arithmetic/transport costs belong to the realization being used, not to a claim that
one notation is a free physical primitive.

[definition] Retaining only a norm, RMS value or extremum can discard orientation, phase,
correlation and predecessor distinctions. Retaining the original source, relevant fibre and
operation does not have that same consequence. The source itself may be implicit in a
generator/constraint rather than copied as raw history. A finite min/max is deterministic,
not intrinsically a statistical estimator; the objection here is its promotion into a
source-free native selection law.

[proved-derived] For two real coordinates, `m=(a+b)/2`, `d=(a-b)/2` give the invertible chart
`a=m+d`, `b=m-d`. By contrast, `min(a,b)=m-|d|` and `max(a,b)=m+|d|` omit the ordering when
the sign of d is omitted. The existing `TwoFaceConstitutive` plus/minus coordinates already
provide this kind of paired mode reconstruction. The positive energy or magnitude face can
be read afterward without replacing the oriented carrier.

[established-bounded; source-inspected] In the preceding gap proof, the expression
`|G(v,v)-F(v,v)|<=epsilon||v||^2` was a bound on a signed expression, not a native update
assigning a magnitude to F or G. Both source forms and v remained in the theorem. The
clarification still improves the construction: only the lower polarity is needed to carry
a lower gap.

[proved-derived; formal-checked] `MassGap.lean` now takes the oriented return
`G(v,v)-F(v,v)>=-epsilon||v||^2` directly and returns
`G(v,v)>=(Delta-epsilon)||v||^2`. The independent upper theorem uses
`G(v,v)-F(v,v)<=epsilonPlus||v||^2` to transport an upper bound. The two allowances need
not be symmetric. This removes an unnecessary absolute-value assumption while retaining
the full difference; a positive return is not treated as damage to a lower bound.

## An existing Swing relation gives a directed approach

[established-bounded; source-inspected] `Millennium/Navigation.lean` already proves that
the split constraint `x*y=T`, on its positive chart, has the involution `x -> T/x` and
work `W=x+T/x`. Its fixed point is the global work minimizer. The earlier response should
have recovered this construction before treating finite graph search as the general method.

[proved-derived; formal-checked] The new passage is

`x'=(x+hT)/(1+hx)`, with homogeneous matrix `[[1,hT],[h,1]]`.

For positive T,x and nonnegative h, it has positive denominator and image. Its signed step
and signed residual obey

`x'-x = h(T-x^2)/(1+hx)`,

`x'^2-T = (1-h^2 T)(x^2-T)/(1+hx)^2`.

In the positive-determinant regime `h^2 T<1`, orientation is retained and the passage with
parameter -h recovers the source. The cross-multiplied reconstruction is
`(1-hx')x=x'-hT`. These are actual return identities, not a selected minimum detached from
its incoming configuration.

[proved-derived; formal-checked] The work return is

`W(x')-W(x) = -h(x^2-T)^2/[x(x+hT)(1+hx)] <= 0`.

The square occurs in this work receiver; the carrying passage still retains the signed
residual and inverse. No list of candidate x-values is scanned and no square root is
evaluated to generate the step. The root is the already-derived fixed-point face of this
particular constraint. T and the constraint's origin remain part of the source; this
conditional construction does not claim their acquisition from an unknown world was free.

[proved-derived; formal-checked] General matrix configurations use the undivided pair `(U,V)` and ordered block
transport `(AU+BV,CU+DV)`. The existing `Geometry/CrossRatio.RatioPresentation` is extended
at that carrier, including noncommuting ring/matrix entries. An affine ratio chart can be
read when its denominator has the required inverse. At a singular chart the pair remains;
there is no RMS substitute for a nonexistent inverse. The block composition and common
right-multiplication identities are checked over an arbitrary ring, retaining multiplication
order. The fractional-chart theorem states its algebraic domain and recovery relation;
an executable inverse and its cost belong to the concrete algebra/codec owner.

[definition] A singular affine denominator and a noninjective whole transport are distinct.
An invertible whole block may need another affine chart; a noninjective block requires its
source fibre/remainder. Merely keeping two output slots does not make every block invertible.
Common right multiplication is a reversible rechart only when that factor is a unit.

[proved-derived; formal-checked] For the scalar passage, two sources obey
`x'-y'=(1-h^2 T)(x-y)/[(1+hx)(1+hy)]`, so strict order is preserved in the admitted positive
chart. The undivided quadratic obeys
`U'^2-T V'^2=(1-h^2 T)(U^2-T V^2)`. It remains oriented; it is not declared to be a conserved
physical energy without a corresponding constitutive/normalization map.

[proved-derived; formal-checked] With `a>0`, `a^2=T`, the signed chart
`z=(x-a)/(x+a)` transforms by `z'=[(1-ha)/(1+ha)]z`. For `0<ha<1` the factor lies strictly
between zero and one. This gives the finite-step contraction law behind approach to the
fixed point. The root is used to analyze the chart; the rational matrix operation does not
evaluate it. Changing source conditions require the ordered product of the corresponding
blocks, rather than treating a changing mode word as repetitions of one frozen matrix.

## Joint/mode configurations beyond the cube

[definition] Start with the active incidence and its local state/conditions, rather than
piece names as machinery boundaries. The total configuration chart can range over different
active incidences; an elementary allowed passage is still `S <- W -> S` with its source,
target, conditions and returned difference. A named generator is partial when its contact
or game rule is not available. A capture, attachment or separation can change which
passages exist. The existing `Holon`, `JointReceiverDescent`, `SwingPotential` and
`WorldTubePotential` owners supply this compositional starting material.

[historical] The recovered human chess correction is in Claude thread
`5c98052d-2f8f-4a4e-a6fe-1329b41f63ea`, message
`a1bc8d3e-0cbd-47a2-af65-ebb92d09b373`, at `2026-09-05T21:38:22.635Z`.
Brandon observed that the then-current lattice converged while all 32 pieces stayed present;
captures should change the active ecology and its possible outcomes. The corresponding local
untracked flux-lattice source and record were inspected read-only and preserved. Raw private
messages and attached image data are not copied into this beacon.

[definition] A chess configuration retains turn, active piece incidence, legal-action
conditions and rule-relevant history/rights. Its transition changes that state and the next
admissible action family. A forced continuation has alternating control quantifiers, such
as `exists our_move, forall admitted_reply, continuation_condition`. This relation is not
the same as a shortest path through a fixed group. A probability model of the opponent
adds its own source distribution; it is not silently exchanged with the universal quantifier.

[definition] Spider-Man-style travel additionally retains continuous position, momentum,
anchor/contact mode, obstacles and the objective clock. For a fixed taut rope with
`r=x-anchor`, the conditions include `r dot r=l^2` and `r dot p=0`; a mode law can have
`xdot=p/m`, `pdot=mg+u-lambda*r`. Differentiating the tangent condition determines
`lambda=(p dot p/m+r dot(mg+u))/l^2` on that mode. Slack/taut transitions, attachment and
release require their actual guards and impulse/return maps. These equations exhibit the
joint constraints; they do not claim a completed city controller.

[definition] The action is a functional of a trajectory, its mode word and its control,
with endpoint and contact constraints. First variation, constrained covectors and boundary
returns determine a stationary continuation. An extremal family can be represented by
inequalities against feasible variations, retaining ties and the source. Global optimality
requires the corresponding convexity, remainder or other certificate; a local gradient is
not silently upgraded to a guarantee across obstacle classes or adversarial futures.

## Procuring the relation is part of the causal computation

[definition] The earlier SAT reply held fixed a checking relation and a candidate while
Brandon was challenging that exclusion. It did not answer the cost of forming the relation,
its representation and its inputs. The full account here retains

`formation/update of relation + candidate construction + candidate comparison`,

with their actual dependencies, reuse, inherited standing and receiver clock. The parts
need not occur as isolated serial phases; a returned difference can change them together.

[definition] The standard [P-versus-NP statement](https://www.claymath.org/wp-content/uploads/2022/06/pvsnp.pdf)
conditions on a fixed checking relation and measures input-dependent computation. That is
a different question from total acquisition of an unknown model. It does not declare a
candidate or its formation causally free. The claim that checker construction necessarily
has the same cost as finding a solution needs an additional construction or reduction;
sharing a history/setup cost alone does not prove it.

[proved-derived] A checker can be built by composing local predicates:
`R_C(z)=and_(c in C) r_c(z)`. Adding a newly formed constraint returns
`R_(C plus c)=R_C and r_c`. This composition constructs a checking map without constructing
an accepted z or a table of all accepted configurations. The costs of learning/forming
the predicates and obtaining z remain real costs; they are not erased by that distinction.
If the law itself is uncertain, retain a joint relation `R(theta,z)` over its compatible
source family. Existential compatibility, universal validity and prediction under one
retained model then have different explicit quantifiers.

[project-postulate] The bird/migration explanation sharpens the relevant programme: an
already formed body continues from its actual origin and builds its usable cartography
through action and returned observations. A solution is a new placement in that continuing
ecology. We should measure and construct that whole relation, while keeping conditional
complexity results at the scope they actually establish.

## The beacon and the returned work

[definition] `docs/BEACON.md` makes the strongest ideas and source available. The earlier
candidate/contribution list remains useful reading material; paper packaging is not the
requested task. Root navigation and the skill now carry the corrected meaning.

[established-bounded; computational-witness] The public mathematical session has returned
six exact oriented split observations at powers 1, 4 and 16 from two initial sections.
Both homogeneous coordinates, signed residuals, work differences and inverse source recovery
are retained in `research/experiments/oriented_split_transport/result.json`. Matrix powers
are constructed through the existing owner and applied resident; ratio decoding and independent
reference arithmetic are exterior. The observation counts are apertures, not minimum scans
or stopping thresholds. This is a consumer of the declared split law, not a new universal
learner, chess engine or model-acquisition result.

[established-bounded; process-audit] Verification passed:

```sh
cargo test -p holonic-engine --example rubik_corner_quotient_navigation
cargo build -p holonics-workbench --bin holonics
bash tools/lean_check.sh ElementaryHolonics.Millennium.Navigation \
  ElementaryHolonics.Geometry.CrossRatio ElementaryHolonics.Millennium.MassGap \
  ElementaryHolonics.Framework
python3 research/experiments/oriented_split_transport/run.py
python3 /home/b/.codex/skills/.system/skill-creator/scripts/quick_validate.py \
  .agents/skills/holonics-research
git diff --check
```

Six reference-search tests passed in their new exterior location. The Framework consumer
completed with 9,129 Lake jobs, including replayed dependencies. The rebuilt public session
returned all six oriented observations with full source recovery and the undivided signed
quadratic return checked. Subsequent source-comment clarifications do not change the checked
declarations. The code move, polarized bounds, matrix/Swing construction, native consumer
and beacon are complete at these scopes. No full chess or city controller is claimed.
Existing reference evidence and unrelated local work remain recoverable; no caches or user
flux-lattice material were deleted.
