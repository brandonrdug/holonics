# Relative code cost has an addressed boundary law

[project-postulate] Brandon asks for Shannon entropy and optimal code-length lifted to the
full holonic setting: executable generators, manifolds, causal flux, time axes and physical
receivers. The purpose is reusable bounds feeding Hephaestus/HNN and source-specific problems,
including the de Bruijn–Newman threshold and computational complexity.

## Entropy belongs to a receiver and its conditions

[definition] Let Ω_B be the admitted source/history family under boundary conditions and
shared standing B. For a finite receiver R and declared probability measure μ_B, set
`p_R(a|B)=μ_B(R⁻¹(a))` and `H_R(μ_B)=−Σ_a p_R(a|B) log₂ p_R(a|B)` on its positive support.
The source can be a complex field, a world tube, a conformational population or a generator
family. Higher dimension changes that source, its admissible incidence and its receiver
partition; it does not require replacing Shannon's logarithm. The full current, phase,
correlations and preimage fibre precede this scalar face. Signed or complex current is not
silently a positive probability mass. A flux-derived measure must declare how it treats
orientation, crossing and normalization while retaining the original current.

[proved-standard] Correlation remains in the joint distribution and conditional chain rule;
summing marginal entropies generally discards it. An invertible rechart carrying both source
measure and receiver leaves the finite outcome probabilities unchanged. For continuous charts,
relative entropy uses the density ratio `dμ/dν` with its reference ν transported as well.
Differential entropy against freshly chosen coordinate volume can acquire a Jacobian term.
Shannon entropy is therefore a situated information receiver, not the total physical state or
a coordinate-free physical entropy current by itself. [Shannon's original development](https://www.princeton.edu/~wbialek/rome/refs/shannon_48.pdf)
already treats constrained sources, channels with unequal symbol duration, and generators such
as a shared machine producing π.

## What is optimized

[definition] An admitted representation includes an executable decoder/generator, parameters,
retained source fibre or reconstruction, clock, remainder and the required receiver family.
Shared decoder material belongs in B; newly transmitted material is charged to the return.
For an occurrence x, one precise task is

`L*(x; R,B,ε,budgets) = inf { L(p|B) : p is executable and meets R's declared reconstruction/continuation tolerance and resource bounds }`.

For a population use expected length under its declared measure. A static face match and
preservation of every admitted successor are distinct tasks. The latter reuses
`ReceiverHistoryCompression.generatorExact` and `quotientCommutesWithEveryOrderedWord`:
`q T_i = U_i q` lifts the local generator law to the complete ordered future family. A
choice-defined inverse is not an executable decoder.

[definition] Literal data, recurrence blocks, analytic generator words and hybrid residual
packets can inhabit the same admissible family. This expands the constructions available to
produce the requested face, just as retaining complex phase and coupled fields expands a fluid
representation's expressivity. Neither extension erases its constitutive laws or remainder.
A local optimum admits no improvement among declared nearby/admissible variations; it need not
be globally best. A minimum needs an attainment argument. Finite grammars, compact continuous
families and unrestricted programs have different search and existence/computability questions.
The existing `CopsonDeBruijnFiniteSharp` owner already demonstrates compactness, attained minimum,
sharp coefficient and an equality witness at its particular finite tail surface.

[definition] Preserve the cost vector `(description bits, executed work, elapsed clock, peak
residency, calibrated energy, reconstruction defect)`. Choose a declared objective and budgets,
or retain incomparable alternatives. Adding bytes, seconds and joules without exchange factors
would not define a quantity. A shorter generator can cost more to execute; if its output must be
fully materialized, output work must also be paid. Shared source knowledge and the receiver task
explain a generator's saving; it does not violate a fixed ensemble's source-coding bound.

## The returned local-to-boundary law

[conditional] For an admitted finite directed channel with positive edge costs c_e, suppose a
capacity coordinate C and positive state weights h satisfy

`Σ_{e:s(e)=v} 2^(-C c_e) h(t(e)) = h(v)`.

The transfer matrix is `K_C(v,w)=Σ_{e:v→w}2^(-C c_e)`: the displayed law is
`K_C h=h`. For a finite irreducible channel this is the positive-eigenvector condition at
spectral radius one. Thus the coding capacity already has a spectral characterization.
Then `Q(e|v)=2^(-C c_e) h(t(e))/h(v)` is normalized. With `V=log₂ h`, the ideal information
length of one edge is

`ℓ_Q(e) = C c_e + V(s(e)) − V(t(e))`.

Serial composition telescopes the middle potentials through the actual joining equalities:

`ℓ_Q(γ) = C c(γ) + V(source γ) − V(target γ)`.

This is Shannon's unequal-cost constrained-channel construction read through the repository's
addressed boundary owner. For a stationary admitted source P, conditional KL adds the exact
mismatch: `C E_P[c] = H_P(edges|state) + E_state KL(P(·|state) || Q(·|state))`.
The stationary boundary expectation vanishes. Thus `H_P/E_P[c] ≤ C` for positive mean cost,
with equality at Q's stationary source. These statements require the displayed normalization,
support and stationarity; an arbitrary local score does not supply them.

[proved-derived; formal-checked] `Foundation/ReceiverCodeCost.lean` formalizes the more general
balance with a retained residual on each occurrence:

`ℓ = C c + V_source − V_target + r`.

It composes two such balances using **existing `Holon.Interaction` pullback occurrences**;
the middle face cancels only by `joined.joins`. Repeated application covers longer serial
compositions without creating a second path engine. It also proves the actual quantitative
receiver bound: if C>0, `|V_source−V_target|≤B` and `|r|≤E`, then

`(ℓ−B−E)/C ≤ c ≤ (ℓ+B+E)/C`.

Its third theorem transports an attained feasible minimum across a candidate equivalence
preserving admissibility and cost. It does not manufacture a minimizer or a global optimizer.
These are conditional algebraic laws with checked proofs, not unconditional physical bounds.

[interpretation] On a manifold the analogous code-cost difference can be a one-form/cochain.
A potential part contributes a boundary term. Nonzero loop circulation prevents representing
the complete difference by a single global scalar potential; retain the residual/holonomy.
This is where the existing Hodge, gyro/turn, knot and world-tube owners become necessary.
A smooth local cost density can define an action on admitted paths, but topology-changing
moves and nonlocal decoder constraints still need their own admissibility. One cannot declare
all optimal representations to be ordinary Riemannian geodesics.

## Exact finite control

[established-bounded; implemented-exact; computational-witness] The new
[`receiver_code_cost.rs`](../../crates/holonic-engine/examples/receiver_code_cost.rs)
instantiates a two-state channel, retaining two distinct B→B edges. Its costs define the
admitted channel; probabilities are derived from h_A=1, h_B=2 and C=1.

| Edge | Cost units | Q | Ideal information bits | Boundary bits |
|---|---:|---|---:|---:|
| A→A | 1 | 1/2 | 1 | 0 |
| A→B | 2 | 1/2 | 1 | −1 |
| B→A | 1 | 1/4 | 2 | +1 |
| B→B, short | 1 | 1/2 | 1 | 0 |
| B→B, long | 2 | 1/4 | 2 | 0 |

The transfer matrix is `[[1/2,1/4],[1/2,3/4]]`, with eigenvalues `1` and `1/4` and
positive eigenvector `(1,2)` at eigenvalue one. The executable checks both characteristic
roots and this eigenvector relation. The stationary population is `(1/3,2/3)`, derived from the transition flows. Entropy and
expected cost are both `4/3` per step. From A alone the one-step readings are 1 bit and `3/2`
cost units, with boundary expectation `−1/2`; from B they are `3/2`, `5/4` and `1/4`.
Ignoring the endpoint potential would falsely report a failed rate law.

[established-bounded; implemented-exact] All 143 histories from either state through lengths
zero to four satisfy product-probability surprise, additive cost and boundary balance.
Rescaling the cost ruler by `3/2` and capacity by `2/3` preserves every code reading.
The exact return is retained [here](2026-09-11_zeta_information_receipts/receiver-code-cost.json.gz).
This is exterior rational apparatus, not a calibrated physical channel or native HNN model.

## Physical clocks, jets and cosmological inference

[definition] Receiver-relative cost can become physical only through the supplied carrier law.
Proper duration along an admitted timelike path, spatial extent in a receiver's slice, energy
flux and angular transport have their own units and source maps. Positive coding cost is not
identical to a Lorentzian metric norm: a null trajectory has zero proper time but can transport
a signal. The real variable being optimized must remain named.

[proved-standard] GR couples its metric to stress–energy through
`G_{μν}+Λ_cos g_{μν}=(8πG/c⁴)T_{μν}`. The usual constant-Λ, conserved-matter chart combines
the contracted Bianchi identity with `∇_μT^{μν}=0`. If Λ is promoted to a field, its gradient
must enter an additional dynamical/source account; coordinate transport alone cannot do that.
[Einstein equations and their physical interpretation](https://www.damtp.cam.ac.uk/user/tong/gr/grhtml/S4.html)
provide this particular physical instance, rather than a proof that coding capacity is mass,
energy or cosmological curvature.

[established-bounded; source-inspected] The repository already carries the more specific
receivers needed here. `ReceiverStressEnergy` retains observer-dependent stress contractions
and angular-current cancellation. `HolonicPantographicSwingJets` retains addressed derivative
orders: acceleration, jerk, snap, crackle and pop correspond to position derivatives of orders
2–6; its force derivatives are separately typed. In a curved chart use the supplied covariant
transport, and under a non-affine clock change retain the chain-rule terms. For a constant
clock scaling `τ=a t`, the nth derivative scales by `a^-n`; nonconstant reparametrization does
not obey that simplified law.

[proved-derived; source-inspected] `HolonicCosmologicalInference` already gives
`Λ_cos=3 Ω_Λ H₀²/c²` in its constant-Λ expansion chart, including the nonlinear preimage fibre
and its inverse-area dimension. It proves that H₀→aH₀ and Ω_Λ→Ω_Λ/a² preserve this face.
Thus equal local inferred constants need not identify equal underlying parameter occurrences.
A locally constant approximation can be useful while its derivative/remainder remains bounded;
this is a precise way to study ecological regularity without silently changing a physical law.

## What reaches the hard problems

[open] For ξ, a useful next bridge would turn a cheaper generator representation into a
**source-specific zero-exclusion certificate**: uniformly control the full heat-flow function,
its analytic remainder and the separation needed by a zero/strip criterion at the original
clock. A local phase code or finite entropy bound does not yet provide that control. The prior
quadratic heat control proves generic strip data alone cannot force the proposed time descent.
`ThresholdRefinement.squareClosed_iff_RH` locates the missing implication on the actual seam set.
The repository's checked bound remains `0≤Λ_DN≤1/8`; no change of code units tightens it.

[proved-standard] Improved rigorous analytic computation has already contributed to stronger
external bounds, as in [Platt–Trudgian](https://arxiv.org/abs/2004.09765). This supports pursuing
better representations and certificate algorithms. It does not identify Λ_DN with Λ_cos or
with the channel capacity C. Each has a different source and clock/dimension map.

[open] For P versus NP, the existing `PVersusNPCausalLengthBridge` anchors boundary length to
fixed encodings and passage length to an actual finite machine's executed steps. A uniform
polynomial upper bound then transports to the literal complexity statement. A lower bound for
one representation or channel does not cover every algorithm. A compact generator can also
execute exponential search. The useful challenge is to exhibit either a uniform algorithmic
construction or an invariant lower bound over the required complete algorithm family.

[definition] This return refines the ongoing operator/receiver work: admissibility, cost,
retained boundary potential and residual now travel together. It does not schedule five new
endpoint campaigns or make their solutions prerequisites to useful Hephaestus applications.

## Verification

[definition] The exterior control is reproduced by
`cargo run -p holonic-engine --example receiver_code_cost --no-default-features -- OUTPUT.json`.

[established-bounded; process-audit] The final exterior control completed with all assertions,
including 143 histories, transfer eigenstructure and the transported clock. The focused Lean
owner check and `lake build ElementaryHolonics.Framework.Information` passed. The latter
includes the new import and the final theorem signatures. No native model or GPU operation
changed.
