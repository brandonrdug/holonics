# Generator inference: codes, free energy and sufficient continuation

[project-postulate] Brandon asks for the mathematical bridges between solving, learning,
Information Theory and generator compression. The September 12 semantic correction is not
completed by labeling them all intelligence: the shared relations must be derived and used.
This return composes existing formal owners and extends the existing exact code-cost application.

## Recover the common object before dividing its applications

[definition] Let a candidate g be an executable representation with its source/domain,
parameters, receiver and required future scope. It can be a factor circuit, an indexed recurrence,
a fixed-architecture parameter vector, or a dependent pair `(architecture, parameters)`.
`DependentMachineLearningCarrier.TotalState` already gives the sigma-type presentation for
changing carriers; `GeneratorFactorization` already certifies complete bilinear and block actions.
Supplied source constraints define a solution/preimage fibre in this candidate population.

[definition] A statistical receiver additionally supplies a likelihood, reference measure and
description code. In its finite positive chart, with shared decoder/standing B, write

`J_D(g) = L(g | B) + L_R(D | g,B)`,

where `L_R = -log₂ likelihood` when that receiver is admitted. For an exact solver, first
restrict to the actual feasible generator fibre and compare its descriptions or other declared
costs. Empty fibres remain obstructions. The statistical chart imposes no artificial probability
on an arbitrary source fibre and is not a mandatory native routing mechanism.

[proved-standard] Two-part MDL and Bayesian model comparison already connect description length
with likelihood; parameter estimation and model selection are studied together in
[Grünwald–Roos, §§2–2.4](https://arxiv.org/html/1908.08484). The following formal return recovers that
connection through Holonics' existing normalized receiver and then joins its cost, quotient and
continuation laws. It does not claim to have invented the MDL/Bayes correspondence.

## 1. Exact solving, MAP and variational inference

[definition] On a finite nonempty admitted candidate type, define the complete receiver

`Π_D(g) = 2^(-J_D(g)) / Z_D`,    `Z_D = Σ_g 2^(-J_D(g))`.

`Foundation/GeneratorInference.posterior` uses the existing `NormalizedExponential.face` with
potential `-(ln 2) J_D`. `posterior_of_log_description_and_likelihood` derives the normalized
prior-times-likelihood expression. Positive unnormalized code weights are permitted; their
normalization is included in Z. Data independence is not an assumption of this theorem: the
likelihood supplied for the complete D carries its actual conditional structure.

[proved-derived; formal-checked] `minimizer_iff_posterior_mode` proves

`argmin_g J_D(g) = argmax_g Π_D(g)`

as a pointwise equivalence of the full minimizing/maximizing predicates, without choosing a
winner. `exact_solver_iff_posterior_mode` specializes it to an actual feasible subtype. Thus
minimum-description exact synthesis and MAP are two receivers of one admitted optimization
problem. The theorem assumes neither a globally optimal search procedure nor an unrestricted
program population.

[proved-derived; formal-checked] Define the variational functional in bits by

`F_D(q) = E_q[J_D] - H₂(q)`.

The new `variational_gap_eq_kl_bits` composes the existing
`Physics.InformationDifference.freeEnergy_difference_eq_thermalScale_mul_kl` at thermal scale
`1/ln 2` to prove

`F_D(q) - F_D(Π_D) = D_KL,₂(q || Π_D) ≥ 0`.

`InformationReceiver.klDivergence_nonnegative` supplies Gibbs' inequality on the common positive
support; `variational_minimum` gives the resulting minimum. This is the precise variational
bridge among probabilistic inference, code objectives and free energy. A physical realization
still supplies its carrier energy, temperature, units and constitutive map; the algebra does not
assign those physical quantities to an arbitrary program length.

## 2. Gauge, sufficient statistics and memory

[proved-derived; formal-checked] The existing softmax common-shift law now has its converse:
`NormalizedExponential.face_eq_iff_pairwise_differences` and
`GeneratorInference.posterior_eq_iff_objective_differences` prove

`Π_J = Π_K  ↔  ∀ g,h, J(g)-J(h) = K(g)-K(h)`.

The normalized inference receiver retains exactly these pairwise differences. A common additive
objective offset is its gauge freedom. Equal scalar entropy is a much coarser relation and does
not satisfy this theorem. The two objective populations use the same candidate type and units.

[proved-derived; formal-checked] Consequently, if a statistic S satisfies

`J_D(g) = j(S(D),g) + a(D)`,

with a(D) independent of g, `sufficient_statistic_posterior` proves that S(D) alone determines
the entire posterior receiver. This is an exact likelihood/objective factorization statement,
not a requirement to reconstruct D. A more general equivalent representation need only preserve
the pairwise objective differences.

[proved-derived; formal-checked] If S also has an admitted closed update,

`S(T_x D) = U_x(S(D))`,

the construction `sufficientHistoryCompression` is an instance of the existing
`ReceiverHistoryCompression`. Its `sufficient_statistic_every_future` theorem transports the
inference receiver through every finite ordered future word. Here statistical sufficiency,
dynamic quotient/conjugacy and persistent inference share an explicit commuting relation.
`CountControl` proves the factorization and closure for additive two-symbol losses: two counts
replace the ordered observation list for that source law. It makes no such claim for a source
whose likelihood or future availability depends on distinctions discarded by those counts.

## 3. Coarse graining candidates carries their complete weight

[proved-derived; formal-checked] Let π map the admitted candidate population onto finite classes.
`posterior_coarse_eq_pushforward` proves the exact noninjective transport law. Its effective
class objective is

`J̄(c) = -log₂ Σ_{g:π(g)=c} 2^(-J(g))`,

and its normalized receiver satisfies

`Π_J̄(c) = Σ_{g:π(g)=c} Π_J(g)`.

This is the log-sum-exp/free-energy cost of the complete fibre. Choosing an arbitrary
representative, taking a plain mean of code lengths, or silently duplicating candidate mass
changes the problem. The candidate prior/code and its pushforward are part of the representation
map. This complements `SituatedInformationRate`'s transported observation-measure law: both
the observed population and the candidate population have measures that must cross their charts.

## 4. Yesterday's addressed code cost enters the same inference

[proved-derived; formal-checked] The retained code-cost balance is

`L(g) = C W(g) + B(g) + r(g)`,

where B is the source-minus-target potential and r is the remaining code-cost defect. The
existing serial theorem composes B through actual holon pullback joins. The new
`code_cost_log_odds` derives, for two admitted generators,

`log₂(Π(g)/Π(h)) = -[C(W(g)-W(h)) + (B(g)-B(h)) + (r(g)-r(h)) + (L_R(D|g)-L_R(D|h))]`.

Thus resource differences, endpoint potential, remainder and data fit participate in the same
comparison. The endpoint/residual terms vanish from inference only when their difference is
actually zero. The normalizing partition cancels; a candidate-dependent physical/code boundary
does not. This is the direct use of the addressed information-cost law, rather than an unrelated
second criterion for whether the solver has learned.

## Exact executable return

[established-bounded; implemented-exact; computational-witness] The existing
`crates/holonic-engine/examples/receiver_code_cost.rs` now also composes
`SymbolicSurprisal::{of_probability,plus,minus,scaled}` and
`RatioFamily::{read,normalised_against}` into the finite inference chart above. Its two supplied
Bernoulli generators have success parameters 1/4 and 3/4, with prefix descriptions `0` and `10`
conditional on their shared decoder. Two failures and one success give objectives
`7−2 log₂ 3` and `8−log₂ 3`; their inferred weights are exactly `(6/7,1/7)`.

[established-bounded; implemented-exact] Direct product likelihoods for two differently ordered
histories agree with the symbolic count-based construction. A common five-bit header leaves
the posterior unchanged. Updating only the two counts with another success returns `(2/3,1/3)`.
Refining description `0` into `00` and `01` returns weights `(3/7,3/7,1/7)`; pushing the first
two back to their common generator recovers `(6/7,1/7)` exactly. The trial distribution `(1/2,1/2)`
has a variational gap equal to its symbolic KL, `log₂ 7−3/2−(log₂ 3)/2`. The minimum functional
equals `8−log₂ 3−log₂ 7`, the negative log partition. All equalities use exact rational/log
owners; no floating-point comparison selects them.

[definition] This is an exterior mathematical application of existing inference/measurement
owners. It introduces no fixture-local optimizer and changes no native update law. Its finite
source and prefix code are declared control inputs. The older 143 complete channel histories,
unequal-cost boundary checks and clock-rescaling comparisons remain in the same application.

## Verification and application boundary

[established-bounded; process-audit] The final
`bash tools/lean_check.sh ElementaryHolonics.Framework.Information` succeeds under
`leanprover/lean4:v4.33.0` with the new import and changed normalization/information owners.
The eight printed central theorem signatures use only the standing `propext`, `Classical.choice`
and `Quot.sound` axioms. Early namespace-alias and algebra-tactic drafts failed and were repaired
before the final build. The [formal terminal](2026-09-12_generator_inference_receipts/formal-terminal.txt)
retains the completion and axiom output; full local output remains under `.local/scratch/`.

[established-bounded; process-audit] The final
`cargo run -p holonic-engine --example receiver_code_cost --no-default-features -- .local/scratch/2026-09-12-generator-inference.json`
builds and completes all assertions. The
[complete exact receipt](2026-09-12_generator_inference_receipts/receiver-code-cost.json) retains
the channel and inference results. The changed example was formatted with Rust 2024 rustfmt;
`git diff --check` passes. Native kernels and source-model conduct were unchanged and their
regressions were not rerun.

[definition] The immediate Hephaestus use is to carry a candidate program/factor family and its
description, decoder, analytic/data receiver and costs through a request. Fixed-architecture
parameter fitting and program synthesis differ in candidate domains, not in whether inference
occurs. A reduced representation of the native dependent programme must establish the relevant
factorization and update square for its actual mathematical task; the finite count example is
not silently substituted for that richer source law. The live roadmap retains the reusable
operator/recurrence construction and now has these proved relations available to guide it.
