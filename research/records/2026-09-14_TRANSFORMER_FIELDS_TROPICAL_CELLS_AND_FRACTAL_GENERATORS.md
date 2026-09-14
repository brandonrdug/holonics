# Transformer fields, tropical cells and fractal generators

[project-postulate] Brandon supplied four papers while correcting the Holon/generation
specification. The purpose is a high-level computational algebra and model design, including
fractal recursion, dimensionality and transcendental operations. These analyses extend the
existing programme; they do not replace Athena construction with another benchmark campaign.

## 1. Liang: field operators and their differentials

[established-bounded; source-inspected] [The Geometry of Semantic Space](https://arxiv.org/html/2607.17146v1)
represents hidden states as sections, attention as a state-dependent nonlocal integral,
RoPE as fixed torus transport and FFN as local reaction. Equations 9–10 differentiate both
transported values and attention weights. Equations 52–53 identify rotational Jacobian terms;
Eq. 59 separates parameter drift, self-advection and the interaction bracket in a small-step
expansion. This is useful operator-level architecture. Its fixed sequence base and positional
connection do not provide HNN's changing incidence. The reported model interventions are
empirical evidence at their tested configurations, not proofs of every geometric claim.

[interpretation; source-inspected] Theorem 5 incorrectly infers a continuous extension at
infinity merely from a bounded continuous value field. Its logarithmic mass-allocation
identity remains valid, but does not by itself prove a necessary first-token attention sink.
Remark 5 qualifies the step-one expansion; an exact modified ODE embedding is not automatic
for arbitrary discrete nonlinear maps. These boundaries sharpen the useful construction.

[proved-derived] The extension error has a concrete separator: `V(x)=cos(πx)` is bounded and
continuous on the half-line, but its even/odd integer subsequences approach 1 and -1. It has
no single value at the point added by one-point compactification. For a periodic/quasiperiodic
source, retain its actual phase on a circle/torus and its envelope. That is an existing Holonic
phase-generator representation, not a reason to store all positions or collapse the oscillation.

[definition] In comparing RMS conventions, the paper's
`sqrt(d)x/sqrt(||x||²+epsilon_paper)` matches ordinary
`x/sqrt(||x||²/d+epsilon_RMS)` with `epsilon_paper=d epsilon_RMS`; learned gains must also
travel through the derivative. A named normalizer does not eliminate these parameter maps.

## 2. Su and Liu: tropical routing geometry

[established-bounded; source-inspected] [Geometric Capacity of Transformers](https://arxiv.org/html/2604.14727v2)
analyzes fixed-key query-space attention, its zero-temperature routing cells, and multihead
common refinement through Minkowski sums of Newton polytopes. Its region-count results use a
conditioned, normalization-free tropical skeleton, with noncollapse and width hypotheses.
They are not unrestricted counts for a full trained Transformer. The auxiliary log-lifted
value family also differs from ordinary fixed signed values. There is no empirical trained-model
experiment establishing attainment of those bounds.

[established-bounded; source-inspected] Theorem VI.1 retains exact top-1 ordering at positive
temperature and gives exponentially small output/derivative defects away from tie boundaries.
The finite-temperature vector field stays smooth; Corollary IV.4's piecewise-constant wording
belongs to the zero-temperature limit. In full self-attention, keys also change with the input,
so the fixed-key polyhedral partition is not a fixed partition of all sequence tensors.

[definition] The useful HNN consequence is an approximation chart, not a native argmax law.
For scores separated by delta, temperature tau and fixed values, the nonwinning contribution
is bounded by its value spread times `(N-1) exp(-delta/tau)`. Keep the vector combination and
its oriented defect. Near a tie, resolve the participating modes rather than promote a cell
label into identity. Different constitutive maps and source families require their own bounds.

## 3. Tai, Liu, Li and Chan: a complete operator composition

[established-bounded; source-inspected] [A Mathematical Explanation of Transformers](https://arxiv.org/pdf/2510.03989)
organizes attention, normalization and feedforward reaction as split evolution of a field over
position and feature domains. Its convolutional extension and optimal-control viewpoint make
the model itself a composition of mathematical operators, rather than a collection of lifecycle
interfaces. Alternative integrators are architecture choices with their own error/stability
properties. Well-posedness and regularity are identified as further analytical work in the paper.

[established-bounded; source-inspected] The September 12
[earlier derivation](2026-09-12_FRACTAL_MODES_LIFT_ATTENTION_INTO_MASS_PRESERVING_GENERATOR_COMPRESSION.md)
already checked the projection-sign correction, nonconvex normalization sphere, gain/epsilon
scope and exact attention summaries. Those proofs and library implementations remain usable.
This analysis recovers their role in the complete operator composition rather than rerunning
them or treating every printed geometric interpretation as a completed native implementation.

## 4. Lai, Bao, Quinn and Gilpin: recursive dynamics and fractal basins

[established-bounded; source-inspected] [Fractal basins trap latent reasoning](https://arxiv.org/html/2609.04963v1)
studies fixed-model, fixed-task latent iteration, varying initial conditions on two-dimensional
slices. It reports complex settling-time boundaries, saddle-associated delays and changes
during training. Appendix B uses finite grids, iteration caps and exclusions; its uncertainty
exponent estimates basin-boundary dimension in those slices. Basin entropy, that dimension,
latent dimension and a finite-time separation indicator are different measurements.

[interpretation; source-inspected] The findings support investigating recursive flow and its
representation. They do not prove that every solver must suffer those delays. Their finite-field
linear-system experiment admits direct Gaussian elimination; the text's description of typical
algorithms as testing integer sequences is not that algorithm. The measured geometry is partly
a property of the learned map and initialization. A decoded answer remaining unchanged also
does not alone prove that the complete latent state reached a fixed point.

## 5. The common Holonic operator construction

[definition] Use the tensor field ket |Psi⟩ on the actual contact complex. A normalized
attention specialization is

```text
|T[Psi]⟩_mu = Σ_nu a_mu,nu[Psi] |z_mu,nu[Psi]⟩,
z_mu,nu = V_mu←nu Psi_nu,
delta T_mu = Σ_nu a_mu,nu delta z_mu,nu + Σ_nu delta a_mu,nu z_mu,nu.
```

The two terms are variation of transported current and variation of its participation.
For a softmax chart, `delta a_i=a_i(delta s_i-Σ_j a_j delta s_j)`; their combination is
an explicit covariance term. This is the same kind of mixed change as varying incidence,
material and current together in the HNN field. A scalar score alone is not the interaction.

[definition] The local reaction R, transport T, normalization/projection N and boundary
operator act on that field. Their actual discrete composition is the model. For smooth
autonomous vector fields, an explicit T step followed by an explicit R step has second-order
term `DR[T]`; the combined exact flow additionally has
`(DT[T]+DT[R]+DR[T]+DR[R])/2`. Nonautonomous material contributes its time derivatives.
The bracket is an important part of this difference, not the complete truncation error.
This gives an operator library a precise composition and differentiation contract.

[definition] For repeated generation `x_(n+1)=F_Theta(x_n,h)`, keep the map and the current
state. Its tangent obeys `J_(n+1)=DF_Theta(x_n,h) J_n`. This is a recurrence for sensitivity,
not a command to retain the trajectory. A basin boundary may require refinement of a family
or a different generator factorization; a finite-time norm or entropy reading is a measurement
under a declared objective, not intrinsic identity or a universal stopping threshold.

## 6. Fractals and transcendental constraints in the algebra

[definition] A recursive geometric generator acts by an operator on objects, for example
`S(H)=union_i F_i(H)` with attractor `H=S(H)` under its contraction hypotheses. Similarities
of ratios r_i satisfying the open-set/separation condition have similarity dimension D
given by `Σ_i r_i^D=1`. Without those hypotheses, that equation is not automatically the
Hausdorff dimension. Finite measured basin dimensions and tensor rank are different quantities.
The classical source is [Hutchinson, §§3 and 5](https://maths-people.anu.edu.au/~john/Assets/Research%20Papers/fractals_self-similarity.pdf).

[proved-standard] For the four maps `F_ij(u,v)=((u+2i)/3,(v+2j)/3)`, i,j in {0,1}, the
Cantor-dust similarity equation is `4·3^(-D)=1`, hence `D=log(4)/log(3)`. Four rational maps
and a depth describe the finite family; listing all level-n cells requires `4^n` cells.
Identifying a particular separated cell still requires its branch/address information.
The synopsis renders these maps directly. This is a geometric construction, not a newly
measured neural basin dimension.

[definition] Exponential, logarithm, trigonometric and Gamma operations are functional
constructions with domains and identities. `exp(tA)` conducts a linear field; a nilpotent A
can make its series terminate. `exp(i theta)` transports phase on a circle, with 2π the period.
Logarithms convert scale ratios to additive lengths and dimension equations. Gamma's recurrence
and retained analytic remainder support the existing block generators. These functions do not
enter merely as floating-point constants. Their native realization uses the corresponding
exact expression, recurrence or enclosed analytic operation with its declared decoder.

[project-postulate] Fractal scale/refinement, source phase and analytic remainders belong in
the high-level Holon operation and its compiler representation. Do not substitute a fixed
embedding dimension, a token count, a scalar routing label or a past-state archive for them.
Use the existing `FractalPacking`, phase/clock, generator-factorization and analytic owners;
the model construction remains the joined field operation in the roadmap.

## 7. Additional primary sources and integration

[established-bounded; source-inspected] Two further relevant sources were located and opened:
[Geshkovski et al.](https://arxiv.org/html/2312.10794v5) treats attention as interacting
particles and studies clustering under stated dynamics; [Barboni et al.](https://arxiv.org/html/2605.17660v1)
develops coupled data/parameter measure dynamics and adjoint training in a mean-field limit.
Their assumptions remain attached; the latter's convergence claim includes NTK injectivity
and a small-initial-loss condition. They are productive comparative sources, not new
prerequisites or evidence that the finite native model has those limit properties.

[definition] This return updates `docs/HOLON.md`, the HNN formula and the existing model
assembly contract with complete operator variation, recursive generators, scale and analytic
operations. The geometric synopsis keeps the Information Chemistry presentation and adds
fractal/functional-calculus plates. It does not create another engine, a new fixture-local
learner or a universal complexity gate. The earlier general Holon/tensor proofs remain the
verified formal foundation; no new paper experiment is represented as a native measurement.

[established-bounded; source-inspected] The tropical paper was also examined by a bounded
Luna reader. Root inspected its core routing, model restrictions and finite-temperature
statements before integrating the report. Liang's theory/limits and the fractal paper's
methods were read directly. Private text extractions retain equation numbers for navigation;
raw paper text is not added to the repository.

[established-bounded; process-audit] The resulting ten-page geometric synopsis compiled with
Typst; every final page was rendered with Poppler and visually inspected. The existing Holon
and Core builds remain the verified formal return of this task. The new paper synthesis is
source analysis and displayed algebra, not a claim that the papers' experiments were rerun
or their general conclusions mechanically verified. Final `git diff --check` passed.
