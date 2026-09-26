# Analytic flux, evolving sources and receiving basins

[project-postulate] Brandon's September 14 correction makes the underlying construction the
deliverable. Recursive geometry belongs to the generating operation, its admissible preimages
and receiving populations. A diagram reads this object; arranging torus pictures or animating
a camera does not construct it. This guide binds the [model formula](HNN_FORMULA.md) and
[receiver holarchy](RECEIVER_HOLARCHY.md) to actual analytic sources and reusable library calls.

## The source determines the current and release

[definition] Let `f:D⊂ℂ→ℂ` be holomorphic on the declared source domain. Retain its jet
`(f,f_s,f_ss)`, the complex coordinate, applicable boundary and source remainder. On a
zero-free patch its logarithmic one-form is

```text
L_f=f_s/f,                ω_f=L_f ds,
ω_f=d log|f| + i d arg f.
```

[proved-derived] Write `s=x+iy`, `L_f=a+ib`. The potential and phase covectors are
`d log|f|=a dx−b dy` and `d arg f=b dx+a dy`. Cauchy–Riemann makes both closed and co-closed
away from the divisor in the Euclidean complex chart. They are locally harmonic but need not
be globally exact on a punctured domain: a positively oriented simple boundary measures
`∮ω_f=2πi(Z−P)`, including multiplicity.
Here π is the circle-period constraint; a numerical enclosure is only a receiver face.

[proved-derived; formal-checked] The repository already supplies the actual argument-principle
owners in `Zeta/LocalArgumentPrinciple`, `Zeta/RectangleArgumentPrinciple` and `Zeta/WeightedArgumentPrinciple`.
The last one binds the weighted contour to ξ. `HodgeFiniteDecomposition`, `HodgeGreenOperator`
and `TemporalHodgeResidue` supply the cellular/metric decomposition and its evolution.
The analytic one-form gives a concrete field and circulation population to discretize on
such a complex. Choosing a mesh does not automatically prove its discrete Hodge projection
equals the continuum one; the restriction, metric and quadrature must realize that comparison.

[definition] At `f_s≠0`, solve the tangent equation rather than rank candidate points:

```text
f_s v=−f,
v=−f/f_s=−conj(f_s) f/|f_s|²,
N_(λ,f)(s)=s−λ f/f_s,
N'_(λ,f)=1−λ+λ f f_ss/f_s².
```

[proved-derived; formal-checked] `Mathematics/AnalyticNavigation` proves the derivative of
this actual map, the normalized complex residual direction and the local chain rule
`d f(s(τ))/dτ=−f(s(τ))` along its admitted velocity. Under that law throughout an interval,
the normalized exponential is the residual evolution and its phase is constant until the
domain ends. The formal leaf proves the local derivative, not global existence of that curve.
For `E=|f|²/2` its real gradient is the complex representation `conj(f_s) f`, giving
`dE/dτ=−|f|²`. This is a declared residual law, not a universal definition of HNN attention.

## Source evolution is part of the same equation

[proved-derived] For a changing source `F(u,s)` and declared clock `u(τ)`, the chain rule gives

```text
dF(u(τ),s(τ))/dτ = u_dot F_u + F_s v,
v = (−F−u_dot F_u)/F_s.
```

For the existing backward-heat source `F(u,s)=heatE(u,ξ,s)`, `F_u=−F_ss`, hence
`v=(−F+u_dot F_ss)/F_s`. At a simple zero the same relation gives
`v=u_dot F_ss/F_s`: the existing RH zero motion. Off the zero it releases the residual while
accounting for the source deformation. The source deformation parameter u, refinement clock τ
and a physical receiver's proper time are distinct until a map between them is supplied.

[definition] The release clock above is normalized. A physical time with dimensional units
uses a declared rate κ and residual equation `F_s v=−κF−u_dot F_u`; setting κ to one is a
choice of time unit, not an intrinsic physical rate.

[proved-derived; formal-checked] `Zeta/ZeroDynamicsEntire` now proves
`hasDerivAt_heatE_comp_residual_guided` and its actual ξ specialization from the existing
heat-flow chain theorem, with the same growth and differentiable-curve hypotheses and a
nonzero source derivative. This joins the source evolution to residual refinement directly.
`FosterClassHeatFlow` already identifies the zero-motion term with its regularized divisor
flux. There is no new universal convergence assumption.

[established-bounded; implemented-exact] `ComplexJet2::residual_velocity_with_source_rate`
solves `f_s v+source_rate=−f` over complete complex rational enclosures. A backward-heat
caller supplies `source_rate=−u_dot*f_ss`; it must supply the actual current source jet too.
The prototype ζ basin application below used a fixed ζ source. It does not mislabel its
static jet as a finite-time evaluation of `heatE(u,ξ)`.

## Recursive geometry is the complete preimage relation

[proved-derived; formal-checked] With `f_s(s)≠0`, a release reaches y exactly when

```text
f_s(s)(y−s)+λ f(s)=0.
```

`Mathematics/AnalyticReceiving` binds this equation to the existing computational `Holon`
and first-arrival owners. Points outside the declared analytic domain or at a rejected
derivative cut enter an explicit absorbing obstruction; Lean's total division cannot silently
turn them into successful continuations. The original domain may have a removable extension,
but that extension needs its actual source formula.

[definition] For an invariant receiving neighborhood U of a root,
`B(U)=⋃_(n≥0) N^(-n)(U)` is its captured population. First arrivals separate the depths:
`A_0=U`, `A_(n+1)=N^(-1)(A_n)\U`. All admissible branches participate. A branch is a solution
of the retained preimage equation; it is not a copied image, arbitrary scale factor or chosen
inverse. The finite receiver can return a certified subregion of B(U) while retaining the
unresolved population. Lack of capture within a finite horizon does not identify a Julia set.

[proved-derived] On an unbranched local inverse g of N,
`g'(y)=1/N'(g(y))`. A composed inverse branch therefore carries the product of these complex
derivatives: both its scale and orientation come from the same source. For a density ρ with
the necessary change-of-variables hypotheses, its planar transfer is
`(Pρ)(y)=Σ_(N(s)=y) ρ(s)/|N'(s)|²`, counting every applicable branch and boundary flux.
The Jacobian carries the density; the complex derivative still carries the angle lost by its
magnitude. Critical values require a singular/branched treatment, not division by a plotted zero.

[definition] Fractal dimension asks about these repeated preimages or invariant/survivor sets
at changing resolution. A bounded experiment can measure basin uncertainty and branch stretch;
dimension or pressure limits require their convergence and separation hypotheses. There is no
general equality between box dimension, entropy, effective rank and a displayed plane's dimension.
The [Newton dynamics literature](https://arxiv.org/abs/1501.05488) supplies global theorems for
specified entire sources; its hypotheses are not automatically met by a meromorphic ζ chart.
[Virtual immediate basins](https://arxiv.org/abs/math/0505652) also distinguish escape to infinity
from capture by a root. These are reasons to retain the actual dynamics and obstructions.

## A receiver changes the relative evolution

[proved-derived; formal-checked] Let `e_n` be a changing equivalence of state charts. The actual
relative recurrence is `T^R_n=e_(n+1) ∘ T_n ∘ e_n^(-1)`, with receiver `U^R_n=e_n(U_n)`.
`AnalyticReceiving` proves the clocked evolution and first-arrival correspondence using the
existing `ClockedFirstArrival`. Merely rotating the endpoint while iterating the old map would
omit the relative-frame change.

[proved-derived] In a differentiable affine complex chart `w=a(τ)s+b(τ)`, `a≠0`,
`w_dot=a v+a_dot s+b_dot`. The phase of a represents orientation and its modulus represents
dilation. In the discrete case `(N^R_n)'=a_(n+1) N'_n/a_n`. The logarithmic stretch therefore
retains both intrinsic stretching and the receiver's changing scale. For a fixed affine chart
and constant nonzero value scale c, pulling back f transports its jets by `f→cf`,
`f_s→c f_s/a`, `f_ss→c f_ss/a²` and conjugates the release map. An arbitrary nonlinear
coordinate change needs the full conjugated generator; bare Newton recalculated in that chart
is not automatically the same operation. A physical change in receiver coupling is also not
merely a coordinate equivalence.

## Exact executable receiving regions

[definition] The retired [`geometry::exact_analysis`](https://github.com/brandonrdug/holonics/blob/551d6c5d/crates/holonics/src/geometry/exact_analysis.rs) exported `ComplexJet2`,
`certify_capture`, `mean_value_release` and `propagate_to_capture`. A supplied callback must
enclose the same holomorphic source and its first two derivatives throughout every requested
box, including its analytic remainder. Capture certificates apply only to that source/law.

[proved-derived] For a convex square `B∞(m,r)`, let q bound
`|Re N'|+|Im N'|` throughout the square and let β bound `|N(m)−m|∞`.
If `q<1` and `β+qr<r`, N is a strict self-map and contraction. Its unique fixed point is a
source zero when λ≠0 and the derivative is nonzero throughout. These are sufficient local
receiving neighborhoods; no global contractive model is imposed.

[established-bounded; implemented-exact] The implementation uses exact rational interval
inequalities and retains those bounds. Propagation uses
`N(X)⊆N(m)+N'(X)(X−m)` on each convex source box. The midpoint m is an explicit proof anchor;
the full displacement family and derivative enclosure remain in the result. Directly evaluating
`X−f(X)/f_s(X)` can lose correlated cancellation and swell even near an attracting root.
Capture, domain obstruction and horizon exhaustion all return the current family.

[definition] A propagation step count is the first certified inclusion of the complete
enclosure in one supplied neighborhood. It bounds each member's arrival time; it does not
prove that every member first arrives at that same step. Exact first-arrival populations
require the earlier exclusions present in the formal preimage relation. Root receiving
regions use `Option.some '' U`, excluding the absorbing obstruction from successful capture.

[definition] The prototype's
[`analytic_receiving_basins`](https://github.com/brandonrdug/holonics/blob/13f8c734/research/experiments/analytic_receiving_basins/README.md)
consumed Euler–Maclaurin ζ jets. It discovered receiving centers from supplied rational initial
regions, certified their neighborhoods, transported other complete initial regions to them, and
independently computed η boundary winding around each accepted neighborhood. In `0<Re s<1`,
`η=(1−2^(1−s))ζ` and the factor is nonzero because `|2^(1−s)|>1`; it contributes zero contour
winding there. The nonzero ξ completion factor likewise preserves the divisor in this strip.
Their logarithmic currents differ by the logarithmic derivative of those factors, so this is
a ζ traversal with a shared zero-count receiver, not a ξ or η traversal renamed after the fact.

[definition] The application was exact CPU mathematical apparatus over the shared library, with
no float-driven semantic decision and no live Lean dependency; it was not a GPU lowering of
general analytic source evaluation. The [dated return](../research/records/2026-09-14_ANALYTIC_RELEASE_AND_RECURSIVE_RECEIVING_POPULATIONS.md)
records the actual regions, source config, elapsed costs, checks and remaining scope.
