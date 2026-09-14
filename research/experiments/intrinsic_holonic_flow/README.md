# One field: linked tori, nonlinear phase attention and recursive arrival geometry

[project-postulate] This construction answers Brandon's September 14 correction: interlinked
and intersecting Holonic structures, attention and recursive geometry belong to the same
object. The earlier tiled IFS and separated layer-column picture do not supply that ontology.
This is a supplied analytic constitutive example used to explain the design. It is evaluated
numerically outside native HNN and does not reproduce a trained model from the cited paper.

[project-postulate] The subsequent exact-mode/receiver correction governs this directory.
`model_constraints.json` retains exact rational parameters, units, integer chart addresses
and the normalized exponential/rotation constraints. `exact/` executes the actual map with
rational enclosures: the first selected state's arrival is certified at 9; the second excludes
arrival through 32 and retains an undecided receiver family at 33. Earlier NumPy output below
is historical exploratory evidence, not an exact Holonic mode or native arrival verdict.
`flow.py` now requires an explicit exploratory-survey flag for that legacy calculation;
its imported numeric functions serve only the exterior display/diagnostic boundary.

## Carrier and common cells

[definition] Six radius-2 toroidal cores form a branched chain, with centers and axes in
`receipt.json`. Five neighboring pairs are linked once: the adjacent perpendicular core
crosses the other's spanning disk at exactly one interior point; its other plane crossing
lies outside the disk. `mesh.json` retains those points and squared-radius comparisons.
The core's displayed tube radius is 13/50. The field domain has minor radius 1 and is defined
by the torus quartic, not by a decorative outline.

[established-bounded; computational-witness] Integer, denominator-cleared quartics on a
quarter-unit lattice produce the shared-support witnesses and hence the admitted coupling
incidence. Surface triangulations close with Euler characteristic zero. The common inscribed
volume complex has 8,317 vertices and 31,440 tetrahedra, of which 240 have multiple domain
owners. Neighboring cells share actual vertex/face identities. Boundary-of-boundary cancels
on the oriented simplex generator. The displayed local patch contains 1,204 tetrahedra.

[proved-derived] Each inscribed cube is contained in every recorded domain. Its center is
inside the same torus with minor radius `1-3/8`; every point of the quarter-unit cube is
within Euclidean distance at most `3/8` of the center. Distance to the radius-2 core circle
is 1-Lipschitz. This proves containment in the radius-1 field tube. The finite subcomplex
is an interior approximation, not a claim that it exhausts every continuous boundary point.
`mesh.npz` retains the actual vertices, tetrahedra and owners. No dimension follows from
camera position or the size of the drawn cells.

[proved-derived] A common material advection carries every core, field domain and volume
cell. For `χ=1/8` the flow is
`F_t(x,y,z)=(x,y cos(χxt)-z sin(χxt),y sin(χxt)+z cos(χxt))`.
Its velocity is `u=(0,-χxz,χxy)`, with zero divergence and Laplacian. At unit nondimensional
density, pressure `χ²x²(y²+z²)/2` and force `(χ²x(y²+z²),0,0)` satisfy the stationary forced
Euler/NS equation on the declared local region. `det DF_t=1` and `F_-t` is its inverse.
The mapped cells remain contained in `F_t(domain_i)` and retain their linking/incidence.
The render draws their curved edge images; `mesh.npz` includes material and advected vertices.

[definition] The carrier is shown at material time 1. The red/blue trajectories carry the
first fourteen phase iterations through material time 0→1, keeping those clocks explicit.
Their derivative includes both material advection and the pushed-forward internal phase
motion. The arrival plots use the material phase coordinates; advection transports the detector
and charts with the body, so it does not change those intrinsic arrival populations.

## One coupled nonlinear operation

[definition] The reference's unit-phase restriction has `q,p ∈ T^6`, hence twelve phase
coordinates. The general field also allows amplitude, material and incidence change; these
are not universally restricted to twelve axes. The two heads have `β=1,4`, share the
geometrically established incidence, and use its antisymmetric phase connection `φ`:

```text
s^h_ij = β_h cos(2π(q_i-q_j-φ_ij)),       a^h = softmax(s^h),
g_i = sigmoid(-cos(2πq_i)),
V(q) = κ/(2π) Σ_i softplus(-cos(2πq_i))
       -κγ/(2πH) Σ_h β_h^-1 Σ_i log Σ_(j∈E_i) exp(s^h_ij),
∂_i V = κ[g_i sin(2πq_i)
           +γ/H Σ_(h,j) (a^h_ij+a^h_ji) sin(2π(q_i-q_j-φ_ij))],
q' = q+κ sin(2πp),                     p' = p-∇V(q')       (mod 1).
```

[definition] `κ=27/100`, `γ=7/20`; self-comparison is included. The two shear stages are
complementary current operations on the **same** state. Heads are normalized comparisons
inside the potential. The inbound and outbound terms both contribute to its gradient.
The trajectory renderer follows the exact analytic subflow formulas between sampled steps,
then maps each torus's two phases through its geometric chart. It does not draw straight
connections between arbitrarily placed layer planes. Both trajectories use the same law.

[proved-derived] Each substep is a Hamiltonian shear, so their real-analytic composition is
symplectic and preserves canonical phase volume. This does not assert exact conservation of
one unsplit Hamiltonian or uniform attraction to a fixed point. Its explicit inverse reverses
the two substeps. The separate local friction figure evaluates the established complex-current
contact at the actual 2↔5 branch. It releases radial amplitude and heat beyond the conservative
unit-phase restriction; the full HNN constitutive field has those additional roles.

## Recursive geometry and numerical scope

[definition] The detector is `q₀∈[1/5,17/50), p₀∈[2/25,1/5)`. A 192×192 family varies
these two **initial** phases while fixing the other ten as recorded in `flow.py`. Each initial
condition follows the complete twelve-phase recurrence. Colors record first reception through
iteration 96; gray retains non-arrival within that window. The two zooms independently evolve
their smaller initial-condition families. They are not rescaled bitmap copies or new physical
objects placed in tiles. `arrival.npz` retains every sampled arrival time.

[proved-derived; formal-checked] For any recurrence Φ and receiver region A,
`A₀=A`, `A_(n+1)=Φ^-1(A_n)\A` are exactly the first-arrival populations.
`HolonicRecurrentEcology.FirstArrival` proves the characterization and covariance under a
state equivalence with conjugated recurrence and transported receiver. The preimages are
full compatible populations; their definition does not require an event archive.

[historical; computational-witness] The earlier floating survey reports that the selected neighboring grid cells first
arrive at steps 9 and 96. Selection is made **after** evolution among adjacent cells whose
first arrivals are both later than 8 and within the window; this avoids presenting the
initial detector edge or a censored outcome as a long-route contrast. The coarse, first-zoom
and second-zoom arrival fractions are respectively 0.6196831597, 0.8907877604 and 0.9420030382.
The changing participation matrices and all plotted flow traces use this same selected state.

[historical; computational-witness] The exploratory numerical checks compare the analytic
potential gradient with central finite differences, the full twelve-axis Jacobian with the
canonical symplectic form, and the composed map with its inverse. Maximum errors were
`3.84e-11`, `1.59e-10`, and `2.22e-16`; the Jacobian determinant was `1.0000000000653`.
These floating-point comparisons corroborate the implementation at the sampled states.
They are not interval-certified long-time trajectories. The three arrival fields took about
29.6 seconds in the recorded run, excluding plotting and mesh generation.

[definition] The pictures expose finite multiscale first-arrival structure. They do not prove
an infinite-scale fractal dimension for this particular analytic map. The supplied
[latent-reasoning paper](https://arxiv.org/html/2609.04963v1) uses trained recurrent models,
initial-condition sections and decoded settling. Its figure motivated the correct kind of
question; its results are not transplanted onto this reference. The former globally contractive
linear control cannot supply the saddle-mediated dynamics under discussion.

## Reproduce and reuse

```bash
cargo run --manifest-path research/experiments/intrinsic_holonic_flow/exact/Cargo.toml --quiet
python3 research/experiments/intrinsic_holonic_flow/render.py
typst compile --root . \
  research/papers/source/papers/elementary-holon-generation/main.typ \
  research/papers/rendered/elementary-holon-generation.pdf
```

[definition] NumPy and Matplotlib serve this exterior numerical/visual construction. The
maintained model formula supplies the general operator contract; the phase chart, common
cell geometry and first-arrival law connect existing analytic-field, graded/simplicial,
connection, normalized-current and recurrent owners. Native implementation must preserve
those relations through its actual field/body consumer. No fixture learner, benchmark gate
or new native subsystem is introduced by these figures.
