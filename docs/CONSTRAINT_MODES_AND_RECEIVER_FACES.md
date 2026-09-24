# Constraint modes, chart transitions and active receiver faces

[project-postulate] Brandon's September 14 correction governs: a named constant is a
constraint-defined mode; a floating approximation is one receiver face. Chart changes must
carry scale, integer degree/count/level, units, orientation and the relevant invariant.
Reception is developed here as participation in the coupled field. Software/ML vocabulary
does not remove the general-relativistic, mechanical or geometric part of the construction.

## A mode and its evaluated face

[definition] Specify a mode by its admissible carrier, defining relation, normalization,
branch/period and generating law. A receiver reads a face of that mode at its declared
frame and grain. A numeral, a truncated series or a function name does not supply that full
contract by itself. Conversely, a formal function name is legitimate shorthand when its
constraint interpretation is supplied; `Real.exp` in Lean is an exact mathematical function,
not a machine float. No symbolic rename is needed to repair a lost source relation.

[definition] The normalized exponential mode E satisfies
`E'=E`, `E(0)=1`, `E(z+w)=E(z)E(w)`. The constant e is specified by its normalized unit-growth constraint `e=E(1)`.
Its complex kernel is `2πi Z`: the constant π is specified by the primitive positive half-turn
constraint in this normalized phase chart, and the integer kernel retains winding. The rotation mode has
`R'=J R`, `R(0)=I`, `J²=-I`, with sine and cosine its paired coordinate faces.
Scaling the generator changes its rate/period together. A unit-conic phase can alternatively
be carried by rational homogeneous data satisfying `c²+s²=1`; no angle mantissa is required.

[proved-derived; formal-checked] The recovered Machin constraint is
`(5+i)^4=(239+i)(2+2i)` and `π=16 atan(1/5)-4 atan(1/239)`.
`MachinPhaseConstraint`, `PhaseCarrier`, `RatioSeriesTransport` and `RadixWindowReceiver`
retain its algebra, branch, navigator state and exact window laws. [`exact_value::CertifiedSeries`](https://github.com/brandonrdug/holonics/blob/551d6c5d/crates/holonics/src/exact_value.rs) carried rational partial sums and oriented remainders, as the prototype's `reopening` did at `13f8c734`.
The [September 11 recovery](../research/records/2026-09-11_PI_AND_E_CONSTRAINT_IDENTITIES_HAVE_ORIENTED_GENERATOR_FACES.md)
connects the August exponential/kernel study to its formal owners and the code of its date.

[definition] Logarithm is the inverse of normalized real exponential transport on the
positive branch, or a complex lifted branch with its winding. A positive rational kernel K
can therefore define its log-potential implicitly by `E(s)=K`. Exact normalized transport
needs K and its row mass; it need not evaluate or store a logarithm. Supplying K does not
claim that a learning procedure inferred its source. Zero-support entries are absent
contacts and are not assigned a finite logarithm.

[definition] Softmax and sigmoid are receiver relations of that normalized mode:
`a_i=E(s_i)/Σ_j E(s_j)`, `σ(s)=E(s)/(1+E(s))`,
`da=(diag(a)-aaᵀ) ds`, `dσ=σ(1-σ) ds`.
Their operand/domain, scale and complete differential travel through the HNN current.
A thermal reading additionally specifies energy, temperature and units; a dimensionless
normalization coefficient is not automatically a physical conductance or stress tensor.

[definition] Euler's Gamma mode obeys `Γ_E(z+1)=z Γ_E(z)`. Its positive-real normalization
`Γ_E(1)=1` and log-convexity select the classical Gamma function; continuation supplies its
meromorphic domain and poles. The shift law gives finite products and noncommuting shift/
coordinate operators even without evaluating one absolute Gamma seed. This is distinct
from Kelvin circulation `Γ_K=∮v·dl`. Riemann, Hurwitz, Dedekind and dynamical zeta constructions
likewise retain their particular coefficient source, product, continuation and receiver.
The [framework synthesis](https://github.com/brandonrdug/holonics/blob/13f8c734/docs/MATHEMATICS_AND_NATIVE_CONDUCT.md#constraint-defined-modes-and-named-de-bruijn-boundaries)
links the actual golden/Gamma/zeta relations, Gaussian rebase and the two separately named de
Bruijn boundaries.

[definition] The golden mode is algebraic: `φ²=φ+1`, `φ>1`. Its reciprocal, fifth-turn
face and Fibonacci residue are parts of the same constrained construction. Its connection
to Euler-Gamma and Dirichlet/dynamical zeta comes through explicit identities, not a shared
decimal. Copson–de Bruijn `c_CD` is a variational/recurrence threshold; de Bruijn–Newman
`Λ_DN` is a heat-flow real-zero threshold. Their lower-boundary pattern is reusable, but
no equality of those constants is asserted. The same [synthesis](https://github.com/brandonrdug/holonics/blob/13f8c734/docs/MATHEMATICS_AND_NATIVE_CONDUCT.md#constraint-defined-modes-and-named-de-bruijn-boundaries)
retains the finite/infinite boundaries, normalized drift and heat-coordinate/time corrections.

[established-bounded; source-inspected] Hypergeometric closure supplies another concrete
connection: rational local turn differences `1-c`, `c-a-b`, `a-b` become integer
residues on a common cyclic chart. Under its irreducibility/domain conditions, Galois-rebased
interlacing decides finite monodromy. The retired
[`hypergeometric_closure.rs`](https://github.com/brandonrdug/holonics/blob/814157ad/crates/holonic-engine/src/hypergeometric_closure.rs)
performed those exact integer operations instead of evaluating transcendental angles, joining
constraint-defined analytic solutions, phase, group transport and algebraic closure.
It does not identify every finite reflection group or rational local descriptor with one
universal global geometry.

## Typed transitions, levels and units

[definition] Write `C_F : H → H_F`, `g_(G←F) : H_F → H_G`. An invertible change of
representation has its inverse and commuting overlap relations. A projection or quotient
instead retains its fibre, decoder and scoped residual. A lossy cast is not an invertible
chart change. A float codeword can be decoded exactly to a dyadic rational; quantizing a
richer source to that codeword is the potentially noninjective step.

[definition] A dilation `D_λ` has exact scale λ and transforms vector/covector components
and the measuring form together. For an invertible coordinate change B,
`v'=Bv`, `α'=B^-T α`, `G'=B^-T G B^-1`, so pairings are preserved. A physical dilation,
a unit conversion and an observer boost have different contracts. In a local orthonormal
spacetime tetrad with `x⁰=ct`, a Lorentz transition obeys `ΛᵀηΛ=η`; its hyperbolic rapidity
and time/length changes belong to that same map. A plot magnification is not thereby a
Lorentz boost. Integer cell grade, tensor order, rank, sample count and refinement level
are stated as integers, with their different mathematical meanings.

[definition] The phase survey's charts can be specified without decimal control values:
`κ=27/100`, `γ=7/20`, `β∈{1,4}`, connection turn `1/8`, `N=192`.
The detector is `[1/5,17/50)×[2/25,1/5)`. The magnified windows have widths
`4/25` and `4/125`, centered at `(15/16,73/384)`, hence dilations `25/4` and `125/4`.
A pixel/sample address `(i,j)` has exact source coordinate
`c_l+w_l((2i+1-N)/(2N),(2j+1-N)/(2N))`.
This identifies the chart; it does not turn a prior floating survey's classification into
an exact arrival proof. Exact/enclosed execution and display projection retain separate roles.

[proved-derived; formal-checked] A positive scale face k gives a Lorentz-normalized pair
`γ_k=(k+k^-1)/2`, `ξ_k=(k-k^-1)/2`, with `γ_k²-ξ_k²=1`.
Thus a boost can consume the mode relation `E(r)=k` without evaluating log k. The local
examples use k=2 and k=3. At k=φ, the golden constraint gives
`γ_φ=√5/2`, `ξ_φ=1/2`, an exact algebraic boost face. This is a source-qualified
mode conversion, not a claim that one physical speed is universally golden.

[proved-derived; formal-checked] The admitted Copson recurrence similarly carries
`s_n=√(u_n²-1)≥0`, `u_n²-s_n²=1` at every stage. Its positive scale face is
`k_n=u_n+s_n`, with inverse `u_n-s_n`. The next recurrence step adds the declared
`x/√(n+2)` term before completing the next admitted hyperbolic pair. The finite thresholds
and their infinite supremum identify c_CD as the all-stage admissibility boundary under
the established normalization. This joins the recurrence, scale and Lorentz-constraint
patterns while preserving their different applications and units.

## The overlap has stress-bearing faces

[definition] A collision group retains the two field domains, their oriented surface charts,
local tangent frames, contact incidence and constitutive interaction. On a shared spacetime
worldtube face Σ, retain the full stress-energy tensor, receiver velocity U and oriented
normal/area covector. In unit-normalized tetrad notation,
`e_U=T_(μν)U^μU^ν`, `j_U^μ=-T^(μν)U_ν`, and the face flux is `j_U·n`.
With stress in unit E0, the physical surface power density is `c E0` times its dimensionless
face coefficient. Proper-time interval and area complete the worldtube integral.

[definition] This gives an active receiving construction: the receiver has current, material,
velocity and an interaction with the incident field. Its response joins the coupled state.
In the working Holonic interpretation, thoughts and measurements are situated participating
faces of that dynamics. The receiving map is a chart of the interaction, not an unexplained
passive screen. Coherent transport, elastic reaction, viscous dissipation and electromagnetic
exchange retain their own constitutive terms; the word friction does not supply those equations.

[proved-derived] In GR, `G+Λ_c g=κ_E T`, contracted Bianchi, metric compatibility and
nonzero constant κ_E imply `∇_μT^(μν)=0`. Contracting the tensor equation with the actual
receiver/face gives its Einstein face. Conservation is the covariant balance of the complete
stress/current through oriented faces, not a conserved count or an identical scalar reading
for every observer. For symmetric T and `j_U=-T U`,
`∇_μj_U^μ=-T^(μν)∇_(μ U_ν)` when `∇·T=0`.
The symmetric observer deformation therefore supplies a work/exchange term. A conserved
observer-energy current requires the corresponding condition on U; it is not automatic for
an accelerating, deforming receiver. The coupled apparatus/material stress belongs in the
complete balance. In a curved region the invariant integrated statement is
`∫_(∂W) j_U·dΣ = -∫_W T^(μν)∇_(μ U_ν) dV_g`; a bare integral of vector components at
different points is not a global four-momentum without its transport/geometry data. These relations reuse `ReceiverStressEnergy`, `NavierStokesCurvedTransport`,
`HolonicCurvedArcEinstein` and the existing moving-boundary/current constructions.

[definition] The programme's Einstein turn-face notation retains the normalized complete
turn `Θ_turn=2π`, so the Newton-matched coupling is
`κ_E=8πG_N/c^4=4 Θ_turn G_N/c^4`. The period, Newtonian matching and physical units belong
to that source relation; no decimal value of π is a constitutive control. Contracting with
U and a face normal gives `(G+Λ_c g)(U,n)=κ_E T(U,n)`. In a tangent spatial face with
`g(U,n)=0`, the cosmological term vanishes in that particular contraction, not from the
full tensor or its other receiver faces.

[definition] At a two-sided contact, the projected relative slip s and constitutive traction
can obey `τ_A=ηs`, `τ_B=-ηs`, `Qdot=η⟨s,s⟩≥0` in the declared receiving tangent metric.
The common traction transfers momentum while its relative mode deposits heat. A moving
interface may also store surface stress/current; its jump balance retains those terms.
The full faces carry normal stress, tangential shear, energy flux, phase and their units.
Surface area alone neither specifies nor quantifies the interaction.

## Gyroparallelogram and an exact receiver calculation

[definition] In the Lorentz/Einstein velocity chart,
`u⊞v=u⊕gyr[u,-v]v`, and `D=(B⊞C)⊖A` completes the based gyroparallelogram.
Noncollinear boosts have an order-dependent spatial gyration. This is a concrete hyperbolic
specialization of the general connection/holonomy account; the diagram's four vertices do
not make it a spacetime four-volume. The existing `Geometry/Gyrogroup` owns the algebraic
contract and its flat additive restriction.

[established-bounded; implemented-exact] The prototype's
[contact receiver calculation](https://github.com/brandonrdug/holonics/blob/13f8c734/research/experiments/contact_receiver_faces/README.md)
uses rational velocities `u/c=(3/5,0,0)`, `v/c=(0,4/5,0)`. It obtains
`u⊕v=(3/5,16/25,0)`, `v⊕u=(9/25,4/5,0)`, and spatial gyration
`[[35,12],[-12,35]]/37`. The fourth vertex is `(315/781,560/781,0)` and its
Einstein gyromidpoint is `(9/35,16/35,0)`. A supplied local stress tensor yields face
coefficients `2`, `7/4` and `10/3` for three receivers, while transforming the same tensor,
receiver and face preserves each contraction exactly. Opposite oriented faces cancel;
the supplied friction law deposits `3/5` in its stated normalized power-density unit.

[project-postulate] This is the route from mathematical synthesis to HNN construction:
retain the constraint and generating mode, its actual field/face tensor, the typed transition
and its preserved balance, then implement the consuming operation. A familiar scalar name,
PDF label or numerical probe cannot take the place of that relation. Existing completed
constructions are starting material across domains; their source laws and scopes carry their
usefulness without a new permission or intelligence test.

[definition] The [receiver-holarchy synthesis](RECEIVER_HOLARCHY.md) now connects these active
stress faces to the perspective object, moving optical projection, induction pullback,
parameterized fractal arrival sets and entropy/encoding. A coordinate rebase transports both
source and receiver; changing the physical receiver need not preserve the old reading.
The constitutive mode and its continuation exceed the particular measured samples.
