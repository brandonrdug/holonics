# Phase parity and clocked tori return generator code potentials

[project-postulate] Brandon's current September 12 request makes this the active research
increment before resuming the paused parallel HNN implementation. Recover time parity,
cross-entropy, complex modulation, tori and nonorientable transport, friction, code lengths,
Smith factors and fractal scale through the existing owners. The interpretation of eight
spokes concerns the drawing's construction and layer gauge; it does not assert eightfold
symmetry. The preceding [pentagonal analysis](2026-09-12_PENTAGONAL_PHASE_AND_CONSTRAINED_CONFIGURATION_NAVIGATION.md)
supplies its exact regular-pentagram and C5 calculations.

## The spoke is a layer receiver

[interpretation] A fixed spoke intersects multiple winding layers and thereby supplies an
ordered radial ruler. Its outward extension matters even where the winding curves stop. The
same ruler can be oriented toward or away from the centre without changing its geometric
incidence. This is consistent with Brandon's partial tower/staircase reading; it does not
recover the photographed author's unrecorded construction or an unobserved depth coordinate.

[proved-derived] For the logarithmic model `r(theta)=R exp(b theta)`, a ray at angle alpha
meets successive turns at `r_k=R exp(b(alpha+2pi k))`. Thus log radius is affine in layer index,
while ordinary radii are geometrically spaced. Direct differentiation of `(r cos theta,r sin theta)`
gives curvature `1/(r sqrt(1+b^2))`. It grows inward. The singularity is a limiting geometric
claim of this model; the finite photographed drawing does not establish an actual singularity.

[established-bounded; computational-witness] The revised local explanation uses eight fixed
ruler spokes independently of the polygon's side count. It computes ray/segment intersections
with all 101 polygon layers, deduplicates vertex hits, and exposes layer index and dimensionless
radius `r/R0`. The direction toggle changes ruler orientation. Desktop/mobile and light/dark
inspection plus native-control interaction checks returned eight spokes and 808 intersections.
Its fragment is `.local/artifacts/2026-09-12-geometry/spiral-matrix.html`.

## Time parity retains the receiver and the protocol

[definition] A parity comparison specifies an involution Theta. A receiver is even when
`r(Theta x)=r(x)` and odd when `r(Theta x)=-r(x)`. Chronology is the actual ordered transport.
The chain boundary relation `d^2=0`, a sign grading anticommuting with d, a physical time-reflection
symmetry, and invertibility of an operation are different statements. The older canon sentence
identifying all parity with boundary closure is corrected in `TABLET_THE_OPERATIONS` §5.3.
`Millennium/Chronology` now scopes its existing fixed-anchor Swing theorem accurately, including
the zero-span case and the endpoint/reference dependence of its oriented receiver.

[proved-derived] For `xdot=A x` and linear Theta with Theta squared=I, the transformed trajectory
`y(t)=Theta x(-t)` satisfies the same equation exactly when `A Theta=-Theta A`. A spatial
symmetry instead commutes with A. Time-dependent drives require their reversed protocol and
the appropriate receiver/frame transport; the comparison does not reverse a past occurrence.

[counterexample] The damped scalar oscillator has
`A=[[0,1],[-omega^2,-2gamma]]`, `Theta=diag(1,-1)` and
`Theta A Theta + A = diag(0,-4gamma)`. Its energy derivative is `-2gamma p^2`, while adding a
heat coordinate with derivative `2gamma p^2` preserves total energy. Conservation of that
enlarged face therefore does not make the reduced passive law time-reflection symmetric.
At finite exact dimension the matrix exponential is nevertheless invertible; its expanding
inverse is a different physical/admissibility and numerical-stability question. The canon's
earlier assertion that forward heat itself necessarily collapses states is repaired too.

[established-bounded; source-inspected] `causal_reflection.rs` already retains exact even and
odd response faces on its declared finite symmetric lattice and a separate instantaneous
subtraction coordinate. Its finite face-lock law is not a new continuum response measurement.
The Niven-theorem prose is corrected: rational sine values include plus/minus one-half, just
as rational cosine values do. This changes no runtime operation.

## Complex cross-entropy: one even and one odd reading

[definition] Reuse the positive normalized sections p,q and an actual angular lift theta,
including any relevant winding. The existing September 12 definition is

`C(p;q,theta)=H_2(p,q) - (2i/ln2) sum_i p_i theta_i`.

It is the probability-calibrated negative lifted amplitude logarithm: amplitude is sqrt(q),
which supplies the factor two. For source phase phi the compared difference is

`C(p;q,theta)-C(p;p,phi)=KL_2(p||q) - (2i/ln2) sum_i p_i(theta_i-phi_i)`.

[proved-derived; formal-checked] `Physics/InformationDifference.lean` now proves the real face,
the complete displayed excess identity, conjugation under theta -> -theta, and cancellation of
a common channel-wise phase rechart from the difference. This formalizes the existing
[complex-information derivation](2026-09-12_FRACTAL_MODES_LIFT_ATTENTION_INTO_MASS_PRESERVING_GENERATOR_COMPRESSION.md),
reusing its real cross-entropy/KL owner. It does not redefine ordinary Shannon entropy as complex.

[counterexample] Even the combined scalar C does not determine every future coherent receiver.
For p=q=(1/2,1/2), phases `(theta,-theta)` always give C=1. A normalized sum/difference analyzer
instead returns powers `(cos(theta)^2,sin(theta)^2)`: theta=pi/6 and pi/3 separate. Thus a
weighted phase mean is not an adequate replacement for a full phase-bearing current family.

[definition] Statistical time asymmetry uses a different, declared comparison: a forward path
law P_F and the pullback Q of the matched reversed-protocol law. Its mean excess path code is
`E_PF[log2(P_F/Q)]=KL_2(P_F||Q)`. Physical entropy production follows only when the supplied
process and reservoir law establish the thermodynamic log-ratio identity, with factor k_B ln2.
Swapping the two arguments of an arbitrary token cross-entropy is not that construction.
[Seifert's physical source](https://arxiv.org/abs/1205.4176) specifies the trajectory/bath setting.

## When a modulator is linear, reflected, singular or invisible

[definition] Every scalar real-linear complex map has the form `M_(a,b)(z)=a z+b conjugate(z)`.
The actual two-real-coordinate matrix is
`[[Re a+Re b,-Im a+Im b],[Im a+Im b,Re a-Re b]]`.
Complex linearity is b=0; pure conjugate linearity is a=0. A unit-modulus b with a=0 is a
mirror about the axis arg(b)/2. A mirror is therefore still linear over the real chart.

[proved-derived; formal-checked] `Physics/PhaseCarrier.lean` now proves

`(a,b) compose (c,d) = (ac+b conjugate(d), ad+b conjugate(c))`,

the direct/reflected restrictions, mirror involution, and the real determinant
`det M=|a|^2-|b|^2`. The zero determinant stratum is singular, not a no-change condition.
The full identity has a=1,b=0. A zero change at a receiver instead means `q(Mx)=q(x)`;
in a linear chart its fixed-face source family is `ker(q(M-I))`.

[proved-derived; formal-checked] The same owner adds an explicit future separator: the real
receiver identifies i and 0 now, but multiplication by i maps their real readings to -1 and 0.
The existing `ReceiverHistoryCompression` and `KernelModeReduction::compile_source_action`
already provide the criterion and returned separator for a future-stable quotient. A mirror,
rotation or other active source change can be invisible now and visible after a later generator.

[proved-derived] For an admitted continuous source vector field F and conserved receiver C,
`DC_x F(x)=0` says the source moves tangent to a level fibre. This does not select F or its
speed. A Lorentzian null direction additionally satisfies its indefinite quadratic metric;
a geodesic/free-fall claim additionally requires its connection and actual dynamical equation.
These are concrete ways to strengthen the proposed conservation-to-free-motion bridge.

## Friction, matching and code potentials

[project-postulate] The recovered friction doctrine names consequential boundary coupling at
the project grain. A dissipative friction law is a particular physical realization. The current
account retains the coupling and its transported flux, rather than treating every interaction
as a residual or every zero reflected reading as absence of contact.

[proved-derived] The existing scalar passive junction chart with positive admittances has
`Gamma=(Y_i-Y_t)/(Y_i+Y_t)`, reflected power `R=Gamma^2` and transmitted power
`T=4Y_iY_t/(Y_i+Y_t)^2`. Direct expansion gives R+T=1. Swapping the traversal direction
negates Gamma while preserving these power fractions. At matching, Gamma=0 and T=1.
Thus a reflected face is null while current crosses. `traversible_chain.rs` already distinguishes
inverting, preserving and matched junction readings with their actual directed passage.

[definition] A nonnegative weighted adjacency A with positive right eigenvector v and positive
eigenvalue lambda supplies the transition
`P_ij=A_ij v_j/(lambda v_i)`. The eigenvector equation makes each row sum to one. On each
positive allowed edge, write `V_i=log2(v_i)` and `ell_ij=-log2(P_ij)`.

[proved-derived; formal-checked] `Foundation/ReceiverCodeCost.lean` now proves row normalization,
nonnegativity, and the exact edge law

`ell_ij=log2(lambda)-log2(A_ij)+V_i-V_j`.

Its existing `serial_boundary_balance` cancels intermediate potentials through actual joining
equalities. Symmetric edge weights also satisfy `v_i^2 P_ij=v_j^2 P_ji`, checked in the same
owner. Normalized squared eigenvector weights then give a reversible stationary chain.
The eigenpair is a hypothesis; this theorem does not supply a generic efficient eigenpair solver.

[proved-derived] For the allowed-word generator `B=[[1,1],[1,0]]`, lambda=phi and v=(phi,1).
Its transitions are `[[1/phi,1/phi^2],[1,0]]`: two consecutive 1s are forbidden. A length-n
allowed path has conditional code `n log2(phi)+V_start-V_end`. The stationary distribution is
`(phi^2,1)/(phi^2+1)`. Adding its initial code makes the full path probability
`v_start v_end / ((phi^2+1) phi^n)`, which agrees with its reversed path. The conditional
boundary asymmetry and full stationary time parity are therefore compatible.

[proved-derived] In that matched source the entropy rate is log2(phi), approximately 0.694242
bits per step: stationarity cancels the mean endpoint-potential change. Another reference
transition code adds the stationary weighted row KL. Zero excess cost retains the intrinsic
source entropy; it does not imply zero bit length, zero execution work or zero physical energy.
For general bidirectional stationary flux F_ij=pi_i P_ij, `KL_2(F||F^T)` measures the declared
one-step reversal asymmetry and vanishes exactly at detailed balance on the common support.

[proved-derived] The same two-state transition has eigenvalues 1 and `-phi^-2`: it is similar
to B/phi. With column probability evolution `p_(n+1)=P^T p_n`, its zero-sum difference from
the stationary law is exactly `p_n-pi=(-phi^-2)^n(p_0-pi)`. Thus an ordinary admissible
probability relaxation can alternate its oriented difference without reversing chronology.
For `p_0-pi=(d,-d)`, the stationary-reference cross-entropy obeys
`H2(p_n,pi)-H2(pi)=-2d(-phi^-2)^n log2(phi)`. This signed baseline comparison alternates;
the nonnegative KL excess instead subtracts the changing source entropy H2(p_n). Confusing
those two baselines hides the parity question. The deterministic edge 1->0 has conditional
code length zero while changing the source state; its endpoint-potential drop cancels the
bulk code term, not the actual traversal.

## Tori, golden clocks and nonorientable returns

[proved-derived] The scalar equal-coupling C5 model has Laplacian eigenvalues 0 and two double
levels `(5-sqrt5)/2`, `(5+sqrt5)/2`, with nonzero frequency ratio phi. For a product lattice
`K=L5 tensor I+I tensor Lm`, modes have eigenvalues `lambda_k+mu_l`. The l=0 sector retains the
original ratio; adding a nonzero second-direction eigenvalue generally changes it. A common
clock/coupling scale preserves the ratio while arbitrary constitutive modulation need not.

[definition] A two-phase torus uses angles modulo one cycle. At constant rates `(1,phi)`, the
trajectory has no common positive exact return time because phi is irrational. At Fibonacci
time F_n the first angle closes and the second retains winding F_(n+1) plus residue epsilon_n.

[proved-derived; formal-checked] `Millennium/Turn.lean` now reuses Mathlib's Fibonacci/golden
identity to prove

`epsilon_n=F_n phi-F_(n+1)=(-1)^(n+1) phi^(-n)`,

`epsilon_(n+1)=-phi^(-1) epsilon_n`.

The returned phase error alternates orientation and contracts, while the positive observation
times increase. This is parity of a sequence of returns, not reversal of physical chronology.
The clock and signed residue are sufficient operands of this comparison; no past sample archive
is needed. The original rational clock quotient/residue owner retains its separate exact scope.

[proved-standard] A torus helix has two winding numbers. The `(p,q)` torus link has gcd(p,q)
components; two offset helical strands do not by themselves make a nonorientable surface.
A ribbon becomes a Mobius band through a reversing cross-section gluing. The Klein bottle's
relation `a b a^-1=b^-1` records a reversing monodromy; abelianization gives `2b=0`, hence
`H1(K;Z)=Z plus Z/2`, whereas `H1(T2;Z)=Z^2`. A sign-sensitive normal returns reversed around
the Mobius base while its squared norm returns unchanged. See
[Hatcher's algebraic topology source](https://pi.math.cornell.edu/~hatcher/AT/ATpage.html).

[definition] Existing `HolonicFourTorusCarrier`, `FourTorusParametronCurrent`, clocked
pantographic Swing and `HolonicTorusMonodromyReceiver` retain winding/cuts, current/fibre,
clock quotient/residue and pairing covariance. Runtime `contact_gluing` and `traversible_chain`
retain orientation-reversing seams. These constructions do not impose torus topology on every
native ecology; their source maps specify when they are relevant.

## Smith factors connect phase clocks, finite counts and scale

[proved-derived] For integer A acting on `(Z/m)^d`, a k-tick return is the kernel of `A^k-I`.
If this matrix has nonzero Smith factors s_1,...,s_r, its abstract return group is

`(Z/m)^(d-r) plus direct_sum_i Z/gcd(m,s_i)`,

and its cardinality is `m^(d-r) product_i gcd(m,s_i)`. Unimodular row/column changes remain
invertible modulo m, so each diagonal equation contributes exactly its gcd factor. An affine
clock adds a target to the same congruence system and can return an empty fibre.

[established-bounded; implemented-exact; computational-witness] The new
`crates/holonic-engine/examples/phase_clock_smith.rs` uses the standing BigInt Smith owner
on the scalar mirror, C5 shift and actual rank-four A1 monodromy from `SixSphereMonodromy`.
It returns the matrix, cyclic kernel factors, cardinality, fixed-width address size and existing
Smith work/schedule fields for moduli 5 and 12 and periods 1,2,3,5. The scalar mirror has gcd(m,2)
fixed phases but every phase returns in two ticks; C5 returns all five phases in five ticks;
A1 returns all four in three ticks. Tiny modulus-5 scalar/C5 populations independently check
the returned factors. The larger returns are exact SNF computations, not enumeration claims.

[proved-derived] The Rubik count contributes `log2(8!)+log2(12!)+8log2(3)+12-log2(12)` bits,
approximately 65.2294, so a fixed-width index needs 66 bits. The three compatibility constraints
remove log2(12), approximately 3.58496, bits from the ambient count. This one finite population
has no nonzero Hausdorff dimension under its discrete metric.

[proved-derived] With an explicit refinement ruler epsilon and distinguishable population
N(epsilon), a scale dimension instead reads `log N(epsilon)/log(1/epsilon)` in its limit.
A fixed legal fraction such as 1/12 changes finite code cost but not that limiting exponent.
For fixed Smith factors and m increasing, the return count has exponent d-r: the gcd terms
are bounded finite torsion corrections. Repeating constraints at every scale can change the
exponent, so a refinement law must be supplied before calling a count fractal dimensionality.

[proved-derived] The no-consecutive-ones generator has F_(n+2) length-n words. In the symbolic
metric where a first difference at position n has distance s^-n, its dimension is
`log(phi)/log(s)`. Equivalently a separated graph-directed geometric realization has that
dimension under the corresponding separation hypotheses. The scale contribution log(s) and
the address growth log(phi) are separate operands. The existing finite Cantor owner instead
has 2^n addresses of width3^-n, yielding the familiar log2/log3 under its self-similar limit
hypotheses. Neither statement follows from a lone permutation count.

## What returns to HNN

[established-bounded; implemented-exact; computational-witness] The same phase/Smith example
now infers a monic annihilator through `ExactRatMatrix::preimage_fibre`. At each degree d it
solves `sum_(j<d) c_j vec(A^j)=-vec(A^d)`, retaining the returned coefficient family, and uses
the matrix dimension as the Cayley-Hamilton search bound. Its first consistent degree is
three for C5 and six for C5xC5. The returned ascending coefficient lists are `[0,5,-5,1]` and
`[0,-500,850,-525,150,-20,1]`, with empty coefficient kernels and complete zero matrix residuals.
The matrices are supplied; these coefficients are inferred. Its power-construction work is
375 and 93,750 exact rational multiplications respectively; the receipt labels that scope
separately from the preimage solve's uninstrumented work.

[established-bounded; implemented-exact; computational-witness] The
[public mathematical-session consumer](../experiments/pentagonal_torus_transport/README.md)
reads those inferred coefficients, lowers L^16 and K^12, and applies them through the existing
resident construction. It independently verifies the full polynomial identities and the
requested powers, and composes L^2 and L^3 through public `compose`. The 25-event process
returned no stream error; its final census was 92 captured launches, 13 deed launches,
143,972 ingress bytes and 142,176 resident bytes. This is not an end-to-end speed comparison:
the current native consumer takes the lowered matrix, not a resident polynomial-coefficient
recurrence. That compiler binding remains a precise useful next integration.

[established-bounded; implemented-exact; computational-witness] The same native run applies
the realified complex analyzer `(z0,z1)->(z0+i z1,z0-i z1)` to `(2,i)` and `(2,-i)`.
It returns `(1,3)` and `(3,1)` respectively. Separate input intensities are `(4,1)` in both
cases; normalized output powers are `(1/10,9/10)` and `(9/10,1/10)`. This is an actual future
phase separator in the declared coordinate chart. Exterior code comparison gives KL excess
`(4/5)log2(9)`, approximately 2.53594 bits, when one output distribution codes the other.
The cross-entropy logarithm was not executed natively in this experiment.

[established-bounded; source-inspected] The inspected implementation baseline is `4320328a`.
`read_prospective_word` composes actual learned member/condition relations into one anchored
joint family. `NormalWaveFamilyReceiver::affine_relation` retains the joint before its
minimum-norm display projection, and `predict_continuation` decodes that one joint. Compound
action publication, self-re-entry/feedback and economical general continuation remain open.
The current normalized receiver returns the real cross-entropy/KL derivative in its declared
potential chart; it does not contain the newly formalized angular-lift comparison.

[definition] The consuming construction should compose the admitted analyzer or modulator
with this retained family before taking intensity, probability or code receivers. A logical
epoch is not a supplied physical/phase clock. A compact representation must preserve every
admitted source action and receiver needed by the task, including the original anchor and
pending comparison. Reflection parity may reduce a family only when the actual generators
preserve its sectors; changed coupling can mix them and reopen the erased directions.

[definition] Recurrence compression concerns the algebra of operators, not necessarily the
dimension of the state. C5's cubic relation can encode all powers with I,L,L^2 while retaining
its five-dimensional state. The C5xC5 sum has a degree-six relation while retaining its
25-dimensional state. Different noncommuting learned generators require a closed joint
operator representation or retained ordered factors; a polynomial for one operator is not
a certificate for arbitrary changing words.

[definition] Code candidates can be priced by the actual returned representation, work,
clock/residency, endpoint potential and residual, through `ReceiverCodeCost`. The Perron
construction supplies one explicit instance of that law. A zero receiver discrepancy or
conserved spectrum alone does not supply an optimal policy. For a growing NP-complete family,
an efficient exact representation must also supply an efficiently executable decoder and
policy, with input and coefficient bit costs included.

## Checks and returned artifacts

[established-bounded; formal-checked; process-audit] The focused final build of
`Physics.InformationDifference`, `Physics.PhaseCarrier`, `Millennium.Turn`,
`Millennium.Chronology` and `Foundation.ReceiverCodeCost` completed successfully with 3,732
dependency jobs. The new declarations' printed axioms are the ordinary propext/Classical.choice/
Quot.sound foundation; no admitted proof is used. The final log is
`.local/artifacts/2026-09-12-geometry/phase-parity-final-lean.log`. Earlier failed proof attempts
were repaired before this result; untouched research targets were not separately rebuilt.

[established-bounded; computational-witness] `cargo check -p holonic-engine --example phase_clock_smith`
passed for the initial clock example. Subsequent `cargo run -q -p holonic-engine --example
phase_clock_smith` compiled and returned the final clock factors and inferred recurrences.
The public-session consumer then ran again using those inference coefficients, returning the
native results above. Its input, actual output, process receipt and portable inference summary
are retained under `research/experiments/pentagonal_torus_transport/`. The complete Smith and
inference work receipt is `.local/artifacts/2026-09-12-geometry/phase_clock_smith.json`.

[established-bounded; computational-witness] Visual checks cover the revised spokes, selected
layer/radius, winding and direction controls at 736px and 360px in light and dark appearances.
They validate the constructed illustration, not a mathematical classification of the photograph.
