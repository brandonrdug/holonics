# Pentagonal phase and constrained configuration navigation

[historical] Brandon's September 12 conversation supplies a photographed handwritten page,
asks for its identifiable geometry, and connects golden-ratio area constraints, RMS, matrices,
Rubik configuration counts and graph diameter to the standing solver work. This is a
mathematical analysis return; the parallel native implementation retains its own position.
The photograph is user-supplied evidence, not evidence of its author's diagnosis or intention.

## What the photograph supports

[historical] Brandon's subsequent September 12 clarification locates the eight spokes in the
drawing's construction/layer ruler, without asserting eightfold symmetry. The
[phase/clock continuation](2026-09-12_PHASE_PARITY_AND_CLOCKED_TORI_RETURN_GENERATOR_CODE_POTENTIALS.md)
uses that corrected reading. The symmetric pursuit model below remains one mathematical
illustration, not a symmetry claim attributed to Brandon or a recovered authorial algorithm.

[interpretation] The upper spiral is a winding mesh with repeated transverse intersections and
outward spokes. An eightfold polygon-pursuit construction is a candidate for the structure
Brandon notices, not a recovered generating algorithm. An exact eightfold model predicts
rotation invariance by 45 degrees; the asymmetric drawn seam and off-centre appearance do not
establish that invariance. No metric scale or evolution law identifies a wavelength, wave
equation, logarithmic pitch or three-dimensional helix from this photograph alone.

[interpretation] The upper star is recognizably a pentagram surrounding a pentagon. The five
`1.6` labels and central phi suggest the golden ratio, but their placement does not specify
areas rather than ratios. Treating them as simultaneous equal areas is a hypothesis tested
below. The lower drawing resembles nested cube projections with additional diagonals and
apices; its untyped crossings do not uniquely specify a polyhedron or higher-dimensional graph.

[interpretation] The interval 1996–2012 is most naturally a year chart: abbreviated intervening
years and `2004` elsewhere support this reading. The midpoint is 2004 and the difference is 16.
The arithmetic remainders are 1 and 2 modulo 3; their sum is 3, hence 0 modulo 3. They do not
by themselves determine the drawing's incidence.

[interpretation] `TABLE OF LAMBDA` could refer to the Platonic Lambda (powers of two and three)
or a Lambdoma musical-ratio table. The nearby powers of three and musical language motivate
those candidates; the small number line is not legible enough to identify a particular table.
Plato's actual source connects the doubled/tripled intervals to arithmetic and harmonic means:
[Timaeus 36](https://www.perseus.tufts.edu/hopper/text?doc=Perseus%3Atext%3A1999.01.0180%3Atext%3DTim.%3Apage%3D36).
The [Lambdoma author's ratio diagrams](https://www.lambdoma.com/pdfs/bill-meyer-lambdoma-figures.pdf)
document a separate musical-table usage, not a verification of this photograph's wider claims.

## A winding matrix construction

[definition] Let P cyclically shift n>=3 planar vertices, let 0<t<1, and iterate
`z(k+1)=((1-t)I+tP)z(k)`. Connect consecutive vertices at each step and the successive locations
of each vertex. This is discrete polygon pursuit; choosing the inverse shift reverses winding.

[proved-derived] With regular initial vertices `z_j(0)=R exp(2 pi i j/n)` and the convention
`(Pz)_j=z_(j+1)`, each iterate multiplies by `lambda=1-t+t exp(2 pi i/n)`.
Thus `z_j(k)=lambda^k z_j(0)`. Its modulus contracts and its argument advances at each step:
`|lambda|^2=1-2t(1-t)(1-cos(2pi/n))<1` for n>1. Interpolating k continuously gives logarithmic
spiral trajectories. This explains a repeated winding mesh through one matrix and a modular
index without an infinite collection of independently specified strings.

## Golden ratio: lengths, areas and modes

[proved-standard] Phi is the positive root of `r^2-r-1=0`, hence an algebraic irrational of
degree two, not a transcendental number. In a regular pentagon the diagonal/side ratio is phi.
See [MathWorld's supplied reference](https://mathworld.wolfram.com/GoldenRatio.html).

[proved-derived] For four consecutive vertices of a regular pentagon, Ptolemy gives
`d^2=s^2+sd`; dividing by s squared yields the golden-ratio equation. Similarity rescales
lengths by c and areas by c squared. A ratio specifies shape; an area value additionally fixes
scale only when the shape family and area unit have been declared.

[proved-derived] In a regular pentagram let a be the central pentagon's side, P its area and
T the area of one exterior tip triangle. The five centre triangles have apothem
`a cot(36 degrees)/2`; the exterior tip has height `a tan(72 degrees)/2`. Therefore

`P=5a^2 cot(36 degrees)/4`, `T=a^2 tan(72 degrees)/4`, `P/T=sqrt(5)`.

The last identity uses `tan(36 degrees)tan(72 degrees)=sqrt(5)`, obtained from the standard
36-degree cosine `(1+sqrt(5))/4` and the double-angle formulas. If `P=phi u^2`, then
`T=phi/sqrt(5) u^2`, approximately `0.72360679775 u^2`. Keeping the central pentagon fixed and
making each tip area P requires multiplying each exterior altitude by sqrt(5). The resulting
fivefold star no longer has the collinearity of the five straight pentagram strokes.

[proved-derived] The central pentagon and the pentagon through the five tips are similar with
length ratio `phi^-2`, so their area ratio is `phi^-4`. Their relative rotation is 36 degrees
up to the chosen vertex correspondence. Iterating that similarity is an actual convergent
construction. It is not by itself a physical optical ray map.

[definition] A concrete resonance model has five identical scalar coordinates x_j of mass m>0,
coupled around a cycle with energy `kappa/2 sum_j (x_(j+1)-x_j)^2`, kappa>0, and kinetic energy
`m/2 sum_j xdot_j^2`. It obeys `m xddot=-kappa L x`, `L=2I-P-P^-1`. This is a scalar oscillator
model with specified coupling, not the unrestricted spatial vibration of any pentagonal object.

[proved-derived] The Fourier vectors `v_j=exp(2pi i kj/5)` diagonalize L, with eigenvalues
`2-2cos(2pi k/5)`. These are 0 and two double levels `(5-sqrt(5))/2`, `(5+sqrt(5))/2`.
The nonzero frequency ratio is
`sqrt((5+sqrt(5))/(5-sqrt(5)))=sqrt((3+sqrt(5))/2)=phi`.
The ratio is independent of the common mass/coupling scale; different couplings can change it.

## Square roots and geometric charts

[proved-standard] Every finite nonnegative real area A has the unique nonnegative real root
sqrt(A). This is an equal-area square's side, not an assertion that its source has square shape
or a single global surface chart. Over a restricted coefficient field a root can be absent:
`x^2=2` has no rational solution. Algebraic extension and geometric coordinate charts are
distinct constructions. Global chart failure does not preclude integrating area over an atlas.

[proved-derived] The field K=Q(sqrt(5)) contains phi but does not contain sqrt(phi). Its norm
sends phi to -1. If y in K satisfied y squared=phi, then `Norm(y)^2=-1`, impossible in Q.
The positive real square root exists in a larger algebraic extension. This gives the
area-root intuition an exact coefficient-domain obstruction without obstructing real area.

[definition] For a Euclidean surface parameterization with Jacobian J, its Gram metric is
`G=J^T J` and the area density is `sqrt(det G)`. For a linear map of a unit planar square with
singular values s1,s2, the image area is s1*s2, while the equal-area square side is sqrt(s1*s2).
The RMS directional stretch is `sqrt((s1^2+s2^2)/2)`, equivalently `sqrt(trace G/2)`.

[counterexample] `J=diag(2,1/2)` has area multiplier 1 and equal-area side 1, but RMS stretch
`sqrt(17/8)`, approximately 1.45774. Thus RMS is not the missing-chart substitute for an area
square root. It retains a different quadratic receiver. A projection followed by an RMS can
be defined, but it must specify the projection and measure.

## Counting configurations through their actual constraints

[proved-standard] For the ordinary 3x3 cube relative to its fixed centre frame, eight distinct
corners have `8!` placements and three twists each; twelve distinct edges have `12!` placements
and two orientations each. Their reachable states satisfy total twist zero modulo 3, total
flip zero modulo 2, and equal corner/edge permutation parity. These are sufficient as well as
necessary for ordinary legal cube configurations. The count is
`8! 12! 3^8 2^12 / (3*2*2) = 43,252,003,274,489,856,000`.
The [cubie representation](https://www.kociemba.org/math/cubielevel.htm) describes the orientation
and permutation composition; the supplied [cube reference](https://mathworld.wolfram.com/RubiksCube.html)
gives the count. Marked centre orientations and alternative spatial identifications change the task.

[proved-derived] The geometry behind the user's `2^3` and `3*2^2` is the cube's eight vertices
and twelve edges. More generally a d-dimensional cube has `binomial(d,j)2^(d-j)` j-faces:
choose the j varying coordinate directions and one of two fixed endpoints in each other
direction. This counts faces, not a generalized puzzle's legal configuration population.

[proved-standard] For finitely many species a with n_a distinguishable pieces, each admitting
o_a orientations independently of placement, the ambient count is `product_a n_a! o_a^n_a`.
When these form an ambient group H and the complete legality test is the kernel of a
homomorphism f, the legal count is `|H|/|image(f)|`. Only independent, uniformly realized
constraints justify replacing the image size by the product of their stated moduli.

[proved-standard] For any finite group G of allowed invertible moves acting on an initial
configuration x0, the reachable population is its orbit, of size `|G|/|Stab_G(x0)|`.
This remains valid for rectangular arrays and constrained labels. The group, coefficient set,
slot identity and moves must first be specified. A nonfree symmetry quotient requires orbit
counting rather than blindly dividing by the symmetry count; noninvertible moves instead
give a transition system. See [Mathlib's orbit-stabilizer theorem](https://leanprover-community.github.io/mathlib4_docs/Mathlib/GroupTheory/GroupAction/Quotient.html).

[proved-derived] A consistent linear system on N entries over a finite field F_q has
`q^(N-rank A)` solutions: one particular solution plus the kernel. For integer A modulo m,
take unimodular `UAV=D` with r nonzero Smith entries d_i and set b'=Ub. Each equation
`d_i y_i=b'_i (mod m)` has gcd(d_i,m) solutions when that gcd divides b'_i, and none otherwise.
Every remaining row must have b'_i=0 modulo m; each of the N-r free variables has m choices.
Consequently the nonempty solution count is `m^(N-r) product_i gcd(d_i,m)`.
The Smith construction is documented in [Stanley's survey](https://math.mit.edu/~rstan/papers/snf_survey.pdf).

[proved-derived] For nonsingular integral square M, unimodular reduction also gives
`|Z^d/MZ^d|=product_i |d_i|=|det M|`. The same determinant is the volume of the fundamental
parallelotope. Thus a geometric volume can equal a constrained configuration count through
an explicit lattice construction. Real matrices without an integral lattice inclusion do not
automatically carry that finite counting interpretation.

[counterexample] `M1=diag(3,3)` and `M2=diag(1,9)` both have determinant/area/index 9, but their
quotients are `C3 x C3` and `C9`. With unit-cost translations by plus/minus the standard basis,
the first graph has diameter 2: each coordinate needs at most one step and (1,1) needs two.
The second has diameter 4: the first coordinate is trivial and the nine-cycle has maximum
cyclic distance four. Area and cardinality therefore determine neither composition nor diameter.

[proved-derived] The base-ten digit-sum rule is `10^k=1 (mod 9)`, hence an integer and its digit
sum agree modulo 9. In base b the analogous modulus is b-1. The prime-power factorization 9=3^2
does not distinguish C9 from C3 x C3; their element orders do. Irreducibility belongs to the
specified ring and operations, and is preserved under actual ring isomorphisms.

## Optimal navigation and the existing solver owners

[definition] For a finite connected Cayley graph with inverse-closed move set S, define
`V(g)=min{|w| : T_w(g)=e}`. The diameter is `max_g V(g)` and a shortest-word algorithm chooses
at each non-goal state an s minimizing V(T_s(g)). Bellman's relation is
`V(g)=1+min_s V(T_s(g))`; thus the chosen value decreases by one at each step. Computing V
or an equivalent optimal policy remains the constructive problem. Matrix powers of the
configuration adjacency matrix count walks; the first nonzero entry determines the distance.

[proved-standard] The Cayley graph's vertex transitivity makes its diameter equal to its
maximum distance from the identity. For a general configuration graph the worst distance to
one specified target is that target's eccentricity, which need not equal the diameter. If an
action has stabilizers, its state graph is naturally a Schreier graph; its target and costs
must still be specified.

[established-bounded; computational-witness] The ordinary 3x3 diameter is 20 when a face's
quarter or half turn each costs one, and 26 when a half turn costs two. The original teams'
[20-move account](https://www.cube20.org/) and [quarter-turn account](https://www.cube20.org/qtm/)
give the computational boundaries. A diameter supplies a worst-case optimal length; it does
not by itself give an efficient per-instance optimal policy.

[established-bounded; computational-witness] Rubik's Clock has 14 independent dial coordinates
modulo 12; the 18 visible dials include four mechanically shared pairs. Its dial-state group
is `(Z/12Z)^14`, and the published move convention has diameter 12. Pin configurations are
controls rather than additional target coordinates in that count. See
[Jaap's construction](https://www.jaapsch.net/puzzles/clock.htm) and the
[complete distance computation](https://www.cube20.org/clock/).

[definition] Clock move types are columns of a matrix B, and solving x asks for
`Bu=-x (mod 12)`. Because their induced dial translations commute, u records net amounts by
move type. For the convention charging one move for any nonzero amount of one type, optimal
navigation minimizes the number of nonzero entries of u among the complete solution family.
Linear solvability and minimum-cost representation are different receivers.

[proved-standard] The variable-n cube decision problem asking whether a configuration has
a solution of at most k moves is NP-complete in the slice-turn and slice-quarter-turn metrics:
[Demaine, Eisenstat and Rudoy](https://erikdemaine.org/papers/Rubik_STACS2018/paper.pdf).
A fixed 3x3 graph is one finite object. A polynomial-time exact algorithm for the general
NP-complete family, including representation and execution cost, would imply P=NP; a small
fixed diameter or cheap verification of a supplied word does not establish such an algorithm.

[established-bounded; source-inspected] At inspected source revision `122da135`,
`Foundation/TransportWord.lean::generatorEquivarianceExtendsToEveryTransportWord` and
`Foundation/ReceiverHistoryCompression.lean::quotientCommutesWithEveryOrderedWord` state the
existing generator-to-word descent law. The latter's `separatingSuccessorReopensTheProposedQuotient`
gives the future separator. These sources were read, not freshly rebuilt in this analysis.

[proved-derived] If `q T_s=U_s q` for every move and q maps the target to an abstract target,
every full solution word projects to an abstract solution of no greater cost. Therefore
`h(x)=distance(qx,qtarget)` is an admissible lower bound for V(x). Multiple such bounds combine
by maximum; summation requires a separate cost allocation. Exact equality of distances requires
additional information beyond generator descent, such as cost-preserving lifts that end at
the actual target. A single exterior face or norm can collapse states whose futures differ.

[counterexample] On C9 with target 0 and moves plus/minus 1, states 1 and 8 both have V=1.
The same +1 move takes their values to 2 and 0. Thus even exact distance-to-go, treated alone
as a state coordinate, does not give a deterministic descended action for each labelled move.
Using V to choose a shortest move assumes access to the state or other sufficient information
with which to evaluate the candidate successors.

[established-bounded; source-inspected] The existing exact rational matrix owner
`crates/holonic-engine/src/exact_linear.rs::preimage_fibre` returns a particular solution plus
kernel, or inconsistency, and `exact_linear/bilinear.rs` composes that owner with fixed-port
sections. This is the available parameter-family construction; it is not an inspected modular
Clock solver or universal shortest-word implementation. The
[September 11 solver record](2026-09-11_HOLONIC_SOLVER_NAVIGATES_EXACT_GENERATOR_FACTORIZATIONS.md)
already sets out the generator/domain/decoder/cost contract for its application.

[historical; source-inspected] The recovered exterior `RubikBoard.dc.html` uses a 24-facelet
2x2 state and bounded search. The
[September 10 record](2026-09-10_HNN_DIAGRAMS_EXPOSE_COMPOSITION_DEVELOPMENT_AND_SOULKILLER_LIFTS.md)
retains the board address 17, word `R U'`, depth 2, and its rechart interpretation. That address
is not a graph diameter. The current analysis reuses this distinction rather than introducing
a separate Rubik subsystem.

## Verification scope

[established-bounded; computational-witness] Python standard-library arithmetic checked the
displayed pentagram area ratio, normalized arm area, 3x3 configuration integer, area-preserving
RMS example, year residues and midpoint. The complete symbolic derivations appear above.
The two lattice diameters were independently enumerated by BFS in their stated move sets;
the five-cycle eigenmodes were checked against the explicit Laplacian (maximum residual
less than 1e-13 for each complex Fourier vector). For
`A=[[8,-6,0],[-6,6,0],[0,0,0]]` modulo 12, unimodular row/column changes give diagonal
`[2,6,0]`. Enumerating the 12 cubed input triples returned 144, 0 and 0 solutions at respective
targets `[2,0,0]`, `[1,0,0]`, `[2,0,1]`, checking both kinds of inconsistency. These are
exterior mathematical checks, not HNN/native execution claims. No proof or runtime source
changed, so no Cargo, CUDA or Lean build is required by this analysis.
