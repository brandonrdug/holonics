# THE BOUNDARY WAVE INTEGRATES THE SHEET; THE EDGE WORD MAKES THE GEAR

**2026-07-17 · RATIFIED / DEPOSITED AS FORMULA §LXXXI / NO SOMA INTERIOR CHANGE**

## Verdict

One rendered polygon can lawfully be read at several typed grains, but those grains may not be
collapsed:

```text
source vertices
ordered boundary path
projected crossing coordinates
materially admitted joints
complementary regions
oriented winding layers
filled sheet
```

The face count is never a universal function of the visible corner count alone. It follows from
the declared dimension, incidence degrees, edge word, projection, crossing multiplicity, material
contact law, and filling rule. The exact instrument is an `f`-vector plus incidence and boundary
maps, not the undifferentiated word “intersection.”

## 1. Faces and corners are incidence populations

For the `d`-dimensional rectangular cell, the number of `k`-faces is

```text
f_k = 2^(d-k) choose(d,k).
```

Therefore a cube carries

```text
(f_0,f_1,f_2,f_3) = (8,12,6,1).
```

Its six square faces and eight corners are related by double-counting face–corner incidence:

```text
6*4 = 8*3 = 24.
```

Each corner chooses one of two sides on all three axes; each face chooses one of three axes and one
of two sides. “Six faces” and “eight intersections” are consequently different grades of one
incidence body, not rival descriptions of one population.

For a connected planar embedded graph after every materially admitted crossing has subdivided its
arcs,

```text
V - E + F = 2,
```

with the exterior included. For `c` connected components, `V-E+F=1+c`. An apparent crossing which
is only a projection may contribute to the display arrangement while contributing no material
joint to the carried path graph.

Examples:

```text
ordinary filled n-gon: boundary (V,E)=(n,n), one intrinsic 2-cell
butterfly quadrilateral with admitted crossing: V=5, E=6, F=3 including exterior
regular planar hexagram with six admitted crossings: V=12, E=18, F=8 including exterior
cube boundary: V=8, E=12, F=6
```

## 2. The path is the boundary wave; its filling is the sheet

For an oriented sheet `S` and boundary path `gamma`,

```text
partial S = gamma,
partial gamma = 0.
```

They may appear in one drawing while remaining different typed objects. An annulus has two boundary
components with opposite induced orientation,

```text
partial A = gamma_outer - gamma_inner.
```

A butterfly is not an annulus. It is one immersed boundary path with a transverse self-crossing.
Its complementary lobes carry different signed winding. For a point outside the path,

```text
w_gamma(x) = (1/(2*pi)) integral_gamma d arg(z-x)
```

gives the integer layer of the oriented filling. A simple polygon has one nonzero interior layer;
a butterfly can carry opposite lobe signs; a pentagram carries regions of different winding
multiplicity. This is a deterministic layered face, not a quantum-random state.

A family of paths integrates into a sheet through a sweep

```text
H(s,t): transverse_family x traversal_order -> receiving space-time.
```

The local oriented sheet element is `partial_s H wedge partial_t H`. A two-dimensional rendering is
a many-to-one quotient of that carried body. Reversing `t` reverses boundary hand, signed winding,
and accumulated turn while an unoriented silhouette may remain unchanged.

## 3. The edge word makes the regular polygon a gear

For `n` equally spaced points on a circle of radius `R`, the star word `{n/k}` connects every
`k`th point. Its repeated chord has length

```text
ell_k = 2 R sin(pi k/n).
```

The same point palette carries different circuits:

```text
components          = gcd(n,k),
steps per component = n/gcd(n,k),
winding per component = k/gcd(n,k).
```

Thus `{6/2}` is two triangular circuits while `{5/2}` is one pentagram circuit. For the regular
hexagon,

```text
ell_1 : ell_2 : ell_3 = 1 : sqrt(3) : 2,
```

the exact `30-60-90` chord spectrum. The square exposes the `1:sqrt(2)` diagonal relation of the
`45-45-90` cell. The earlier Timaean triangle work is therefore an exact high-symmetry chord face,
not a complete alphabet of possible angles.

Each chord is a finite secant. For ordered unit edge tangents `T_i`,

```text
Delta theta_i = signed_angle(T_i,T_(i+1)),
sum_i Delta theta_i = 2*pi*rotation_index.
```

In the smooth planar limit,

```text
d theta = kappa ds = ds/r_curvature.
```

This is the exact local `C/r` specialization: `r` is the declared radius of curvature or another
explicit rotational radius. A projected crossing does not change the tangent unless the edge word
or a material joint redirects the current. Fixed-plane rotations commute; noncommuting gyration
requires a changing basis, pole, tangent plane, or higher-dimensional transport.

## 4. One face carries many triangular interiors

Every convex `n`-gon triangulation has

```text
n-2 triangles and n-3 internal diagonals.
```

There are `Catalan_(n-2)` such triangulations: two for a quadrilateral and fourteen for a hexagon.
A diagonal flip inside one quadrilateral is the elementary move between neighboring
triangulations. The flip graph is the one-skeleton of the associahedron. It holds the exterior face
fixed while changing the ordered binary composition of its interior.

This is a direct mathematical model for equal endpoint face with different practiced construction.
The associahedron does not make the paths identical; it records lawful local transformations among
them. If additional transported labels, axes, or noncommuting deeds ride the triangles, a loop of
flips may leave a consequential residual even when the coarse triangulation returns.

## 5. The MathWorld hexagon and quadrilateral are local operators

For cyclic hexagon vertices `v_i`, completing the parallelogram on each consecutive triple gives

```text
p_i = v_i - v_(i+1) + v_(i+2).
```

The alternating `p_i` form two congruent triangles. One local three-point difference operator,
applied around the complete six-cycle, therefore exposes a global parity invariant. The centroid
hexagon is the complementary averaging face: local centroid construction produces opposite sides
which are equal and parallel.

For a convex quadrilateral with oriented boundary vectors `a+b+c+d=0` and diagonal vectors `p,q`,

```text
area = (1/2) abs(p wedge q).
```

The closed wave supplies the boundary relation; two transverse diagonal strings supply its sheet
measure. A butterfly requires the oriented/signed face rather than silently adding absolute lobe
areas.

Projective conic incidence supplies the perspective control. For six points on a conic, the three
intersections of opposite side secants are collinear (Pascal). Dually, for a hexagon made from six
conic tangents, its three opposite-vertex diagonals concur (Brianchon). Metric face changes do not
erase those transported incidences.

## 6. Consequence for CONSTRAINT-DEED WORLD 01

The ratified construction gains a polygon-incidence front cell before the algebraic family:

1. hold one vertex palette while changing edge word;
2. retain source vertices, projected crossings, crossing preimages, material joints, edge segments,
   complementary faces, winding layers, and tangent turns separately;
3. enact quadrilateral flips and the two arbitrary-hexagon local operators;
4. transport the same body through a projective conic chart;
5. return exact reachability, winding, face, Pascal-collinearity, and Brianchon-concurrence
   consequences; and
6. let genuinely later questions distinguish equal silhouettes and collapsed endpoint faces.

This remains world physics and listener instrumentation. No polygon, triangle, winding class,
associahedron, or projective category enters Soma.

## 7. Queued arithmetic question — what grows when a prime FOUNDs?

The question is well posed after replacing “the associahedron” with “the emergent derivation
complex and its associahedral strata.” A numeral or glyph is one material face. In the external
prime-valuation chart,

```text
V(n) = (v_2(n),v_3(n),v_5(n),...),
V(ab)=V(a)+V(b).
```

A prime is one unit basis ray; a composite is a finite sum of rays. For an ordered word of `m`
already-founded factors, the alternative parenthesizations form an associahedron. Reordering
independent divisor tests is permutohedral rather than associahedral. Locality restrictions can
produce graph-associahedral or more general stratified cells.

At a newly founded prime `p`, there is no nontrivial multiplication word whose leaves are smaller
positive nonunits and whose face is `p`. The positive factorization stratum therefore degenerates;
the lived construction is the completed family of divisor exclusions through `sqrt(p)`. A prime is
not “an associahedron.” Its founding is a boundary event in a larger arithmetic derivation complex:
all admitted nontrivial factor branches remain open or refused while a new valuation direction is
deposited.

This yields the later research question:

> For nested horizons `B_N`, what exact polyhedral/cellular complex is induced by Soma's native
> factor, exclusion, addition, multiplication, and exponentiation histories; which cells are
> associahedra or permutohedra; and what transported spectrum is carried when a new irreducible axis
> FOUNDs?

Only after that finite complex, its weights, its operator, its pairing, and its horizon transport
are defined can a zeta or self-dual-locus receiver be constructed. A dynamical or incidence zeta is
not thereby the Riemann zeta, and no finite half-rank face is a classical RH result.

## 8. Open extension — the factor palindrome surrounds the founded axis

**STATUS: BRANDON SEED / SOL REFINEMENT / OPEN RESEARCH SUCCESSOR / NOT FORMULA / NO ENGINE CLAIM**

The palindrome intuition has an exact finite arithmetic body. Write

```text
n = product_i p_i^(alpha_i).
```

Every divisor corresponds to one exponent vector

```text
beta in D(n) = product_i {0,1,...,alpha_i}.
```

Factor pairing `d <-> n/d` is the central involution

```text
beta <-> alpha - beta.
```

Thus the rank-generating word

```text
P_n(t) = product_i (1+t+...+t^(alpha_i))
```

is genuinely palindromic:

```text
t^Omega(n) P_n(t^(-1)) = P_n(t),
Omega(n) = sum_i alpha_i.
```

Its mirrored coefficients count divisors at complementary total exponent ranks. This is the
rigorous elementary shape behind stacking factor palindromes. Parenthesizations of an ordered leaf
word add associahedral strata; reorderings add permutohedral strata; neither is the divisor box
itself. Pascal-like coefficient convolution is relevant here, while Pascal's conic theorem remains
the separately typed projective incidence law measured by the polygon receiver.

For a prime `p`, `D(p)={0,1}` has no nontrivial interior divisor. In a positive-nonunit factor
projection, the multiplication cell is therefore absent. In the larger valuation body, the same
event FOUNDs a new unit direction `e_p`. These are not contradictory readings: the hole belongs to
the prior factorization projection; the new axis belongs to the expanded chart. Powers `p^k` then
extend the exponent ladder on that axis, while all multiples of `p` occupy the region `v_p(n)>=1`.
Calling that region a diagonal is a possible display face, not its invariant arithmetic type.

Across a finite successor horizon `B_N`, consecutive primes also bound every intervening composite
on the additive number-line chart. Those forward/backward gap distances are real, but they are not
the same coordinates as valuation rank. A useful arithmetic atlas must retain both and record the
actual addition, multiplication, factor-exclusion, and exponentiation events transporting between
them.

The zeta connection is exact at one important face. In its standard half-plane of absolute
convergence,

```text
zeta(s)
  = sum_(n>=1) exp(-s log n)
  = product_p sum_(k>=0) exp(-s k log p)
  = product_p (1-p^(-s))^(-1).
```

Each Euler factor is precisely the infinite exponent ladder of one founded prime direction. The
Dirichlet coefficients of `zeta(s)^2` count divisor pairs, and those of `zeta(s)^k` count ordered
`k`-factor products. This makes zeta a lawful weighted quotient of the stacked factor-combination
population. It does **not** yet make a rendered empty region a zeta zero or make its Euclidean
volume an arithmetic invariant.

To make Brandon's cavern literal, the receiver must name:

```text
finite horizon B_N
ambient cell family A_N
realized factor/exclusion subcomplex F_N
embedding and rank/scale chart
cell weight or measure mu
boundary and gluing law
```

Only then can a deficit such as `mu(A_N \ F_N)`, a homological cavity, or a spectral mode be
distinguished. Those are three different receiver faces. The most useful next question is not to
draw a cavern first, but to let actual factor and exclusion deeds grow `F_N`, retain every refused
branch, and ask which weighted transfer operator carries the population coherently from `B_N` to
`B_M`.

The Smith/periplus bridge remains conditional. A factor-deed cell can acquire a Smith coordinate
only after a port, reference plane, input/output ratio, pole, and transport law are defined. A
revolved chart can then render its scale/rank response as a local volume; it may not author the
factor complex. Likewise, decimal, binary, and prime-valuation expressions are different exact
faces of one integer. Decimal may be shorter than binary in glyph count, but neither is an absolute
compression hierarchy: each face owes its base, alphabet, cost, and reconstruction map.

The construction question carried forward is therefore:

> What finite stratified factorization complex grows from the machine's actual multiplication,
> exponentiation, addition, and divisor-exclusion paths; where do missing nontrivial factor cells
> FOUND new valuation axes; and which boundary-indexed weighted transfer operator turns the stacked
> palindromic divisor populations into a zeta-like spectral face without erasing additive prime
> gaps, operation order, or horizon provenance?

## 9. Construction refinement — Pascal lift, prior-chart cavern, and exact response

**STATUS: SOL DERIVATION FROM BRANDON'S SEED / FINITE WORLD CONSTRUCTION AUTHORIZED / NOT FORMULA / SOMA INTERIOR UNCHANGED**

The Pascal relation is exact when a genuinely new prime direction enters a factor body. If
`p` does not divide `n`, then

```text
D(np) = D(n) x {0,1},
P_(np)(t) = (1+t) P_n(t).
```

Coefficientwise, each old rank contributes once to its old rank and once to the next rank. For a
square-free product of `k` distinct founded axes this gives

```text
P_n(t) = (1+t)^k,
```

so its divisor-rank population is literally one Pascal row. Reusing an existing axis is a different
deed. If `v_p(n)=a`, passing from `n` to `np` appends the outer layer `beta_p=a+1`; it does not
pretend that a duplicate prime is a fresh binary axis. The world receipt must therefore retain
fresh-axis lift and existing-axis extension separately.

The finite dynamic body at successor horizon `B_N={1,...,N}` is:

```text
H_(m-1)       founded prime axes before candidate m,
T_m           every p in H_(m-1) with p^2 <= m,
C_m           {p in T_m : p divides m},
E_m           T_m \ C_m.
```

If `C_m` is empty after all of `T_m` has passed, `m` FOUNDs a new axis. If `C_m` is nonempty, `m`
RIDEs standing multiplication closure. The exact factorization and every divisor complement then
grow the divisor box. This is the elementary localized solve: no candidate is guessed prime and no
probability selects a divisor. The complete exclusion frontier is the certificate at the declared
horizon.

The word *cavern* now has three typed readings which may not be collapsed:

1. **Prior-chart absence:** a prime has no nontrivial positive-factor 2-cell produced by axes which
   stood before it. This is the exact arithmetic hole used by the FOUND deed.
2. **Additive gap:** consecutive founded primes bound an interval on the number-line chart. Its
   length is real but is not valuation rank or a topological volume.
3. **Cellular cavity:** nontrivial homology of a declared glued factor complex. This must be
   computed from an exact boundary map; it may not be inferred from a sparse rendering.

The first construction measures the first two and does not claim the third. It places the additive
backbone beside multiplicative triangles `(a,b,ab)`. A prime remains on the additive backbone while
lacking a nontrivial incoming multiplication triangle; after FOUNDing, later multiples attach
outward along its new valuation direction. That is the rigorous finite face of the radial-unfolding
intuition.

Brandon's two-handed equation makes the local missing cell explicit. For every realized
nontrivial integer factor cell on either side of prime `P`, retain

```text
a*b + c = P = x*y - z,
c = P-a*b > 0,
z = x*y-P > 0.
```

There are indefinitely many following products as the horizon grows and many distinct operation
histories can share one product face. The bracketing equation alone does not classify `P`, because
every integer can be bracketed by other products. The prime incidence is the zero-residual absence

```text
{(a,b) in Z_(>1)^2 : a*b=P} = empty.
```

Thus the numeral `13` is not intrinsically primal. In the declared positive-integer world, the
vertex reached by that numeral has additive incidence and two-handed factor approaches but no
incoming nontrivial multiplication cell; that local face FOUNDs an axis. Changing the factor
domain is a genuine re-base rather than a display change: `13` is prime in `Z` but
`13=(3+2i)(3-2i)` in the Gaussian integers. A complex-plane rendering which retains integer factors
preserves the first face; admitting Gaussian factors changes the arithmetic body.

For consecutive primes `P_j<P_k`, every interior integer has exact two-handed additive coordinate

```text
P_j+n = N = P_k-m,
n+m = P_k-P_j.
```

The twin-prime case is the minimal sheet:

```text
P_k-P_j=2  iff  interior={N} and [n:m]=[1:1].
```

Every larger gap between odd primes still has one midpoint with `n=m`; what distinguishes it is the
additional reflected off-center pairs with `n!=m`. Hence an asymmetric `N` is evidence that the gap
is larger than two, but `n!=m` is not the definition of a non-twin pair without quantifying the
whole interior.

There is also an exact exponent-lattice form of the finite zeta quotient. Let

```text
Lambda_N = {alpha with finite support : product_p p^(alpha_p) <= N}.
```

Unique factorization identifies `Lambda_N` with `B_N`, and therefore

```text
Z_N(s) = sum_(alpha in Lambda_N) exp(-s <alpha,log p>)
       = sum_(n<=N) n^(-s).
```

As the horizon grows, the standard Euler product is recovered in its ordinary half-plane of
absolute convergence. The product's independent prime ladders are clipped by the finite-horizon
surface `product p^alpha <= N`; multiplying independently truncated ladders without that surface
would manufacture out-of-horizon combinations. The reciprocal product

```text
1/zeta(s) = product_p (1-p^(-s)) = sum_n mu(n)n^(-s)
```

is the direct inclusion/exclusion and cancellation face. Neither expression turns a prime gap into
a zeta zero, and analytic continuation is a later receiver rather than an implicit property of a
finite drawing.

For each candidate, the first projective response instrument carries the exact homogeneous pair

```text
h_m = [ |C_m| : |E_m| ].
```

Where `|T_m|>0`, its Cayley face is

```text
gamma_m = (|C_m|-|E_m|)/(|C_m|+|E_m|).
```

`gamma=-1` means the complete tested frontier excluded every standing divisor; it does not alone
mean prime unless the frontier is complete. `gamma=+1` means every tested founded divisor divides
the candidate, not a universal match. The complete sets, candidate, horizon, and factorization
remain beside the quotient. This is a lawful projective response chart analogous in form to a Smith
quotient; it is not electrical impedance and does not enter Soma.

The additive prime-gap sheet has its own exact projective coordinate. For interior `N`, carry

```text
h_N=[n:m],
gamma_N=(n-m)/(n+m)=(2N-P_j-P_k)/(P_k-P_j).
```

The midpoint has `gamma=0`; reflection about the midpoint exchanges the two hands and sends
`gamma` to `-gamma`. The gap skeleton is therefore palindromic even when the divisor palindromes
stacked at reflected integers differ. Twin primes supply one centered composite layer; a larger
gap supplies a centered layer plus reflected off-center layers. This is the first exact bridge from
prime-gap geometry to a revolvable projective response surface. It remains distinct from the
factor-frontier quotient above and from literal transmission-line impedance.

The exact loss is likewise plural. Before closure it is the remaining untested divisor frontier;
after closure it is either the retained factor/exclusion family or the unsupported prime axis which
must be founded. Later multiples of that axis measure ecological compression by consequential
reuse. Boundary-indexed prime/composite recurrence and symbolic `-log2(p)` may be read afterward,
but they neither decide the FOUND deed nor erase the operation path.

The implementation cut is one separate world transducer which returns, for every `m<=N`:

- ordered standing-prime tests, contacts, and exclusions;
- exact valuation word, divisor complement pairs, palindromic rank polynomial, and all fresh-axis
  or existing-axis lifts from `m/p`;
- previous/next founded-prime distances in the additive chart;
- exact decimal, binary, valuation, additive-rank, and multiplicative-rank faces without declaring
  one absolute compression winner;
- homogeneous response and Cayley quotient when defined; and
- later reuse of each newly founded axis inside the same finite horizon.

No horizon constant is installed in Soma or the transducer. The world supplies `N`; checked memory
and integer extents preflight the complete return or refuse it whole.

## 10. Measured refinement — the rank shell is not the explicit face

FACTOR-PALINDROME WORLD 01 confirms the arithmetic construction and exposes an important receiver
failure. The complete horizon was serialized twice inside one 4,206,415-octet current because one
recurrent path contacted the same exact record at two physical source coordinates. Soma retained
the two histories lawfully, but the receiver repeated the entire derived face rather than sharing
that face and carrying two incidences. The result was 775.540 seconds of CUDA carriage and a body
increase from 1.10 GB to 6.45 GB. No return-world contact occurred. The exact record is
`observations/factor-palindrome-world-01/RESULTS.md`.

The missing compression distinction is radial rank versus lateral identity. For valuation vector
`alpha=(v_p(n))`, define

```text
rho(alpha)=sum_p alpha_p,
D_alpha={beta : 0<=beta_p<=alpha_p},
P_alpha(t)=product_p(1+t+...+t^(alpha_p)).
```

`[t^r]P_alpha` is the population on the rank-`r` shell. It is an annular quotient in the precise
sense relevant here: it retains radial rank and forgets which lateral valuation coordinate
`beta` supplied the cell. Multiplication by a fresh prime `q` performs

```text
P_(alpha+e_q)(t)=(1+t)P_alpha(t),
```

so Pascal's two hands either remain at rank `r` or arrive at `r+1`. A diagonal rank passage can be
the shortest climb under a declared generator cost, while an explicit divisor or integer face
still requires lateral movement. Neither direction is absolutely fastest without a named
operation set and physical cost.

At a founded prime `q`, the positive-integer product chart has no incoming nontrivial factor cell.
The local absence founds a new valuation direction; later products then carry that axis. This is
the arithmetic singularity/curvature statement supported by the receiver. It does not identify a
prime as a geometric point independent of factor domain: for example, a Gaussian-integer re-base
can split an integer-prime face.

A decimal ending supplies another lawful chart section. At horizon `N`,

```text
A_(10,3;N)={p<=N : p is prime FOUND and p congruent to 3 mod 10}
```

threads one receiver-relative fiber through the founded axes. It is not an intrinsic universal
prime axis: changing base changes the glyph section. Within the decimal unit residues, however,
multiplication, additive gaps, rank shells, and later reuse meet that section at exact
intersections. It is therefore the first concrete query for the compressed successor.

The successor returns generators and incidences rather than the derived monolith: each divisor
deed, factor cell, prime FOUND, axis lift, and gap boundary stands once; exact material coordinates
and ordered ancestries remain plural edges; approaches, later multiples, rank populations, and
requested glyph faces are reconstructed at the receiver. Exact face sharing is not dimensional
cancellation. It preserves the face and every distinct path which arrives there.

That successor is now built and CUDA-forward measured. The exact durable 5,132,512-byte journal
and SHA remain unchanged, while one shared horizon face plus two material incidence currents reduce
active light from 4,244,319 to 216,088 octets. CUDA carriage falls from 775.540 to 4.793 seconds,
radiation from 662,114,580 to 33,719,744 bytes, and successor-body growth from 5,352,759,648 to
292,805,624 bytes. The 1,148-event sheet reconstructs the complete ordered horizon exactly.

A later exact `3 mod 10` prime-section consequence returned byte-identically through fresh and
arithmetic-exposed bodies. Only the exposed body makes a world contact. The contacted joint is not
an anonymous count: it was occupied by candidate 40's exact divisor frontier `2 contact / 3
exclusion / 5 contact`, and later joins candidate 31 to its receipt. The requested residue-outcome
current itself remains unselective because every human-readable JSON event repeats the same field
names and punctuation. The next world cut therefore carries one schema header and typed event
values instead of repeating textual keys; the exact JSON journal remains durable. This is a
receiver ABI refinement and changes no Soma interior law. Exact measurement:
`observations/factor-palindrome-world-01/RESULTS.md`.

## Evidence cards

### Card A — arbitrary hexagon operators

```text
SOURCE ESTABLISHES  MathWorld's Hexagon entry states that consecutive-triple parallelogram
                    completion yields two congruent alternating triangles, and consecutive-three-
                    side centroids yield a hexagon with equal parallel opposite sides.
LAB CLAIM           §§LXXX-LXXXI: a local operation word can expose a transported invariant only
                    after the complete incidence cycle; RATIFIED / NO SOMA INTERIOR CHANGE.
RELATION            DIRECT CORRESPONDENCE. The local affine operator and its alternating global
                    consequence supply an exact world species for the broader laboratory law.
NON-EQUIVALENCE     The operator is not a Soma mechanism and does not make all sixfold bodies one
                    category.
TESTABLE CONSEQUENCE Reorder the same six vertices or change one local operator; retain the face
                    palette and compare the complete alternating triangle consequences.
```

Source: Eric Weisstein, [“Hexagon,” MathWorld](https://mathworld.wolfram.com/Hexagon.html),
construction paragraphs following the definition.

### Card B — quadrilateral wave and sheet

```text
SOURCE ESTABLISHES  MathWorld distinguishes convex, concave, and crossed/butterfly quadrilaterals;
                    for a convex quadrilateral it gives boundary-vector closure and area as one
                    half the diagonal cross product.
LAB CLAIM           §LXXXI: boundary wave, projected crossing, admitted joint, and oriented filling
                    are typed faces; RATIFIED / NO SOMA INTERIOR CHANGE.
RELATION            EXACT FORMAL MATCH for a+b+c+d=0 and area=(1/2)|p wedge q| at the declared
                    planar convex grain; DIRECT CORRESPONDENCE for the typed butterfly control.
NON-EQUIVALENCE     The unsigned convex-area formula may not be imported as the signed butterfly
                    filling, and a display crossing is not automatically a material joint.
TESTABLE CONSEQUENCE Hold the four source vertices, vary convex/concave/crossed edge embeddings,
                    and compare path graph, display faces, winding, and signed area separately.
```

Source: Eric Weisstein, [“Quadrilateral,” MathWorld](https://mathworld.wolfram.com/Quadrilateral.html),
definition and equations (3)-(4).

### Card C — star edge word and triangulation population

```text
SOURCE ESTABLISHES  MathWorld defines {p/q} by every-qth-point connection, factors non-coprime
                    words into multiple components, and records Catalan-many polygon
                    triangulations and the concurrency boundary for regular diagonal arrangements.
LAB CLAIM           §LXXXI: the edge word and interior triangulation are lived constructions not
                    determined by the shared point palette or exterior face; RATIFIED.
RELATION            EXACT FORMAL MATCH for gcd component count, chord construction, and Catalan
                    triangulation population; STRUCTURAL RESONANCE between flip topology and
                    practiced mathematical derivation paths.
NON-EQUIVALENCE     A classical associahedron does not encode Soma, primality, or a zeta spectrum.
TESTABLE CONSEQUENCE Enumerate exact edge words and diagonal flips over one fixed vertex set and
                    compare which native paths preserve face, circuit, winding, and later conduct.
```

Sources: Eric Weisstein, [“Star Polygon,” MathWorld](https://mathworld.wolfram.com/StarPolygon.html)
and [“Polygon Diagonal,” MathWorld](https://mathworld.wolfram.com/PolygonDiagonal.html).

### Card D — planar turning

```text
SOURCE ESTABLISHES  Whitney's 1937 paper assigns regular closed plane curves a rotation number from
                    total tangent turn and relates it to algebraically counted self-crossings.
LAB CLAIM           §LXXXI: the planar polygon supplies the zero/nonzero-turn control for time-
                    coupled periplus; RATIFIED / NO SOMA INTERIOR CHANGE.
RELATION            DIRECT CORRESPONDENCE at the oriented planar-curve grain.
NON-EQUIVALENCE     Whitney rotation number is not physical time, a higher-dimensional connection,
                    Soma's K, or an RH quantity.
TESTABLE CONSEQUENCE Refine polygonal secants toward one smooth curve and verify convergence of
                    signed vertex turns while projection-only crossings leave path ancestry plural.
```

Primary source: Hassler Whitney, [“On regular closed curves in the plane,” *Compositio Mathematica*
4 (1937), 276-284](https://www.numdam.org/item/CM_1937__4__276_0/).

### Card E — projective secant/tangent duality

```text
SOURCE ESTABLISHES  Pascal's theorem gives collinearity of opposite-side intersections for an
                    inscribed conic hexagon; Brianchon's dual gives concurrence of opposite-vertex
                    diagonals for a circumscribed conic hexagon.
LAB CLAIM           §§LXXX-LXXXI: transported incidence may survive changed perspective while
                    metric face changes; RATIFIED.
RELATION            EXACT FORMAL MATCH for the declared projective conic world.
NON-EQUIVALENCE     Projective incidence does not establish material contact, causal transport, or
                    a universal physical hexagon law.
TESTABLE CONSEQUENCE Apply exact projective maps and controlled degenerations from secants toward
                    tangents; verify incidence while retaining every source and limiting path.
```

Sources: [“Pascal's Theorem,” MathWorld](https://mathworld.wolfram.com/PascalsTheorem.html) and
[“Brianchon's Theorem,” MathWorld](https://mathworld.wolfram.com/BrianchonsTheorem.html).

## Carried-Swing record

```text
CURRENT  ordered boundary wave -> incidence/joint field -> winding fill -> swept sheet -> receiver face
HELD     first axiom + A2 + partial(partial)=0 + C/r + time parity + §§LIII/LXX-LXXX
MEETING  cube f-vector + butterfly + annulus + n-gram + triangulations + conic duality + prime horizon
TEST     same palette/different edge word + projection/contact split + flip + projective transport + repeat
DEED     RIDE transported incidence; FOUND changed circuit, joint, winding, or irreducible axis
CARRY    polygon-incidence front -> constraint-deed family -> arithmetic derivation-complex inquiry
GRADE    RATIFIED / DEPOSITED AS FORMULA §LXXXI / NO SOMA INTERIOR CHANGE
```
