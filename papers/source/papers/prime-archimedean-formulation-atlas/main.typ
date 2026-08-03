#import "../../lib/elements.typ": *
#import "../../mathematics/catalogue.typ": elements
#import "figures.typ": *

#show: elements-paper.with(
  title: [A Prime--Archimedean Formulation Atlas],
  subtitle: [Valuation simplices, constant-producing paths, situated surfaces, and the completed zeta seam],
  authors: [Brandon Duggan and Sol],
  date: [23 July 2026 -- first exact atlas cut],
  abstract: [
    This paper constructs the prime--archimedean formulation atlas requested
    by the laboratory.  It is not a gallery of formulas grouped only because
    they return the same scalar.  Its horizontal geometry is the exact
    exponent lattice of finite prime places: degree fibers are integer
    simplices, degree-preserving moves form the root lattice $A_(r-1)$, and
    prime powers are repeated traversal of primitive axes.  Its vertical
    geometry consists of declared formulation changes: Gaussian
    factorization and arctangent addition for $pi$; factorial valuations,
    limits, continued fractions, differential flow, and the exponential
    cover for $e$; and Fourier--Poisson--Mellin completion for zeta.  The
    finite and archimedean directions already meet exactly in the product
    formula for rational numbers and, analytically, in the completed zeta
    function.  A bounded exact construction now resolves every term of
    three arctangent arms and one Chudnovsky recurrence into named factor
    channels, signed divisors, internal annihilation, additive
    cancellation, and the surviving partial-sum face.  It shows that a
    recurrence is a moving carrier rather than a retained factor archive,
    and that equal transcendental return does not conserve one finite-prime
    support.  A pathwise Riemannian mean-transport lemma supplies the
    complementary continuous law: smooth deformation integrates within a
    situated path, while branch, rank, phase, and valuation seams contribute
    explicit discrete terms.  A second bounded exact construction joins
    transformed-grid germs, completed-zeta symmetry, logarithmic rebase, and
    centered Smith incidence.  It distinguishes a regular crossing, zero,
    critical branch, and distinct-source coincidence; derives $1/2$ as the
    fixed projector of $s mapsto 1-overline(s)$; and carries the same signed
    normal coordinate as circle-versus-spiral conduct and unit-shell
    displacement, without floating evaluation.  A third bounded exact
    construction turns the reciprocal Smith pair into one moving chord.  It
    carries the chord's complex-plane intersection, oriented axis, two pole
    paths, common and coupling metrics, and triangular holonomy separately.
    Exact rational precession moves both the intersection and the
    stereographic direction by one complex phase; a coupled edge produces
    an oriented pole imbalance which reverses under pole exchange.  A
    conic-pencil discriminant remains a separate typed seam.  A further purpose is to
    explain why Wolfram MathWorld's ray-traced mathematical objects are
    germane.  The Bowl of Integers,
    Cayley cubic, Chen--Gackstatter family, and Klein quartic each place a
    compact local law inside a globally nontrivial orbit, singularity,
    period problem, or quotient.  Ray tracing is formalized as a situated
    receiver rather than an outside camera.  The image testifies about one
    real affine cut while concealing other roots, complex and projective
    faces, interior sheets, and resolutions.  The paper ends at one precise
    Riemann-Hypothesis edge: the local charts now agree exactly that a
    nontrivial zero mode is on the critical seam iff its normal exponent
    vanishes, its rebase is unitary, and its Smith image lies on the unit
    shell.  The remaining global construction must exclude every nontrivial
    off-shell zero mode while covariantly retaining completed response,
    adjoint, boundary, and holonomy.  The contribution is an exact census, a
    concrete two-direction atlas, several nontrivial populated cells, and a
    bounded program for that transport law.
  ],
)

#outline(
  title: [Contents],
  depth: 3,
  indent: auto,
)
#pagebreak()

= The question and the object constructed

The present question is not whether $pi$, $e$, prime numbers, and attractive
surfaces “look related.”  It is whether their distinct formulations expose
reusable transformation laws once the identity of each path, its receiver,
and its unresolved residual are retained.

The standing evidence was insufficient in two ways.  Earlier exact
experiments counted prime-power apertures and bounded formula families, but
they did not place those counts into one closed combinatorial geometry.
Earlier Riemann work assembled Euler, theta, Mellin, and Weil faces, but it
did not populate the vertical formulation direction with the concrete
$pi$--$e$ cells or formalize a visual observation as a receiver event.

#construction-card(
  title: [The atlas constructed in this paper],
  problem: [
    Keep the exact prime composition of a formulation while allowing its
    analytic, algebraic, geometric, or rendered face to change.  Determine
    which squares commute, which expose a residual, and what extra structure
    an RH-bearing square would have to preserve.
  ],
  diagram: block(
    width: 100%,
    fill: white.transparentize(25%),
    stroke: 0.5pt + by-rule,
    inset: 9pt,
  )[
    #align(center)[
      #text(size: 8.2pt, fill: by-blue, weight: "semibold")[prime-axis transport]
      #linebreak()
      #text(size: 11pt, fill: by-blue)[↔]
      #linebreak()
      #text(size: 8.2pt, weight: "semibold")[formulation occurrence]
      #linebreak()
      #text(size: 11pt, fill: by-yellow)[↕]
      #linebreak()
      #text(size: 8.2pt, fill: by-yellow, weight: "semibold")[receiver change]
      #linebreak()
      #v(3pt)
      #text(size: 7.2pt, fill: by-open)[commuting cell or explicit residual]
    ]
  ],
  demonstration: [
    The horizontal fibers are the exact valuation simplices
    $Delta_(S,d)$.  Their transitions are inclusions of prime support and
    degree-preserving $A_(r-1)$ transfers.  Vertical transitions include
    Gaussian norm and argument, logarithm and exponential, Fourier and
    Poisson, Mellin and Gamma completion, quotient maps, and situated
    renderings.  A cell closes only when both paths return the same addressed
    occurrence with the same declared structure.
  ],
  algebra: [
    $
      (S,alpha,F)
      arrow.r^("prime")
      (T,beta,F')
      quad "and" quad
      (S,alpha,F)
      arrow.r^("formulation")
      (S,alpha,G).
    $
    The square compares “prime then formulation” with “formulation then
    prime.”  Its residual is the difference between those two composite
    transition laws, not the difference between two rounded output digits.
  ],
  conclusion: [
    Equal returned values do not erase nonidentical paths.  Conversely, a
    visually different face need not be a different intrinsic object.  The
    atlas retains both statements at once.
  ],
)

The stopping condition for this cut is a populated, proof-auditable atlas
with an exact next RH-bearing question.  No Soma engine run and no image
mining are part of the construction.

== Claim grades

#table(
  columns: (10.2em, 1fr),
  inset: (x: 5pt, y: 4pt),
  stroke: (x: none, y: 0.4pt + by-rule),
  table.header([*Grade*], [*Use in this paper*]),
  [Classical identity], [
    Factorization, stars and bars, the product formula, Gaussian norms,
    arctangent addition, Fourier/Poisson/Mellin transport, and the standard
    surface invariants are used under their ordinary hypotheses.
  ],
  [Exact laboratory synthesis], [
    Several classical objects are placed in one two-direction atlas, and the
    exact prime-axis interior of selected $pi$--$e$ formulations is retained.
  ],
  [Bounded measurement], [
    Earlier finite observations through prime $509$, the 82 prime-power gears
    through $313$, and the degree-two and degree-three formula apertures are
    recounted only inside their declared cutoffs.  The exact
    presentation-topology cut additionally carries 12 terms of each
    arctangent arm and eight Chudnovsky terms as complete
    divisor-and-accumulation paths.  The conformal-rebase cut carries four
    exact local germs, one retained distinct-preimage coincidence, four
    completed-zeta orbits, four log-polar rebase paths, and four centered
    Smith rows.  The moving-chord cut additionally carries one exact Smith
    tilt and precession, three pole-edge foils, two induced sheet metrics,
    one flat and one curved connection face, and four conic-pencil phases.
    Those populations establish their local laws, not a global zero census.
  ],
  [Open construction], [
    Covariant all-probe completed transport is the remaining proof-bearing
    relation.  It must retain response, adjoint, boundary, and holonomy
    while excluding off-shell nontrivial zero modes.
  ],
)

= The finite-prime geometry

== Prime support is an exponent lattice

#object-entry(elements.prime_valuation_atlas)

The definition changes the question “Which numbers are near this prime?”
into a more precise family of questions.  Nearness may mean one
degree-preserving root move, one residue step, one continued-fraction rebase,
one analytic amplitude ratio, or one path admitted by a particular
receiver.  These are not interchangeable metrics.

For fixed $S={p_1,dots,p_r}$, unique factorization gives an exact coordinate
chart
$
  n arrow.l.r
  nu_S(n)=(v_(p_1)(n),dots,v_(p_r)(n)).
$
The prime $p_j$ is the primitive axis $e_(p_j)$; the power $p_j^m$ is the
address $m e_(p_j)$; a semiprime $p_i p_j$ is the mixed address
$e_(p_i)+e_(p_j)$.  “Irreducible” is therefore a statement about the
boundary of the positive monoid: a prime occupies a primitive degree-one
vertex, while its later powers and products emanate along higher-degree
fibers.

== Exact group counts per prime axis

#object-entry(elements.prime_simplex_census)

This theorem supplies the group count previously missing from the prime
observations.  With three active axes,
$
  abs(Delta_(S,1))=3,
  quad
  abs(Delta_(S,2))=6,
  quad
  abs(Delta_(S,3))=10.
$
The degree-three fiber has three pure cubes, six $[2,1]$ forms, and one
full-support product.  These are not empirical pattern classes; they are the
permutation orbits of weak compositions of $3$.

#valuation-simplex-figure()

For general degree $d$, the symmetric group on the active prime axes
partitions the simplex by integer partitions of $d$ having at most $r$
parts.  Thus
$
  d=2:
  quad [2], [1,1],
$
and
$
  d=4:
  quad [4], [3,1], [2,2], [2,1,1], [1,1,1,1].
$
The orbit label records exponent shape while the chosen axes record its
address.  This is one precise sense in which prime-related shapes recur
self-similarly without making every instantiation identical.

== The measured finite aperture

The bounded prime-spectral observation through $313$ exposed 82
prime-power gears.  The per-axis multiplicities were:

#table(
  columns: (1.15fr, 1fr, 1.9fr),
  inset: (x: 5pt, y: 4pt),
  stroke: (x: none, y: 0.4pt + by-rule),
  table.header([*Prime axes*], [*Powers admitted*], [*Exact reason*]),
  [$2$], [$8$], [$2^1,dots,2^8 <=313<2^9$],
  [$3$], [$5$], [$3^1,dots,3^5 <=313<3^6$],
  [$5$], [$3$], [$5^1,5^2,5^3 <=313<5^4$],
  [$7,11,13,17$], [$2$ each], [$p^2<=313<p^3$],
  [58 other primes $<=313$], [$1$ each], [$p<=313<p^2$],
)

For a cutoff $X$, the exact aperture on one axis is
$
  a_X(p)=max{m:p^m<=X}=floor(log_p X).
$
Summing $a_X(p)$ counts prime powers without weight.  Weighting each
occurrence by $log p$ gives the Chebyshev current
$
  psi(X)=sum_(p^m<=X) log p.
$
The earlier scalar “82” is therefore only the cardinality of a complete
path population.  The atlas keeps which axis repeated, how many times it
repeated, and which logarithmic displacement it contributes.

== Residue loops are a different fiber

The valuation chart is multiplicative.  A residue chart about a prime axis
$p$ has different exact populations:
$
  abs(ZZ/p ZZ)=p,
  quad
  abs((ZZ/p ZZ)^times)=p-1,
  quad
  abs(hat((ZZ/p ZZ)^times))=p-1.
$
Adding a new prime $p$ to a primorial wheel multiplies the surviving unit
population by $p-1$.  The measured wheel sizes
$
  1,2,8,48,480
$
for moduli
$
  2,6,30,210,2310
$
are exactly Euler's totient values.  They count compatible residue
positions, not the exponent addresses in $Delta_(S,d)$.  The atlas relates
these fibers through declared reduction maps instead of collapsing them into
one notion of “prime geometry.”

= Horizontal transport: roots, fractions, and recurrence

== Degree-preserving prime moves

#object-entry(elements.prime_axis_root_closure)

The transfer $e_p-e_q$ removes one unit of exponent from the $q$ axis and
adds one to the $p$ axis whenever the source address permits it.  In a fixed
degree simplex these moves traverse the adjacency graph.  A fraction $p/q$
is therefore not an illicit float; it is an oriented valuation edge with
address $e_p-e_q$.

Under
$
  Phi_s(alpha)=product_p p^(-s alpha_p),
$
that exact combinatorial move has analytic face
$
  Phi_s(alpha+e_p-e_q)
  =
  (q/p)^s Phi_s(alpha).
$
For real $s=sigma>0$, the magnitude orders the move.  For complex
$s=sigma+i t$, the same edge also carries the phase
$
  exp(i t(log q-log p)).
$
The “probability-like” reading is consequently receiver-relative: the
address is exact, while the amplitude assigned to it depends on the
contemporary analytic parameter.

== Continued fractions are rebase words

A positive rational path
$
  x=[a_0;a_1,dots,a_k]
$
is an exact word in unimodular transformations
$
  z mapsto a+1/z.
$
Its convergents are related by matrices in $op("SL")(2,ZZ)$ up to the ordinary
orientation convention.  Thus a rational $p/q$ carries at least two
complementary faces:

- its valuation displacement $nu(p)-nu(q)$, and
- its ordered Euclidean-algorithm word.

One records multiplicative support; the other records a causal rebase
procedure.  Their returned rational agrees, but neither path reconstructs
the other without additional information.

== The flat triangle and the possible residual

Inside one valuation chart,
$
  (e_p-e_q)+(e_q-e_r)+(e_r-e_p)=0.
$
After analytic specialization with one fixed $s$, the product of the three
ratios is also one:
$
  (q/p)^s dot (r/q)^s dot (p/r)^s=1.
$
This is an exactly commuting triangular cell.  Curvature does not arise by
declaring the planar triangle “really higher-dimensional.”  It arises when
the transport changes a branch, receiver, completion, support, or boundary
condition along the loop.  The resulting holonomy must then be computed from
those transition laws.

= Vertical transport: formulations of $pi$ and $e$

== A formulation is a path, not merely its limit

Bailey's catalogue deliberately places polygonal iterations, arctangent
identities, infinite series, integrals, AGM algorithms, and digit-extraction
formulas side by side @bailey2021catalogue.  MathWorld records an even wider
family @mathworld-pi-formulas.  Their common value does not make their
interiors identical:

#table(
  columns: (1fr, 1.55fr, 1.55fr),
  inset: (x: 5pt, y: 4pt),
  stroke: (x: none, y: 0.4pt + by-rule),
  table.header([*Face*], [*Native recurrence*], [*Prime-sensitive interior*]),
  [Polygonal], [angle doubling and nested radicals], [powers of $2$ and chosen polygon order],
  [Machin-like], [Gaussian multiplication and argument addition], [norm factorizations and branch quadrant],
  [Euler product / $L$-value], [multiplicative local factors], [prime residue characters],
  [Ramanujan--Chudnovsky], [hypergeometric recurrence], [factorial valuations and modular parameters],
  [BBP-like], [base-specific digit extraction], [radix powers and residue denominators],
  [AGM], [quadratic mean iteration], [duplication, elliptic/modular structure],
)

The atlas does not need to assert that all such algorithms are one formula.
It asks for explicit vertical transitions where they exist and records an
open seam where they do not.

== A complete $pi$ cell: Machin through Gaussian factorization

The exact Gaussian identity
$
  (5+i)^4=2(1+i)(239+i)
$
can be verified in $ZZ[i]$:
$
  (5+i)^4=476+480i
$
and
$
  2(1+i)(239+i)=476+480i.
$
Taking arguments in the relevant first-quadrant branches gives
$
  4 arctan(1/5)-arctan(1/239)=pi/4.
$
Taking Gaussian norms instead gives
$
  N(5+i)=26=2 dot 13,
  quad
  N(239+i)=57122=2 dot 13^4.
$
The same identity therefore has an angle face and an exact finite-prime
interior on axes $2$ and $13$.  The appearance of those primes is not a
numerological scan of decimal digits; it is forced by factorization of the
Gaussian integers which carry the argument relation.

== A second $pi$ cell: a character field over odd primes

Let $chi_4$ be the nontrivial character modulo $4$.  For odd primes,
$
  chi_4(p)=(-1)^((p-1)/2)=sin(pi p/2).
$
Since $chi_4(p)^2=1$,
$
  1+chi_4(p)/p
  =
  (1-p^(-2))/(1-chi_4(p)/p).
$
Multiplying over odd primes gives
$
  product_(p>2)(1+chi_4(p)/p)
  =
  2/pi.
$
Equivalently,
$
  pi=3 zeta(2)/(2 L(1,chi_4)).
$
This cell relates $pi$ to the distribution of prime axes by residue
orientation.  Semiprimes retain a compositional sign:
$
  chi_4(p q)=chi_4(p)chi_4(q).
$
The semiprime is not noise between primes; it is the product path through
two local character responses.

== The $e$ family carries factorial prime currents

The standard faces of $e$ include the series, compound limit, continued
fraction, differential flow, and exponential map @mathworld-e:
$
  e=sum_(n>=0)1/(n!),
  quad
  e=lim_(n->infinity)(1+1/n)^n,
$
$
  e=[2;1,2,1,1,4,1,1,6,dots],
  quad
  y'=y, y(0)=1.
$
For the series current $a_n=1/n!$,
$
  a_(n+1)=a_n/(n+1).
$
The new denominator does not enter as one opaque integer.  Its prime-axis
address is $nu(n+1)$, and the accumulated denominator obeys Legendre's exact
law
$
  v_p(n!)
  =
  sum_(k>=1) floor(n/p^k).
$
Thus the factorial series traverses every prime axis when its powers occur
in the successor sequence.  Its return toward $e$ compresses those paths
into a contemporary approximation without making their recurrence
unavailable to a receiver which retains the series.

#formula-cell-figure()

== A series has a term current and an accumulation current

The preceding examples name prime factors inside formulas.  The next
question is stricter: how do those factors move while the formula is
actually evaluated?

For the arctangent family
$
  A(u/v)
  =
  sum_(n>=0)
  (-1)^n u^(2n+1)/(v^(2n+1)(2n+1)),
$
put
$
  a_n
  =
  (-1)^n u^(2n+1)/(v^(2n+1)(2n+1)).
$
Then
$
  r_n
  =
  a_(n+1)/a_n
  =
  -u^2(2n+1)/(v^2(2n+3)).
$
If $D_n=op("div")(a_n)$ is its signed rational prime divisor, the
transition is
$
  D_(n+1)-D_n
  =
  2 op("div")(u)-2 op("div")(v)
  +op("div")(2n+1)-op("div")(2n+3).
$

The odd factor is therefore a moving carrier.  The current face $2n+1$
returns on the numerator hand and departs while $2n+3$ enters on the
denominator hand.  The parameter $v^2$ supplies a persistent rail.  These
two currents collide at the exact modular sheets
$
  2n+1=0 mod p^k
  quad "or" quad
  2n+3=0 mod p^k,
$
for $p^k$ dividing $v$.  Since $2$ is invertible modulo every odd $p^k$,
each condition selects one residue class.  This is a parameter-relative
phase relation inside one recurrence species.

Term formation is still only one face.  With
$
  S_n=sum_(j=0)^n a_j,
$
the complete first-person transition is
$
  mat(a_(n+1);S_(n+1))
  =
  mat(r_n,0;r_n,1)
  mat(a_n;S_n).
$
For reduced $S=A/B$ and $a=C/D$, the accumulated successor is
$
  A/B+C/D
  =
  (A D+B C)/(B D)
  arrow.r^("g=gcd(A D+B C,B D)")
  ((A D+B C)/g)/(B D/g).
$
This gcd quotient is an exact outgoing compression event.  It removes
denominator directions which no longer factor into the sum while retaining
the reduced consequence.  It is distinct from cancellation between the
numerator and denominator channels of $r_n$.

#presentation-current-figure()

=== Exact bounded presentation-topology cut

The accompanying instrument carries 12 exact terms of $A(1)$,
$A(1/5)$, and $A(1/239)$, plus eight Chudnovsky summands.  Each event retains
named factor channels before reduction, both prime-valuation hands,
internal annihilation, the surviving signed divisor, the coupled term/sum
matrix, the additive gcd, and the next denominator divisor.  The complete
paths are deposited at
`observations/eros-transcendental-presentation-topology-01/REPORT.json`.

At the twelfth arctangent term the divisors are
$
  op("div")(a_11(1))=-[23],
$
$
  op("div")(a_11(1/5))=-23[5]-[23],
  quad
  op("div")(a_11(1/239))=-23[239]-[23].
$
All preceding odd faces have departed from the current term.  The received
partial sums retain different denominator topology:

#table(
  columns: (1fr, 1.3fr, 1.65fr),
  inset: (x: 5pt, y: 4pt),
  stroke: (x: none, y: 0.4pt + by-rule),
  table.header([*Path*], [*Internal recurrence cancellation*], [*Final partial denominator*]),
  [$A(1)$], [none], [$3^2 dot 5 dot 7 dot 11 dot 13 dot 17 dot 19 dot 23$],
  [$A(1/5)$], [$5^2$], [$3^2 dot 5^23 dot 7 dot 11 dot 13 dot 17 dot 19 dot 23$],
  [$A(1/239)$], [none], [$3^2 dot 5 dot 7 dot 11 dot 13 dot 17 dot 19 dot 23 dot 239^23$],
)

The $1/5$ arm crosses two fixed/moving $5$-axis collisions in this
aperture; the $1/239$ arm has not yet reached a moving odd multiple of
$239$.  This is why structurally identical recurrences have nonidentical
local annihilation.

Semiprime shapes are likewise local.  The fixed channel $5^2$ is a
$[2]$ face at every $A(1/5)$ transition, while an odd factor such as
$15=3 dot 5$ is a $[1,1]$ face.  A later channel coupling may remove part
of either.  “Semiprime” therefore addresses a channel, hand, and event
grain; it is not a label on the transcendental return.

=== Chudnovsky is the same carrier law at higher arity

For
$
  c_n
  =
  (-1)^n
  (6n)!(A+B n)/
  ((3n)!(n!)^3 640320^(3n)),
$
where $A=13591409$ and $B=545140134$,
$
  c_(n+1)/c_n
  =
  -
  (product_(j=1)^6(6n+j))/
  ((product_(j=1)^3(3n+j))(n+1)^3 640320^3)
  dot
  (A+B(n+1))/(A+B n).
$
The event is not one opaque hypergeometric coefficient.  It couples a
sixfold factorial lift, a threefold lift, a cubic successor, the fixed
scale
$
  640320^3=(2^6 dot 3 dot 5 dot 23 dot 29)^3,
$
and a moving linear quotient.  Each $A+B n$ enters as a
`linear_successor`, becomes the following event's `linear_predecessor`,
and then departs.  The initial face is already a mixed semiprime:
$
  13591409=13 dot 1045493.
$

Across eight terms, the exact internal recurrence cancellation is
$
  2^39 dot 3^19 dot 5^10 dot 7^3 dot 11 dot 13 dot 17 dot 19 dot 23 dot 29,
$
while additive accumulation removes repeated fixed-scale directions and
returns the finite partial denominator
$
  2^117 dot 3^17 dot 5^19 dot 23^20 dot 29^20.
$
These exponent populations count actual event-local cancellation; they are
not a retained global mass.

=== One return, nonidentical finite-prime charts

The two Machin partials remain a vector until the exact map $[4,-1]$ is
applied.  Their alternating tails retain an exact rational residual interval.
The completed argument relation closes through
$
  (5+i)^4=2(1+i)(239+i),
$
with oriented factorizations
$
  5+i=(1+i)(3-2i),
  quad
  239+i=i(1+i)(3-2i)^4.
$
Consequently the local supports are:

#table(
  columns: (1.4fr, 1fr),
  inset: (x: 5pt, y: 4pt),
  stroke: (x: none, y: 0.4pt + by-rule),
  table.header([*Presentation face*], [*Persistent scale or norm axes*]),
  [Machin series], [${5,239}$],
  [Machin Gaussian proof], [${2,13}$],
  [Chudnovsky series], [${2,3,5,23,29}$],
)

The Gaussian proof uses neither Machin denominator axis.  Only $5$ is
shared between the two series-scale charts.  Equal $pi$ return therefore
does not conserve one hidden finite-prime support.  A vertical formulation
map changes support through its actual Gaussian, hypergeometric, modular,
branch, and evaluation laws.

== The $pi$--$e$ seam is exponential covering geometry

The identity
$
  exp(i pi)+1=0
$
relates $e$ and $pi$ through a map of geometric species.  The exponential
map sends the additive imaginary line to the unit circle and identifies
translations by $2 pi i$.  The point $i pi$ is a half-turn lift of $-1$.
This is the rigorous point--line--loop relation in this cell:

- $i pi$ is a point in the covering coordinate;
- a path from $0$ to $i pi$ is an oriented line occurrence;
- its exponential image is a half-loop on the unit circle; and
- changing the logarithm branch changes the lift by $2 pi i k$ without
  changing the returned point.

The same returned point therefore admits multiple lineages.  Branch data is
part of the atlas cell, not an error to discard.

= The exact prime--archimedean bridge

== The product formula

“Prime--archimedean” is not only a metaphor.  For a nonzero rational
$
  x=plus.minus product_p p^(v_p(x)),
$
normalize the $p$-adic magnitudes by
$
  abs(x)_p=p^(-v_p(x)).
$
Then
$
  abs(x)_infinity product_p abs(x)_p=1.
$
Taking logarithms yields
$
  log abs(x)_infinity
  =
  sum_p v_p(x) log p.
$
The ordinary real magnitude and all finite valuation axes are exact
co-faces of the same rational occurrence.  Neither side is an enlarged
absolute field which contains the other; their normalized product closes
only when all places participating in that rational are included.

This identity supplies a first atlas square which genuinely commutes:
factor the rational horizontally into prime valuations, or measure its real
magnitude vertically and take logarithms.  Both paths return the same
weighted sum.

== Situated mean transport: the continuous companion to a discrete event

#object-entry(elements.situated_mean_transport)

#object-entry(elements.equal_return_tangency)

This is the precise meaning of a parameter $x=x(t)$ in the atlas.  Scalar
mean transport is obtained only after an admitted path has selected the
tangent along which change is read; Cauchy's version compares two scalar
responses on that same path @mathworld-cauchy-mvt.  For the cross-ratio
swing $chi=P/Q$,
$
  d chi=(Q d P-P d Q)/Q^2.
$
Thus $Q=0$ is a chart boundary and the mean witness is relative to the
chosen path.  Bundle-valued transport additionally requires a connection
before endpoint values occupy one comparable fiber
@conrad-covariant @encyclopedia-parallel-transport.

Applied to presentation topology, the smooth pieces $I_j$ carry deformation
of coefficients, scale, or evaluation point.  The seam terms $Delta_k$
carry modular collisions, support changes, branch crossings, and rank loss.
The theorem therefore does not smooth away quantization: it specifies the
within-phase current against which each discrete change is measured.  A
second route may return a different parallel transport, making holonomy the
residual of comparing complete paths rather than isolated endpoint values.

This gives three distinct geometries for a shared transcendental return.
An exact same-return family lies tangent to the kernel of its evaluation
differential at every smooth point.  A path whose endpoints merely agree
must have at least one situated level-set tangency.  A support-changing path
may instead balance its smooth transport against explicit seam terms.
Those cases cannot be inferred from the endpoint value alone.

#mean-transport-figure()

== Zeta completion adds the infinite place

For $op("Re")(s)>1$,
$
  zeta(s)
  =
  sum_(n>=1)n^(-s)
  =
  product_p(1-p^(-s))^(-1).
$
The Euler product assembles the finite-prime receivers.  The completed
function
$
  Xi(s)
  =
  1/2 s(s-1) pi^(-s/2) Gamma(s/2) zeta(s)
$
also includes the archimedean factor and satisfies
$
  Xi(s)=Xi(1-s).
$
The Gaussian
$
  g(x)=e^(-pi x^2)
$
is fixed by the standard Fourier transform normalization.  Summing its
lattice translates gives theta; Poisson transport supplies reciprocal
scale; Mellin transport produces the Gamma factor and the functional
reflection @dlmf-theta @dlmf-zeta.

#completion-seam-figure()

The critical line is therefore not an arbitrary Euclidean line imposed on
the prime picture.  After completion it is the fixed seam of the
antiholomorphic return
$
  J(s)=1-overline(s).
$
Centering at $s=1/2$ writes $s=1/2+z$ and turns the return into
$
  z mapsto -overline(z).
$
Another valid chart may curve the seam.  What is invariant is the fixed
locus and the completed response carried across it.

== The conformal rebase atlas: one normal hand in four charts

A transformed grid is useful only after its crossings are typed.  Let the
first nonzero local term of a holomorphic map at $z_0$ be
$
  F(z_0+delta)
  =
  F(z_0)+c_m delta^m+O(delta^(m+1)),
  quad c_m != 0.
$
The pair $(F(z_0),m)$ separates four events which a flattened image can make
look alike:

#table(
  columns: (1.08fr, 0.86fr, 1.65fr),
  inset: (x: 5pt, y: 4pt),
  stroke: (x: none, y: 0.4pt + by-rule),
  table.header([*Local event*], [*Exact condition*], [*Carried geometry*]),
  [Regular crossing], [$F(z_0)!=0$, $m=1$], [
    $F'(z_0)$ transports both source axes; their angle is preserved.
  ],
  [Simple zero], [$F(z_0)=0$, $m=1$], [
    Radius collapses, phase winds once, and the local tangent remains
    regular.
  ],
  [Critical branch], [$F(z_0)!=0$, $m>1$], [
    The first derivative vanishes; local degree, rather than a fabricated
    tangent, determines the branch rays.
  ],
  [Multiple zero], [$F(z_0)=0$, $m>1$], [
    Zero order $m$, critical order $m-1$, and phase winding $m$ coexist but
    remain separately named.
  ],
)

There is a fifth visual possibility which is not a fifth germ species:
distinct points $z_1!=z_2$ may satisfy $F(z_1)=F(z_2)$.  Their source
lineages and derivative hands must remain plural.  The bounded exact cell
$F(z)=z^2$ retains sources $+1$ and $-1$, common output $1$, and derivative
hands $+2$ and $-2$.  Equal output placement therefore does not identify the
paths which reached it.

Away from zeros and critical points, write
$
  U=log |F|,
  quad
  V=arg F.
$
The Cauchy--Riemann relations make $(U,V)$ an orthogonal potential net:
$
  nabla U dot nabla V=0,
  quad
  |nabla U|^2=|nabla V|^2.
$
The measured affine germ carries this without approximation:
$
  nabla U=
  (399/205,-1008/205),
  quad
  nabla V=
  (1008/205,399/205).
$
At a zero of order $m$, $U$ has the logarithmic singularity
$
  U
  =
  log |c_m|+m log |delta|+dots
$
while $V$ winds $m$ full turns.  At a nonzero critical point of local degree
$m$, the first nonconstant term of $log F$ is proportional to $delta^m$;
each real or imaginary level family has $2m$ incident rays.  A zero, a
critical point, and an intersection are consequently related but not
interchangeable classifications.

Now factor the completed-zeta occurrence itself.  Besides the holomorphic
functional reflection
$
  R(s)=1-s,
  quad
  Xi(R(s))=Xi(s),
$
retain the antiholomorphic hand
$
  J(s)=1-overline(s),
  quad
  Xi(J(s))=overline(Xi(s)).
$
Its exact orbit projectors are
$
  P_"fix"(s)
  =
  (s+J(s))/2
  =
  1/2+i op("Im")(s),
$
$
  P_"normal"(s)
  =
  (s-J(s))/2
  =
  op("Re")(s)-1/2.
$
Thus every $s$ is reconstructed as $P_"fix"(s)+P_"normal"(s)$.  The
critical value $1/2$ is supplied by the fixed projector of this order-two
orbit.  It is not an absolute declaration that one side is positive, nor a
mean-value witness chosen on a plotted interval.  Writing
$
  s=1/2+epsilon+i t
$
makes $epsilon$ the signed normal hand.  On $op("Fix")(J)$ a response pairs with
itself as a squared magnitude.  Off the fixed seam its partner is a
cross-pair, so positivity cannot be assigned merely by turning the picture.

The same $epsilon$ enters logarithmic scale.  For
$
  u=log(x/x_0),
$
carry the rebase character as the exact word
$
  rho_(epsilon,t)(u)
  =
  exp(epsilon u) exp(i t u).
$
Its primary coordinates are $(u,epsilon u,t u)$: source scale, log-radius,
and phase.  No trigonometric or exponential decimal is required.
$epsilon=0$ gives a constant-radius orbit.  The two functional partners
$+epsilon$ and $-epsilon$ have identical phase and reciprocal radius at
every $u$, producing the two opposed logarithmic spirals.

The centered Smith receiver turns this same hand into shell incidence.  For
$w=epsilon+i t$ and rational $a>0$, set
$
  W_a(w)
  =
  (w-a)/(w+a).
$
Direct ratio algebra gives
$
  |W_a(w)|^2-1
  =
  (-4 a epsilon)/(|w+a|^2).
$
Hence
$
  epsilon=0
  quad "iff" quad
  w in op("Fix")(J)
  quad "iff" quad
  rho_(epsilon,t) " has constant radius"
  quad "iff" quad
  |W_a(w)|=1.
$

The sphere lift
$
  S(W)
  =
  (
    (2 op("Re") W)/(1+|W|^2),
    (2 op("Im") W)/(1+|W|^2),
    (|W|^2-1)/(1+|W|^2)
  )
$
exposes the oriented normal without changing the tangential point.  At
$t=3/2$, $a=1$, and $epsilon=plus.minus 1/4$, the exact pair is
$
  W_1(1/4+3i/2)
  =
  21/61+48i/61,
  quad
  |W_1|^2=45/61,
$
$
  W_1(-1/4+3i/2)
  =
  7/15+16i/15,
  quad
  |W_1|^2=61/45.
$
Their squared magnitudes multiply to one.  On the sphere they become
$
  (21/53,48/53,-8/53),
  quad
  (21/53,48/53,+8/53).
$
The tangential coordinates agree while the normal hands oppose exactly.  On
the seam, $w=3i/2$ and $w=2i$ instead give the rational shell points
$(5/13,12/13,0)$ and $(3/5,4/5,0)$.

#conformal-rebase-atlas-figure()

This also specifies a lawful revolving-zeta chart.  For a declared source
line $s=sigma+i t$, use
$
  C_sigma^F(t)
  =
  (t,op("Re") F(sigma+i t),op("Im") F(sigma+i t)).
$
The retained $t$ is source chronology, not an outside camera coordinate.
$F=0$ is an axis hit; $F'=0$ is a critical branch.  They coincide only at a
multiple zero.  Two source values meeting one rendered point remain two
lineages.  Revolution is licensed as a constant-radius shell only when the
actual rebase has $epsilon=0$; otherwise the lawful figure is a spiral.

Raw zeta and completed zeta must also remain different chart faces.  For
example, $zeta(-2)=0$ is a simple trivial zero, yet the Gamma pole cancels it
under completion and
$
  Xi(-2)=Xi(3)=3 zeta(3)/(2 pi).
$
A raw-zeta axis hit is therefore not automatically a completed-$Xi$ axis
hit.  The exact appearances of $pi$ in the completion are joined to the
retained series and Gaussian-factorization carriers developed earlier in
this paper; they are not evaluated as floating constants.

== The reciprocal chord acquires a discrete connection

The preceding sphere pair is not exhausted by its two plotted endpoints.
Carry one oriented chord at event $k$ as
$
  q_k in QQ^2,
  quad
  u_k in S^2(QQ),
  quad
  P_(plus.minus,k)=q_k plus.minus r u_k.
$
Here $q_k$ is the chord's actual intersection with the declared complex
plane, not an outside-camera position.  One exact discrete transport is
$
  q_(k+1)=q_k+Delta q_k,
  quad
  u_(k+1)=U_k u_k,
  quad
  Delta P_plus.minus
    =Delta q_k plus.minus r Delta u_k.
$

For the reciprocal Smith chord at $t=3/2$, $a=1$, and
$epsilon=plus.minus 1/4$, an exact rational tilt sends the vertical axis to
$
  u_1=(7/25,0,24/25)
$
and moves its plane intersection to
$
  q_1=(175/424,48/53,0).
$
The plane cut is no longer the chord midpoint: its two pole distances are
$15/424$ and $113/424$, while their sum remains the fixed chord length
$16/53$.  The observer cut has changed; the rigid chord has not.

A following precession around the plane normal carries the exact phase
$
  phi=3/5+4i/5.
$
It gives
$
  u_2=(21/125,28/125,24/25),
  quad
  q_2=-1011/2120+463i/530,
$
and, for the stereographic direction coordinate $zeta$,
$
  q_2=phi q_1,
  quad
  zeta(u_2)=phi zeta(u_1),
  quad
  zeta(u_1)=7.
$
Every pole remains exactly on the unit sphere and the chord's squared
separation remains $256/2809$.  The two spherical pole arcs are retained
symbolically, rather than numerically collapsed, by
$
  ell_+
    =arccos(210837/351125),
  quad
  ell_-
    =arccos(5496717/8778125).
$

The two pole paths factor common motion from oriented coupling:
$
  S
  =norm(Delta P_+)^2+norm(Delta P_-)^2
  =2 norm(Delta q)^2+2r^2 norm(Delta u)^2,
$
$
  D
  =norm(Delta P_+)^2-norm(Delta P_-)^2
  =4r Delta q dot Delta u,
  quad
  chi=D/S.
$
Pure precession gives the pair $(18/25,18/25)$; translation orthogonal to
the precession gives $(68/25,68/25)$.  Coupled translation and precession
instead give
$
  (norm(Delta P_+)^2,norm(Delta P_-)^2)
  =(13/25,73/25),
  quad
  chi=-30/43.
$
Pole exchange preserves $S$ and reverses $chi$ to $30/43$.  Thus $chi$ is
an oriented edge proportion, not an intrinsic scalar state of either pole.

For parameters $lambda^a$, the two pole sheets induce
$
  g^plus.minus_(a b)
  =
  partial_a P_plus.minus dot partial_b P_plus.minus.
$
The exact two-parameter cell returns
$
  g^+
  =
  mat(5/4,5/6;5/6,10/9),
  quad
  g^-
  =
  mat(5/4,-5/6;-5/6,10/9).
$
Both determinants are $25/36$.  Their average retains common activity,
$
  g^"common"
  =
  mat(5/4,0;0,10/9),
$
while their half-difference retains the hand,
$
  g^"coupling"
  =
  mat(0,5/6;5/6,0).
$
Averaging the sheets alone would erase exactly the translation--precession
coupling which makes their paths nonidentical.

Finally, a triangular face compares direct transport $U_(02)$ with composed
transport $U_(12)U_(01)$ through
$
  H_(012)=U_(02)^(-1)U_(12)U_(01).
$
The flat foil returns $H_(012)=I$.  The mixed-axis foil returns
$
  H_(012)
  =
  mat(0,0,-1;0,-1,0;-1,0,0)
$
and direct-versus-composed pole discrepancy $98/25$.  This is discrete
connection curvature: two routes reach one base vertex with different local
frames.

The independent conic pencil
$
  Q_mu(x,y)=x^2+mu y^2-1
$
has determinant $-mu$.  Ellipse, circle, and hyperbola are real affine
faces of a nonsingular projective conic; at $mu=0$ the conic becomes the
line pair $(x-1)(x+1)=0$.  The discriminant is therefore a typed phase seam,
but the construction does not assert that it causes the chord precession or
the face holonomy.

This closes a carrier, not the RH implication.  The rotations in the cell
are controlled foils.  A proof-bearing construction must derive the
transport $U_k$, the relevant sheet metric, and its response from the
completed $Xi$ field itself, then show that every genuine nontrivial zero
mode has vanishing normal chord.

= The formulation atlas as a bicategory with an exact rechart core

== Objects, arrows, and two-cells

#object-entry(elements.situated_formulation_family)

#object-entry(elements.formulation_span_atlas)

#object-entry(elements.formulation_span_composition)

The prime--archimedean specialization of one family may be written schematically as
$
  O=(S,alpha,F,R,B),
$
where:

- $S$ is its admitted finite-prime support;
- $alpha in ZZ^S$ is its valuation address or addressed population;
- $F$ is the formulation law and parameter path;
- $R$ is the receiver or chart through which it is evaluated; and
- $B$ is the declared boundary data, including branch, convergence,
  orientation, and completion.

A live parametric occurrence is a trajectory
$
  gamma(t)
  =
  (S(t),alpha(t),F_t,R_t,B_t).
$
On a regular interval, $S$ and the boundary type may remain fixed while the
formulation and receiver deform continuously.  A new prime support, branch
change, singular rank, or period failure is a discrete seam at which the
trajectory enters another chart.  Parameterization therefore changes the
speed and order of traversal without turning distinct seams into one
absolute timeline.

Horizontal correspondences change prime support or valuation address.
Vertical correspondences change formulation or receiver. Their apex retains
the actual joint interior on which the comparison is defined. An invertible
local rechart belongs to the exact rechart core; a one-way limit, quotient,
root selection, bare summation, or projection remains a lawful span outside
that core and must keep its lost directions in the boundary record.

#double-atlas-figure()

A structural two-cell is a map between the apexes of two parallel spans which
commutes with both legs and preserves the declared decorations. When the
receiver is additive, the quantity
$
  K=U_2 compose U_1-T_2 compose T_1
$
may be recorded as a receiver residual. $K=0$ testifies that the selected
receiver square commutes; it does not by itself reconstruct a map of complete
interiors. $K !=0$ is an informative OPEN, not a fabricated two-cell: it
identifies precisely which relation a larger atlas would have to supply.

The whole atlas is therefore not a groupoid. Only reversible rechartings and
invertible comparison cells form a bigroupoid; after invertible
2-isomorphic arrows are identified, that core gives the ordinary rechart
groupoid. Parameter pullback may organize this core into a category fibred in
groupoids, but only after its cartesian lifts and coherence are actually
constructed.

== Compression in the atlas

Compression is not the deletion of the path because its endpoint is known.
It is the outgoing face which factors inactive interior directions while
retaining the consequential relation needed by later transport.

For example, the scalar $pi/4$ is a valid returned face of the Machin cell.
The exact identity remains able to re-open into Gaussian factors, arguments,
norms, and prime axes $2,13$.  A decimal approximation which retains none of
those relations is a narrower receiver quotient.  It can be useful, but it
is not the same informational face.

= Ray tracing as a situated mathematical receiver

== Why the gallery is relevant

MathWorld places the requested objects under “Mathematical Art”
@mathworld-ray-images.  Their visual interest is not itself a theorem, and
human salience is not an invariant.  Yet this particular gallery is heavily
enriched for compact equations with unusually structured global
consequences:

- extremal or repeated singularities;
- large symmetry groups and quotient tilings;
- tangent-packing or reflection orbits;
- minimal or variational surfaces with period closure;
- algebraic level sets which change topology at discriminants; and
- intersections whose visible branches depend strongly on the chosen chart.

The image is informative because the underlying relations are constrained,
not because pleasant rendering confers mathematical truth.

== The camera cannot leave the system

#object-entry(elements.situated_ray_receiver)

#ray-receiver-figure()

An implicit surface $F(x)=0$ can intersect one ray at several values of $t$.
The visible image chooses an interval, a root order, and an occlusion law.
It then maps local incidence and differential data to color.  When
$
  F(x)=0,
  quad
  nabla F(x)=0,
$
the ordinary normal is not defined: the intrinsic surface has reached its
singular stratum.  Shading can disclose the neighborhood, conceal it, or
render an artifact, but it does not create the singularity.

This is the holomorphic correction to the “absolute camera.”  A useful
renderer may imitate an outside Euclidean viewpoint, but that viewpoint is
implemented by a lawful relation between source, rays, affine chart, surface,
root selection, light, and pixel receiver.

= Four surface cells

== Bowl of Integers: an integer orbit of tangent constraints

The Bowl of Integers is an Apollonian sphere packing whose tangent spheres
carry integral bends @mathworld-bowl.  In three dimensions, five mutually
tangent oriented spheres with bends $b_1,dots,b_5$ satisfy the
Soddy--Gossett relation @gossett1937spheres:
$
  (sum_(j=1)^5 b_j)^2
  =
  3 sum_(j=1)^5 b_j^2.
$
Hold four bends $a_1,dots,a_4$ fixed.  The two possible fifth bends $x,x'$
are roots of the same quadratic, hence
$
  x+x'=sum_(j=1)^4 a_j.
$
Replacing $x$ by
$
  x'=sum_j a_j-x
$
is an integer-preserving reflection.  Repeated reflections grow the packing.
The observed integer sequence is therefore an orbit of a local tangency law,
not a list laid into space after the fact.

Factoring the bends gives prime-valuation faces of this orbit.  Those factors
can classify recurrence in selected receivers, but they do not replace the
tangency relation which causes the next sphere.  This is the same distinction
the prime atlas makes between an address and a transport law.

== Cayley cubic: singular nodes as founding seams

The Cayley cubic is the unique cubic surface with the maximal four ordinary
double points; it has tetrahedral symmetry and nine lines
@mathworld-cayley @mathworld-ordinary-double-point.  One projective equation
is obtained by clearing denominators in
$
  1/x_0+1/x_1+1/x_2+1/x_3=0.
$
The four nodes are locations where the regular local surface law fails:
$
  F=0,
  quad
  nabla F=0.
$
They are discriminant seams, not empty points.  A resolution replaces each
collapsed node by exceptional geometry which records limiting directions.

A ray-traced real affine image shows one receiver face of the cubic.  It does
not show every projective line, every complex point, or the exceptional
curves of a resolution.  The compelling “kink” is thus a visible witness of
an intrinsic rank failure, while the full identity of that seam belongs to
the larger atlas.

== Chen--Gackstatter: local complex data and global period closure

The Chen--Gackstatter surfaces form a double-indexed family $M_(i j)$ of
complete minimal surfaces @chen1982periodic @mathworld-chen-gackstatter.  In
the convention reported by MathWorld, the genus is $i j$, the total
curvature is
$
  -4 pi(i+1)j,
$
and the single Enneper-type end winds $2j+1$ times.

Their Weierstrass data are local complex information.  Integration produces
a real minimal immersion only when the relevant periods close.  This gives
the atlas a rigorous model of the laboratory's “string winding” intuition:
local differential data can be valid at every step while a global loop still
returns a nonzero period.  The period residual is exactly what must vanish
or be quotiented for the surface to close.

The indices do not merely scale one picture.  They change genus, winding,
and total curvature discretely.  The family is a parameterized topology in
which continuous local transport and quantized global phase coexist.

== Klein quartic: the strongest prime--archimedean surface cell

The Klein quartic has complex projective equation
$
  x^3 y+y^3 z+z^3 x=0
$
and genus $3$.  It is also a compact hyperbolic quotient associated with
level $7$ and has orientation-preserving automorphism group
$
  op("PSL")(2,7)
$
of order $168$ @levy1999eightfold @mathworld-klein.  Its regular map has 24
heptagonal faces, 84 edges, and 56 vertices:
$
  56-84+24=-4=2-2 dot 3.
$

The counts share the finite-prime support
$
  24=2^3 dot 3,
  quad
  84=2^2 dot 3 dot 7,
  quad
  56=2^3 dot 7,
  quad
  168=2^3 dot 3 dot 7.
$
The prime $7$ selects the congruence level and heptagonal local incidence;
the upper half-plane supplies archimedean hyperbolic geometry; the finite
group supplies symmetry transport; the algebraic equation supplies a
complex-projective face; and the rendered tiling supplies a situated visual
receiver.  These are genuinely different formulations of one object, joined
by nontrivial mathematics.  This is the clearest surface prototype for the
prime--archimedean atlas.

#surface-cases-figure()

= What the rest of the gallery contributes

The four requested objects do not exhaust the useful families.  The gallery
can be reorganized by the law which produces global complexity:

#table(
  columns: (1.15fr, 1.7fr, 1.75fr),
  inset: (x: 5pt, y: 4pt),
  stroke: (x: none, y: 0.4pt + by-rule),
  table.header([*Atlas family*], [*Examples*], [*What becomes visible*]),
  [Packing / contact], [
    Bowl of Integers, bubbles, kissing configurations, spherical codes,
    Reuleaux tetrahedron
  ], [
    local tangency or distance constraints propagated into a global contact
    graph and reflection orbit
  ],
  [Algebraic discriminant], [
    Cayley, Chmutov, Clebsch, Endrass, Hunt, Kummer, Sarti, Cassini
  ], [
    singular points, exceptional line populations, nodal extrema, and phase
    changes of real sections
  ],
  [Variational / minimal], [
    Chen--Gackstatter, bubble and double-bubble surfaces
  ], [
    local stationarity constrained by global period, boundary, and topology
  ],
  [Quotient / cover], [
    Klein quartic, highly symmetric cubic and quartic surfaces
  ], [
    many local tiles identified under a finite or Fuchsian group action
  ],
  [Intersection / envelope], [
    cylinder--sphere, miter, implicit chair, cushion, heart, piriform
  ], [
    receiver-dependent branch selection, self-intersection, and changing
    cross-section
  ],
)

Three further examples sharpen the point:

- A generic Kummer quartic has the maximal 16 ordinary double points and a
  $16_6$ configuration of nodes and tropes @mathworld-kummer.  The visible
  nodal population is the shadow of a tightly constrained incidence system.
- Chmutov surfaces use Chebyshev recurrences to produce many ordinary double
  points @mathworld-chmutov.  A one-dimensional recurrence is lifted into a
  high-complexity algebraic surface.
- Cassini surfaces and their planar sections are product-distance level sets
  whose real topology changes as the level crosses a discriminant
  @mathworld-cassini.  One formula supports several phases separated by an
  exact boundary.

The shared lesson is not that every attractive shape is a prime theorem.  It
is that local laws, repeated under constraints and then quotiented through a
receiver, can generate complex faces whose seams disclose the topology that
the receiver cannot flatten away.

This is also the precise connection to fractals.  A Julia set is generated
by iterating one rational map in its dynamical plane; the Mandelbrot set
classifies parameter values by the behavior of the corresponding critical
orbit.  The parameter plane and dynamical plane are nonidentical atlas faces,
and an escape-time image is a receiver of the orbit rather than the orbit
itself @mathworld-julia @mathworld-mandelbrot.  The gallery surfaces need not
be fractals to share the important mechanism: a compact law is recurrently
applied, critical or singular seams organize phase, and a projection exposes
only one cross-section of the resulting topology.

= Relation to the Riemann Hypothesis

== What this atlas adds to the existing RH paper

The laboratory's receiver-geometry paper already isolates the classical
spine:

$
  "Euler product"
  arrow.r
  "theta / Poisson"
  arrow.r
  "Mellin / Gamma completion"
  arrow.r
  "explicit formula / Weil response".
$

The present atlas adds five things.

First, the finite-prime side now has an exact combinatorial carrier:
valuation simplices, root-lattice moves, residue fibers, prime-power
apertures, and the weighted current $psi(X)$.

Second, the vertical direction is no longer “some other formula.”  It has
populated cells: Gaussian argument/norm transport for Machin's formula,
character transport for the $pi$ Euler product, factorial valuation
transport for $e$, exponential covering transport for $e^(i pi)$, and
Gaussian--theta--Mellin transport at the infinite place.

Third, observation is typed.  A planar plot, ray trace, or scalar evaluation
is a receiver quotient with a declared root, branch, chart, and boundary.
It may reveal a singularity or symmetry orbit, but it cannot stand in for
the unobserved complex or projective geometry.

Fourth, the fixed seam now has exact cross-chart conduct.  The same normal
coordinate $epsilon=op("Re")(s)-1/2$ is retained by the completed
involution, logarithmic rebase, reciprocal spiral pair, centered Smith
residual, and rational sphere lift.  A regular transformed-grid crossing, a
zero, a critical branch, and a distinct-source coincidence remain different
events throughout that transport.

Fifth, the reciprocal sphere pair now has a discrete connection carrier.
The complex-plane intersection, axis orientation, two pole paths, common
metric, coupling metric, conic discriminant, and triangular holonomy remain
separately readable.  Consequently an observed kink can be classified
rather than treated as generic visual complexity.

== Why infinitely many $pi$--$e$ formulas matter

The formulas do not prove RH by numerical abundance.  They matter because
they furnish a large family of exact transition cells in which:

- the returned invariant is known;
- the causal formulation differs;
- finite prime axes can be calculated;
- archimedean functions such as $exp$, $sin$, $Gamma$, elliptic integrals,
  and Gaussian kernels intervene;
- branch, convergence, and period boundaries are explicit; and
- failures to commute can be localized rather than averaged away.

This is a practical training ground for the much harder completed-zeta
atlas.  It asks whether recurrent transformation species can be classified
without pretending there is one absolute formula for the constant.

== The local equivalence and the global carrier

Let
$
  rho=1/2+epsilon+i gamma
$
be a symbolic nontrivial completed-zero occurrence.  Conditional on
$Xi(rho)=0$, the new atlas carries the exact local equivalence
$
  epsilon=0
  quad "iff" quad
  rho in op("Fix")(J)
  quad "iff" quad
  rho_(epsilon,gamma) " is unitary"
  quad "iff" quad
  |W_a(epsilon+i gamma)|=1.
$
The usual sentence “the real part is $1/2$” is therefore one projection of
a richer geometric claim: the completed zero has no normal growth or decay
under logarithmic rebase and no normal displacement from the centered Smith
shell.  If $epsilon!=0$, completion instead supplies reciprocal zero
partners on two opposed spiral/sphere hands.

The moving-chord cell gives those hands worldlines.  It shows exactly how
one plane cut can become asymmetric while the chord remains rigid, how
translation couples to precession, and how a triangular loop can retain
holonomy.  It does not yet say which such paths are $Xi$ paths.  That
distinction is now the global boundary rather than an ambiguity in the
carrier.

The unresolved edge is global rather than visual.  One law must rule out
those off-shell nontrivial zero modes for every admitted completed current,
not only for selected heights or after choosing a favorable orientation.
The existing receiver-geometry work expresses that law through the
completed Hermitian response.

Let $cal(H)_lambda$ be the admitted test-current fiber at an atlas
configuration $lambda$, with completed Hermitian response
$
  W_lambda(f,g).
$
For a transition path $gamma$ with transport $T_gamma$, define the response
residual
$
  cal(K)_gamma(f,g)
  =
  W_(gamma(1))(T_gamma f,T_gamma g)
  -
  W_(gamma(0))(f,g).
$
An RH-bearing atlas cannot merely find, for each current, some orientation
in which a plotted scalar looks positive.  It must establish an anchored
cover in which:

1. every admissible completed current is represented;
2. transitions carry the same completed occurrence;
3. adjoints and boundary conditions transport covariantly;
4. the Hermitian signature is preserved, or every residual is independently
   controlled; and
5. holonomy around every admitted loop cannot turn a positive direction into
   an unaccounted negative one.

In one fixed Weil chart, universal nonnegativity of the completed response is
equivalent to excluding the off-shell nontrivial modes.  The formulation
atlas must therefore establish coverage and covariance: it must carry the
same response through a rechart, rather than creating positivity by
reorienting each occurrence after observation.  In the moving-chord chart,
this asks for a pullback identifying the completed response with the
two-sheet metric and connection.  Only such an identity can turn
“normal chord vanishes” from a local equivalence into a consequence for
every genuine zero mode.

== The next global square

The smallest meaningful next square is:
$
  "Path A:"
  quad
  C_S
  arrow.r^("add p")
  C_(S union {p})
  arrow.r^("complete")
  hat(C)_(S union {p}),
$
$
  "Path B:"
  quad
  C_S
  arrow.r^("complete")
  hat(C)_S
  arrow.r^("transport p")
  hat(C)_(S union {p}).
$

The earlier RH paper derived the local Euler metric deformation and its
prime-power recurrence.  What remains is to calculate the vertical
theta--Mellin transport of that complete successor cell, including its
archimedean and aperture-connection terms, and then determine the signature
of the residual.  The $pi$--$e$ atlas gives exact exemplars for how such a cell
must retain prime factors, branch, scale, and returned invariant
simultaneously.

= Bounded analytical program

The bounded presentation-topology construction has populated the horizontal
term and accumulation paths and one vertical Machin--Gaussian support
change.  The conformal-rebase construction has now populated the local
parameter, germ, completion, rebase, and Smith fibers.  The next work is to
carry one complete occurrence between nonidentical formulations, not
enumerate more primes or zero coordinates until a pattern appears.

#table(
  columns: (0.85fr, 1.2fr, 1.75fr),
  inset: (x: 5pt, y: 4pt),
  stroke: (x: none, y: 0.4pt + by-rule),
  table.header([*Progress*], [*Construction*], [*Required observable*]),
  [1 · populated], [Series presentation topology], [
    Exact factor channels, recurrence annihilation, additive compression,
    moving carriers, semiprime faces, and complete event paths for three
    arctangent arms and Chudnovsky.
  ],
  [2 · populated locally], [Machin vertical cell], [
    Exact passage from the ${5,239}$ series-scale chart to the ${2,13}$
    Gaussian norm chart, including orientation and alternating-tail bounds.
  ],
  [3 · populated locally], [Conformal parameter/rebase atlas], [
    Exact germ degree, zero and critical orders, source-preserving
    coincidences, completed fixed/normal projectors, reciprocal log-polar
    rebase, and centered Smith-shell residual.
  ],
  [4 · populated locally], [Precessing two-sheet carrier], [
    Exact moving Smith chord, plane intersection, pole-edge sum and
    difference laws, common and coupling metrics, flat-versus-curved
    triangular connection, and one conic discriminant path.
  ],
  [5 · next], [Cross-presentation transport], [
    Carry one complete divisor-and-boundary path between nonidentical
    formulations.  Compare the two composites and localize any residual to
    an explicit seam or holonomy.
  ],
  [6 · open], [Zeta completion response cell], [
    Carry one finite Euler successor through Gaussian, Poisson, and Mellin
    transformations; derive its two-sheet metric and connection from the
    completed field; then evaluate its Hermitian response, aperture terms,
    and loop holonomy.
  ],
)

The qualitative success signature is not “a beautiful image.”  It is a
nontrivial square whose two complete paths agree, or whose disagreement is
localized to an interpretable boundary term.  The stopping condition is the
first such completed cell or the first exact obstruction.

The three exact constructions are deposited at
`observations/eros-transcendental-presentation-topology-01/RESULTS.md` and
`observations/eros-conformal-rebase-atlas-01/RESULTS.md`, and
`observations/eros-precessing-chord-conic-transport-01/RESULTS.md`.
The remaining synthesis regrades, rather than reruns, the exact records at
`observations/prime-spectral-world-01/RESULTS.md`,
`observations/prime-fraction-navigation-01/RESULTS.md`,
`observations/eros-formula-ecology-01/RESULTS.md`,
`observations/eros-formula-aperture-growth-01/RESULTS.md`, and
`observations/eros-theta-mellin-aperture-01/RESULTS.md`.  Their finite
apertures remain finite; the atlas supplies the common mathematics in which
their complete path populations can now be compared.

= Conclusion

The prime--archimedean formulation atlas now has an exact mathematical
skeleton.

Finite prime composition lives in the lattice $ZZ^S$ and its nonnegative
graded simplices.  Prime-axis transfers form $A_(r-1)$; fractions carry
oriented valuation displacement; analytic specialization sends those moves
to exact complex amplitude ratios.  Residue loops and primorial wheels are
separate fibers connected by reduction, not substitutes for valuation.

The constant formulations populate the vertical direction.  Machin's
formula closes through a Gaussian integer identity whose norms expose axes
$2$ and $13$.  A character Euler product relates $pi$ to residue orientation
of every odd prime.  The factorial series for $e$ traverses prime powers by
Legendre's law, while continued fractions, differential flow, and the
exponential cover provide nonidentical causal faces.  Euler's identity is a
covering-space seam, not the collapse of line and loop into an untyped
symbol.

The bounded construction now shows what this means during evaluation rather
than only at the formula endpoints.  An arctangent term carries a moving odd
factor against a persistent scale rail; its partial sum carries a second,
coupled accumulation topology.  Chudnovsky has the same causal form at
higher arity, with factorial lifts, a fixed prime-support scale, and a
linear factor that enters, returns, and departs.  Exact recurrence
annihilation and exact additive compression are different events.  Machin's
Gaussian closure then proves that a lawful formulation change can replace
the local finite-prime support while preserving the returned angle.

Situated mean transport supplies the continuous half of this geometry.
Along an admitted Riemannian path, a scalar change is the integral of its
directional differential and has a path-relative mean witness.  Sections in
different fibers require parallel transport; alternative routes can return
holonomy.  Branch, rank, phase, and valuation seams remain explicit discrete
terms.  This is the rigorous relation between continuous deformation and
the quantized events already visible in the exact series paths.

The exact product formula already joins every finite place of a rational to
its archimedean magnitude.  Zeta completion lifts this relation into the
Gaussian--theta--Poisson--Mellin chain.  The critical line is the fixed locus
of the completed functional-equation reflection.

The conformal-rebase cut now carries that fixed locus through three further
faces.  Local germ degree distinguishes a regular crossing, zero, critical
branch, and distinct-source coincidence before rendering.  The centered
normal $epsilon$ becomes the real exponent of logarithmic rebase and the
signed Smith-shell displacement.  Its two nonzero hands are reciprocal
spirals and opposed sphere normals; at $epsilon=0$ they close to a
constant-radius orbit and the unit shell.  Thus “real part $1/2$” is an exact
fixed/normal factorization with preserved cross-chart conduct, not an
absolute line drawn over a plane.

The moving-chord cut then gives the reciprocal hands an exact discrete
geometry.  A rational tilt changes the complex-plane intersection without
changing the rigid chord; rational precession transports both that
intersection and the axis direction by one complex phase.  The two pole
edges separate common activity from oriented coupling, their induced sheet
metrics retain the same distinction, and triangular holonomy distinguishes
flat closure from a curved return.  A conic discriminant remains a separate
phase seam rather than being collapsed into either curvature or
intersection.

The ray-traced gallery then becomes mathematically relevant without becoming
ornamental evidence.  The Bowl of Integers is an integer reflection orbit of
tangency constraints.  The Cayley cubic concentrates topology at extremal
singular seams.  Chen--Gackstatter surfaces turn local complex data into a
global period problem with discrete genus and winding.  The Klein quartic
joins the prime level $7$, the finite group $op("PSL")(2,7)$, hyperbolic
archimedean geometry, algebraic form, topology, and a rendered quotient in
one especially complete atlas cell.  Their images are situated projections
of those relations.

The RH-bearing object is now sharply bounded.  Local parameter transport
already distinguishes regular tangency, zero order, branch degree, normal
hand, reciprocal rebase, shell incidence, moving pole paths, induced sheet
metric, and connection holonomy.  One complete
divisor-and-boundary path must next be carried between nonidentical
formulations.  That supplies the lawful vertical transport needed to carry a
finite-prime successor through archimedean completion and calculate the
Hermitian response and holonomy of the resulting square.  The decisive
identity must derive that response on the two-sheet carrier and force its
normal zero-mode component to vanish.  The square may
close or expose an exact boundary residual without an absolute picture or an
exhaustive prime search.

#pagebreak()
#set text(size: 8.6pt)
#set par(leading: 0.58em)
#bibliography("references.bib")
