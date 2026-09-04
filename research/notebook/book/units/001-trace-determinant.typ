#let characteristic-fiber-unit(
  show-derivations: false,
  panel: none,
  investigation: none,
  derivation: none,
  boundary: none,
) = [
= Unit 001 — The geometry inside a characteristic receiver

#panel(
  "Object of play",
  [
    Do not evaluate a list of matrices. Treat the four entries as coupled coordinates, unfold the
    named receivers, and study the full source families on which those receivers agree.
  ],
)

== The characteristic map

Let $K$ be a field of characteristic not equal to $2$, and write

$
M = mat(a, b; c, d) in upright("Mat")_2(K).
$

The characteristic receiver is the polynomial map

$
Phi: K^4 arrow.r K^2, quad
Phi(a,b,c,d) = (t,p) = (a+d, a d-b c).
$

It sends the source matrix to

$
chi_M(lambda) = lambda^2-t lambda+p.
$

The discriminant is not an additional independent coordinate. Unfolding it gives

$
Delta = t^2-4p
       = (a+d)^2-4(a d-b c)
       = (a-d)^2+4b c.
$

This last expression exposes the coupling that the names $upright("tr")(M)$ and $det(M)$ conceal:
the characteristic stratum depends on a squared diagonal imbalance and the signed product of the
two off-diagonal transports.

#boundary([
  The map $Phi$ is a lossy receiver. This unit studies its fibers and conjugation transport. It does
  not state or derive a closed commutator trace law while R33 remains under source separation.
])

== A graph chart before quotient

In the chosen basis, one may draw two vertices with loop weights $a,d$ and opposed directed edge
weights $b,c$. In that chart,

$
t = "loop sum", quad
p = "loop product" - "two-edge cycle product",
$

and

$
Delta = "loop imbalance"^2 + 4("two-edge cycle product").
$

This makes the sign coupling visible:

- $b c>0$ reinforces the nonnegative diagonal contribution;
- $b c=0$ leaves only the diagonal imbalance; and
- $b c<0$ can cancel the diagonal imbalance and carry the matrix through $Delta=0$.

The graph is a coordinate chart, not yet an intrinsic source graph. A general change of basis mixes
all four edge and loop weights while preserving $t,p$, and $Delta$.

#figure(
  image("../figures/characteristic-map.svg", width: 100%),
  caption: [The visible construction: a basis-dependent entry graph is reparameterized before the
  characteristic receiver condenses it to $(t,p)$. The quadric at right is the retained source
  fiber, not an illustration of one evaluated matrix.],
)

== Reparameterize the coefficient space

Introduce

$
t=a+d, quad x=a-d, quad y=b+c, quad z=b-c.
$

Because $2$ is invertible in $K$, the original entries are recovered by

$
a=(t+x)/2, quad d=(t-x)/2, quad
b=(y+z)/2, quad c=(y-z)/2.
$

Then

$
4b c=(b+c)^2-(b-c)^2=y^2-z^2,
$

so the discriminant becomes the indefinite quadratic form

$
Delta=x^2+y^2-z^2.
$

The characteristic map has therefore separated into:

- one trace coordinate $t$; and
- one quadratic receiver $Delta$ on the remaining three coordinates.

Since $p=(t^2-Delta)/4$, fixing $(t,p)$ is equivalent to fixing $(t,Delta)$.

#investigation("A", "Unfold the hidden quadratic geometry", [
Derive the inverse coordinate map and the identity $Delta=x^2+y^2-z^2$ without introducing scalar
examples. Then decide which parts require only commutative-ring algebra and which require division
by $2$.

Treat $t$ as an axis transverse to the three-dimensional $(x,y,z)$ coefficient geometry. What does
one fiber of $Phi$ look like in the remaining coordinates?
])

#derivation(show-derivations, [
The polynomial identity

$
(a-d)^2+(b+c)^2-(b-c)^2=(a-d)^2+4b c
$

uses only commutative-ring algebra. Recovering $a,d,b,c$ from $t,x,y,z$ uses division by $2$, so the
coordinate change is invertible only where $2$ is a unit.

For fixed receiver coordinates $(T,P)$, set $D=T^2-4P$. The full fiber is

$
Phi^(-1)(T,P) arrow.l.r { (x,y,z) in K^3 : x^2+y^2-z^2=D }.
$

Thus one characteristic output corresponds to a two-dimensional quadratic source family in the
generic algebraic sense, not to one matrix.
])

== Real strata as quadric geometry

Over $K=RR$, the sign of $Delta$ cuts the coefficient space into three geometric strata. At fixed
trace:

$
x^2+y^2-z^2=Delta.
$

- $Delta>0$ gives a connected one-sheet hyperboloid.
- $Delta=0$ gives a double cone.
- $Delta<0$ gives a two-sheet hyperboloid aligned with the $z$ direction.

The zero stratum is where the root type changes. Its tip

$
x=y=z=0
$

corresponds to the scalar matrix $M=(t/2)I$. The rest of the cone has the same repeated
characteristic root but retains non-scalar structure.

#figure(
  image("../figures/quadric-fibers.svg", width: 100%),
  caption: [Real level-set atlas for $x^2+y^2-z^2=Delta$. Solid outlines carry the qualitative
  geometry; transverse ellipses expose the changing sections rather than hiding them behind a
  shaded surface.],
)

#investigation("B", "Locate the change of type", [
Take the defining quadratic $q(x,y,z)=x^2+y^2-z^2$ as the object. Study its level sets by slicing at
fixed $z$, then by slicing at fixed $x$. Do not select points; describe when a slice is empty, a
point, one circle, or two branches as a relation among the remaining variables.

Compute the gradient of $q$ and locate the singular point of the zero fiber. Relate that singularity
to the collision between scalar and non-scalar repeated-root matrices.
])

#derivation(show-derivations, [
At fixed $z=z_0$, the level equation is

$
x^2+y^2=Delta+z_0^2.
$

The sign of the right side decides whether the slice is empty, a point, or a circle. At fixed
$x=x_0$, one obtains $y^2-z^2=Delta-x_0^2$, whose factorization

$
(y-z)(y+z)=Delta-x_0^2
$

exposes hyperbolic branches and their degenerations.

The gradient is $nabla q=(2x,2y,-2z)$. It vanishes only at the origin. That point lies on the zero
fiber, so $q=0$ is singular exactly at the scalar matrix. Away from the tip the cone is regular,
including the non-scalar repeated-root locus.
])

== Describe the fiber without diagonalizing

Fix receiver values $(T,P)$. Eliminating $d$ from

$
a+d=T, quad a d-b c=P
$

gives

$
d=T-a, quad b c=a(T-a)-P.
$

This already describes the fiber as a coupled surface.

On the chart $b != 0$,

$
c=(a(T-a)-P)/b,
$

so $(a,b)$ are local coordinates. There is a symmetric chart with $c != 0$. On the seam $b=0$,
the relation requires $a(T-a)=P$, while $c$ is not determined by the characteristic receiver.

#investigation("C", "Move inside a receiver fiber", [
Hold $a,d$ fixed and consider the symbolic transport

$
(b,c) mapsto (mu b, mu^(-1)c), quad mu != 0.
$

Derive everything preserved by this motion. Then study what happens as one tries to continue the
chart toward $b=0$ or $c=0$. Is the apparent obstruction in the fiber itself, or in this chosen
parameterization of the fiber?
])

#derivation(show-derivations, [
The product is unchanged:

$
(mu b)(mu^(-1)c)=b c.
$

Therefore $t,p,Delta$, and the entire characteristic polynomial remain fixed while the individual
off-diagonal entries move. The transport is a multiplicative orbit inside one receiver fiber.

The formula uses $mu^(-1)$ and therefore cannot cross $mu=0$. The underlying fiber may still contain
points with $b=0$ or $c=0$; what fails is this particular multiplicative chart. The distinction is
between a geometric obstruction and a coordinate obstruction.
])

== Deform across the strata

Instead of evaluating independent matrices, deform one coupling inside a single family. Hold
$a,d,b,c$ as symbolic initial data and set

$
b_lambda=lambda b, quad c_lambda=c.
$

Then

$
Delta(lambda)=(a-d)^2+4lambda b c.
$

If $b c != 0$, the exact crossing parameter is

$
lambda_* = -(a-d)^2/(4b c).
$

The sign and magnitude of $b c$ determine whether the chosen direction of parameter motion can ever
reach the cone $Delta=0$. This describes when the cases occur rather than exhibiting one value from
each case.

#investigation("D", "Replace cases by a transition locus", [
Analyze $Delta(lambda)$ as an affine function of $lambda$. Separate the cases $b c>0$, $b c<0$, and
$b c=0$ over $RR$, but retain $(a-d)^2$ symbolically. Determine which directions of motion cross the
zero stratum and which remain trapped in one sign region.

Then invent a two-parameter deformation of $(b,c)$ and derive its zero locus in parameter space.
])

#derivation(show-derivations, [
The slope is $4b c$. If $b c=0$, the deformation does not move the discriminant at all. If $b c>0$,
$Delta$ increases with $lambda$ and crosses zero only when the permitted parameter range contains
the nonpositive value $lambda_*$. If $b c<0$, it decreases and may pass from positive through zero to
negative as $lambda$ increases.

For $b_(lambda,nu)=lambda b$ and $c_(lambda,nu)=nu c$,

$
Delta(lambda,nu)=(a-d)^2+4lambda nu b c.
$

The transition locus is the hyperbola

$
lambda nu=-(a-d)^2/(4b c)
$

when $b c != 0$. Degenerate initial couplings change that parameter-space geometry rather than merely
changing a final scalar answer.
])

== Conjugation as a tangent flow

The complete change of basis $M mapsto P M P^(-1)$ preserves the characteristic receiver, but its
entry formula can conceal the local mechanism. To expose the infinitesimal transport, write

$
P(epsilon)=I+epsilon X+O(epsilon^2).
$

Then

$
P(epsilon) M P(epsilon)^(-1)
=M+epsilon(X M-M X)+O(epsilon^2).
$

For

$
X=mat(alpha,beta;gamma,delta),
$

the tangent motion $dot(M)=[X,M]$ is

$
dot(M)=mat(
  beta c-gamma b,
  beta(d-a)+b(alpha-delta);
  gamma(a-d)+c(delta-alpha),
  gamma b-beta c
).
$

The diagonal motions cancel in the trace. For a general tangent matrix
$H=mat(h_(11),h_(12);h_(21),h_(22))$, the determinant differential is

$
D(det)_M(H)=d h_(11)+a h_(22)-c h_(12)-b h_(21).
$

Substituting $H=[X,M]$ makes this differential vanish as well. Commutator directions are therefore
tangent to the characteristic fibers.

#figure(
  image("../figures/fiber-transport.svg", width: 100%),
  caption: [Two distinct algorithmic geometries: a deformation crosses receiver strata at
  $lambda_*$, while conjugation generates a tangent motion that remains inside one fixed
  characteristic fiber.],
)

#investigation("E", "Compare orbit directions with fiber directions", [
Derive the displayed commutator entry by entry. Verify symbolically that its trace and determinant
differential vanish. Then set $M=(t/2)I$ without choosing $t$ and determine every infinitesimal
conjugation direction there.

Compare that orbit tangent space with the tangent space of the cone $x^2+y^2-z^2=0$ at its tip.
Explain the mismatch geometrically.
])

#derivation(show-derivations, [
The trace cancellation is visible in the opposite diagonal entries. Substituting the four entries
of $[X,M]$ into $D(det)_M$ yields pairwise cancellation, so both first-order receiver changes vanish.

At a scalar matrix, $X M-M X=0$ for every $X$: the conjugation orbit has zero tangent dimension. But
the gradient of $x^2+y^2-z^2$ vanishes at the cone tip, so the linearized fiber equation imposes no
first-order constraint there. Its Zariski tangent space is three-dimensional. The large fiber
tangent and collapsed orbit tangent are two faces of the same singularity.
])

== The characteristic polynomial as a recurrence law

Cayley–Hamilton returns the characteristic receiver to the source operator:

$
M^2-t M+p I=0.
$

Therefore every higher power reduces inside the two-dimensional span generated by $I$ and $M$:

$
M^(n+2)=t M^(n+1)-p M^n.
$

Taking trace gives a scalar receiver recurrence

$
tau_(n+2)=t tau_(n+1)-p tau_n,
quad tau_0=2,
quad tau_1=t.
$

The coefficients are not arbitrary fitted numbers. They are the same coupled invariants that define
the entire characteristic fiber.

#investigation("F", "Follow one receiver into another", [
Starting only from $M^2-t M+p I=0$, derive the recurrence for $M^n$ and then for $tau_n$. Ask what is
lost in the passage from the operator recurrence to its trace recurrence.

Next, replace trace with another linear receiver on matrices. Determine the minimal property that
receiver needs in order to inherit the same recurrence.
])

#derivation(show-derivations, [
Multiplying Cayley–Hamilton by $M^n$ gives

$
M^(n+2)-t M^(n+1)+p M^n=0.
$

Any linear receiver $L$ therefore returns

$
L(M^(n+2))=t L(M^(n+1))-p L(M^n).
$

Trace is one such receiver. The scalar sequence forgets the matrix coefficients in the expansion of
$M^n$, eigenvectors or generalized eigenspaces, the chosen basis, and source lineage. Linearity—not
trace-specific mystique—is the property conducting the recurrence.
])

== Formal mirror

Open `research/notebook/lean/U001Trace.lean`. The Lean unit does not enumerate matrices. It checks general
identities in symbolic integer variables:

- $Delta=(a-d)^2+4b c$;
- $Delta=x^2+y^2-z^2$ under the changed coordinates;
- determinant multiplicativity and Cayley–Hamilton;
- trace and determinant differentials along $[X,M]$;
- the parameterized repeated-root fiber; and
- characteristic recurrence transport through an arbitrary linear receiver.

The declarations marked `FORMAL PLAYGROUND` are invitations to change a coordinate definition, a
transport, or a hypothesis and inspect the new proof obligation. The objective is not to reproduce a
stored tactic sequence.

#panel(
  "Continuation surface",
  [
    The next useful motion is whichever relation catches your attention: classify the conjugation
    orbits inside each quadric fiber; generalize the characteristic map to larger matrices; replace
    the two-vertex graph chart with a path or local system; or study how a selected receiver changes
    the visible stratification. The notebook does not prescribe an exercise order.
  ],
  fill: rgb("#fff6dd"),
  border: rgb("#9a6b12"),
)
]
