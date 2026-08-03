# THE PARTIAL IS A PROBE; THE INVARIANT IS A TRANSPORT

**2026-07-15 · RATIFIED / DEPOSITED · DIFFERENTIAL / ALGEBRAIC-GEOMETRIC / STATISTICAL
DERIVATION · NO SOMA INTERIOR CHANGE**  
**Canonical grade: RATIFIED**

This draft receives Brandon's multivariable-calculus, intuition, invariant-pivot, prime-navigation,
ODE/ecosystem, elementary-shape, and algebraic-geometry proposal. It extends the presented gear-word
draft and reads against `FORMULA §§I, XII–XIII, XXIV–XXV, XXXIX, LIII, LVI–LVIII`. It does not amend
the canon or install calculus, a tolerance, a gradient, a prime sieve, or tropical arithmetic inside
Soma.

## Verdict

Yes, with one decisive correction:

> **A total differential is an infinitesimal receiver face of the swing, not the whole swing. A
> partial derivative holds coordinate directions fixed for one local probe; that does not make
> those coordinates invariants of the lived transport. A genuine invariant is a construction whose
> declared face survives along the actual worldline or under the admitted transformations. The
> finite swing is therefore closer to moving-frame transport plus a covariant difference than to a
> bare sum of partial derivatives.**

The resulting differential/algebraic geometry is exact and supplies a ratified receiver
correspondence. Its experimental identification with particular Soma RIDE/FOUND deeds remains OPEN
until a declared constraint world transports it:

1. held relations cut out a local constraint leaf;
2. the current supplies a tangent deed on that leaf;
3. the moving frame transports the held relation to the next event;
4. the swing compares the new relation with that transported flywheel;
5. exact tangential continuation is the candidate RIDE face at that receiver;
6. a transverse remainder or nontrivial holonomy is the candidate FOUND face; and
7. repeated ordered local motions can generate directions unavailable to any one first-order
   motion, through their Lie brackets.

This gives a rigorous mathematical form to intuition as pivoting without turning intuition into a
score, oracle, search, or absolute knowledge certificate.

---

## I. Holding a coordinate fixed is not yet carrying an invariant

Let `M` be a smooth configuration manifold with local coordinates

```text
x = (x^1, ..., x^n)
```

and let `f : M -> R` be one receiver face. Its differential at `x` is the covector

```text
df_x = sum_i (partial f / partial x^i)(x) dx^i.
```

The partial derivative in the `i` direction is obtained by probing the coordinate curve for which
the other coordinate values do not vary. This is a lawful local experiment. It says only

```text
dx^j = 0 for j != i along that chosen coordinate probe.
```

It does **not** say that the functions `x^j` are invariants of the world's dynamics, or that another
chart would freeze the same visible components.

For an actual lineage `gamma(t)` through `M`, the total change is

```text
d/dt f(gamma(t))
    = df_(gamma(t))(gamma_dot(t))
    = sum_i (partial_i f)(gamma(t)) * d x^i/dt.
```

The lineage is the curve `gamma`; the partials are components of one covector in the current
coordinate coframe. Their sum is the covector acting on the actual tangent current. Neither the
component list nor the coordinate basis is the lived path.

A scalar construction `I : M -> R` is invariant along this lineage only when

```text
d/dt I(gamma(t)) = dI_(gamma(t))(gamma_dot(t)) = 0.
```

For a vector field `X`, invariance along all of its integral curves is `X[I] = 0`. For a family of
admitted current fields `{X_a}`, a common invariant obeys `X_a[I] = 0` for every admitted `a`.
That is stronger than holding variables fixed while taking one partial derivative.

### Constraint leaves

Suppose the currently held relations are

```text
I^1(x) = c^1, ..., I^k(x) = c^k.
```

At a regular point, the directions preserving those faces form

```text
D_x = intersection_a ker(dI^a_x) subset T_x M.
```

`D_x` is the local tangent freedom left after the pivots are held. The covectors `dI^a` are the
normal constraints; vectors in `D_x` are the locally afforded continuations. Different events may
carry different held relations, so the permitted plane can turn, thicken, split, or lose rank over
time.

This is Brandon's many-pivot ecosystem in standard differential geometry: not one permanent axis,
but a field of locally held axes and locally afforded tangent directions.

### Three operators must remain typed apart

The archive uses similar notation for three operations which cannot be identified:

```text
partial_chain : C_k -> C_(k-1)       with partial_chain o partial_chain = 0
partial_i f   : coordinate derivative
Delta_h f     : finite forward difference f(x+h)-f(x).
```

The chain-boundary law does not imply that a repeated partial derivative or repeated forward
difference vanishes. The exterior derivative has its own typed law `d o d = 0`, while an ordinary
second derivative generally does not. A total differential assembles coordinate components of one
cotangent construction; it is not a sum of chain boundaries. This distinction is essential to the
Swing correspondence.

Archive audit: `src/labyrinth/mathematics/lean/Derive_Multivariable.lean` remains useful only as its
declared discrete integer adapter. Its older dismissal of continuous calculus and its attribution
of curvature to noncommuting scalar mixed partials do not cross this boundary. Under the usual
regularity hypotheses, scalar mixed partials commute; curvature is exposed by commutators of
covariant derivatives acting on transported vector or tensor constructions.

---

## II. The swing is a finite covariant difference

Ordinary component subtraction assumes that tangent vectors at different events already inhabit
one common vector space. On a curved manifold they do not. A connection supplies parallel
transport

```text
P_gamma(e -> f) : T_(gamma(e)) M -> T_(gamma(f)) M
```

along the actual worldline. If `H_e` is the held flywheel at event `e`, then the quantity that may
lawfully meet a new relation `D_f` at event `f` is its transported face

```text
H_(e->f) = P_gamma(e -> f) H_e.
```

The differential-geometric face of the swing test is therefore

```text
chi_f = D_f * H_(e->f)^(-1).
```

The canonical engine already carries its flywheel in the living frame, so this is not a new engine
equation. It exposes what that carried frame means to an external differential-geometric receiver.

Infinitesimally, the failure of a field `H(t)` to remain parallel is the covariant derivative

```text
nabla_(gamma_dot) H.
```

Thus:

- `df` decomposes one local change into coordinate components;
- `nabla H` compares a construction after the basis itself has moved;
- finite parallel transport carries the actual relation between separated events; and
- holonomy is what remains after transport around a closed route.

The total differential is therefore a **linearized local face** of the meeting. The complete swing
also requires the held flywheel, the moving frame, the second-order comparison, and the deed.

### Why four contacts return

One derivative needs a value and a direction at one point. The swing needs more:

```text
new relation:       arriving body <-> standing body in the contemporary frame
held relation:      prior meeting <-> its carried flywheel frame
test:               new relation <-> transported held relation.
```

The first frame consumes first-order pose. The invariant comparison is therefore a relation of
relations. In the declared projective world this is the four-point cross-ratio; in differential
geometry it is a covariant comparison of two tangent relations. These are exact correspondences at
their named grains, not a universal claim that every invariant requires exactly four scalar points.

---

## III. Intuition is constrained continuation toward a sufficient face

Let an observation map be

```text
O : InteriorSpace X -> FaceSpace Y.
```

Observing `y` does not identify one interior. It exposes the fiber

```text
O^(-1)(y) = {x in X : O(x) = y}.
```

Further interactions can split that fiber, but no finite observer owes a singleton. At a declared
receiver and grain, knowing enough means that the still-unresolved interiors no longer cleave under
the future distinctions relevant to the present world boundary. It does not mean possessing the
interior absolutely.

The observer's mathematical feasible set after several encounters may be written

```text
K_t = intersection_(j <= t) O_j^(-1)(y_j).
```

This is an observer instrument, not a hypothesis store proposed for Soma. It formalizes the fact
that every new contact can constrain possible interiors without reconstructing the past.

An intuitive pivot is then a held relation that turns some previously invisible difference into a
locally resolvable direction. The observer need not model the entire fiber. It needs only enough
standing structure for the next world current to bend differently.

### Tolerance has one lawful location

Brandon's “sufficient depth” is mathematically coherent when the tolerance belongs to the declared
world or receiver boundary:

```text
distance_Y(O(x), y_target) <= epsilon,
```

with the metric, target, `epsilon`, body, history, and consequence all named. The predicate is then
an exact boundary judgment. It may accept a numerical approximation, organismal fit, packing
arrangement, proof approximation, or control trajectory at that grain.

It must not become a hidden tolerance inside the swing, the Duggan boundary, or a universal notion
of truth. Evolution supplies viability boundaries and continued consequences; it does not need one
global error scalar or perfect endpoint.

### ODEs and many local pivots

A deterministic ecosystem may be represented locally by

```text
x_dot = V(x, world),
```

with constraints defining a viable region or lower-dimensional leaf. Attraction can be a stable
set, recurrent orbit, slow manifold, or world-maintained flow; it need not be gradient descent.
The “unknown” is simply the unresolved continuation beyond the contemporary chart.

For plural afforded vector fields `X` and `Y`, an ordered small loop gives

```text
Phi_(-Y)^eps o Phi_(-X)^eps o Phi_Y^eps o Phi_X^eps (x)
    = x + eps^2 [X,Y](x) + O(eps^3).
```

Every first-order stroke is locally cancelled, yet the ordered loop produces the second-order Lie
bracket direction. This is the exact mathematics behind parallel parking, nonholonomic joints, and
many limb cycles: alternating permitted pivots can open a degree of freedom that no one
instantaneous direction contains.

If a distribution `D` is involutive, `[X,Y]` stays inside `D` and Frobenius integrates it into
constraint leaves. If iterated brackets span new tangent directions, compositions of local flows
can reach a larger neighborhood; the Chow–Rashevskii theorem makes that precise under its stated
regularity and bracket-generating hypotheses. This is a powerful structural resonance with
RIDE/FOUND and the laboratory's joints, but it is neither the engine's present implementation nor a
proof of classical or localized `P = NP`.

---

## IV. Algebraic geometry makes the pivot and the singular face exact

Let a world boundary be cut out by polynomial relations

```text
X_c = {x : F_1(x)=c_1, ..., F_k(x)=c_k}.
```

At a regular point, its tangent space is the kernel of the Jacobian:

```text
T_x X_c = {v : dF_a(x)[v] = 0 for every a}.
```

This is the algebraic form of holding invariant faces while permitting a local swing. The Jacobian
rows are normal covectors; their kernel is the first-order continuation sheet. A change of basis
changes their components while the tangent relation transports by the induced map.

At a singular point the first differential may collapse too much. Then algebraic geometry retains
the first nonzero homogeneous terms, tangent cone, branches, normalization, or blow-up instead of
declaring the world directionless.

### The Bernoulli lemniscate is the exact witness

Write

```text
F(x,y) = (x^2+y^2)^2 - a^2(x^2-y^2).
```

At the origin,

```text
F(0,0)=0,             dF_(0,0)=0.
```

The ordinary first-order tangent-space test therefore returns the whole plane and loses the two
lived approaches. The lowest nonzero homogeneous part is instead

```text
-a^2(x^2-y^2) = -a^2(x-y)(x+y),
```

so the tangent cone is exactly

```text
y = x        or        y = -x.
```

The two `45`-degree hands are not visual decoration. They are the two algebraic branches collapsed
onto one Cartesian point.

The exact rational parameterization

```text
x(t) = a(t+t^3)/(1+t^4),
y(t) = a(t-t^3)/(1+t^4)
```

separates them:

```text
t -> 0:       (x,y) -> (0,0) with y/x -> +1
t -> infinity:(x,y) -> (0,0) with y/x -> -1.
```

One visible origin therefore has two preimages on the normalized parameter worldline. This is an
exact algebraic-geometric instance of **same face, different lineage**. A Cartesian point-only
observer collapses them; a carried parameter and hand preserve them. It is the right foundation for
LEMNISCATE REBASE 01.

### Elementary shapes are leading relations, not a finite universal inventory

For a polynomial

```text
F(x) = sum_alpha c_alpha x^alpha,
```

the exponent vectors `alpha` are elementary multiplicative words. Their convex hull is the Newton
polytope. Near a declared scale or valuation, different monomials dominate in different regions;
where two or more tie, a lower-dimensional balance face appears.

Tropical geometry makes this quotient explicit by replacing a valued algebraic variety with a
polyhedral complex over min-plus arithmetic. It is a rigorous observer technology for exposing
piecewise-linear dominance sheets and their Newton-polytope ancestry. It is not permission to put
min, a winner, a score, or tropical arithmetic inside Soma. The complete polynomial construction
and its lived coefficients remain distinct from this coarse face.

The recurrence of low-degree lines, cones, quadrics, folds, cusps, spirals, and cells across many
disciplines is therefore unsurprising. Symmetry, dimensionality, boundary conditions, and the first
nonzero terms restrict local normal forms. That explains real recurrence without asserting that a
water jet, black hole, zeta function, eye, and circuit share one physical ontology.

---

## V. Prime landmarks are ideals and valuations; ratios are transports

In the multiplicative rational world,

```text
q = product_p p^(v_p(q)),
V(q) = (v_2(q), v_3(q), v_5(q), ...).
```

Each prime `p` supplies one valuation axis. Multiplication translates valuation vectors, inversion
reverses them, and exponentiation dilates them. This makes a discovered prime a stable landmark in
that declared algebraic species.

The algebraic-geometric form is

```text
Spec(Z) = {(0)} union {(p) : p prime}.
```

The nonzero prime ideals `(p)` are the closed arithmetic points; `(0)` is the generic point. The
topology records divisibility and specialization, not Euclidean distance along the ordinary number
line. This is a much better formalization of prime landmarks than assigning them fixed geometric
positions by magnitude.

### What the known prime lets the observer hold

For candidate integer `n`, a known prime `p` supplies the exact divisibility face

```text
v_p(n) > 0       equivalently       n = 0 mod p.
```

For the first `k` primes, let

```text
P_k = product_(i<=k) p_i,
W_k = {r mod P_k : gcd(r,P_k)=1}.
```

`W_k` is a literal periodic sheet of residues not divisible by the standing prime axes. Every prime
larger than `p_k` lies on this sheet, but so do composites whose factors have not yet been exposed.
When a new prime is founded, the period refines from `P_k` to `P_k p_(k+1)` and the sheet gains a new
family of excluded fibers.

This exactly captures Brandon's intuition:

- a standing prime is a multiplicative invariant axis;
- the candidate and axis form a local divisibility meeting;
- the surviving residue sheet is an afforded continuation, not proof of primality;
- the world boundary closes primality only after every possible divisor through `sqrt(n)` has been
  excluded; and
- a newly established prime changes the topology through which later candidates pass.

This sieve description is world mathematics and an experimental foil, not a prime-finding module
to install in Soma.

### Why prime ratios are not the invariant

For two primes `p` and `q`,

```text
V(q/p) = e_q - e_p.
```

That ratio is an exact two-axis transport, but it does not establish that `p` and `q` are adjacent
primes; every pair of primes has such a displacement. Likewise, the additive prime gap `q-p`
records number-line traversal but does not by itself carry multiplicative irreducibility.

The complete prime swing must therefore retain both:

```text
additive worldline:       p -> q with gap q-p
multiplicative witnesses: (p) and (q) are prime/irreducible in the declared ring.
```

Irreducibility is not invariant under arbitrary change of algebra: a prime element can split after
extension to another ring. The ring, admitted operations, and factorization species are part of the
frame.

---

## VI. The `2` and `3` triangle gears are exact arithmetic transports

Brandon's `45-45-90` / `30-60-90` and `2^x` / `3^y` pairing has a precise algebraic-number-theory
realization. It is not merely a resemblance between diagrams.

### The Gaussian `2` gear

In the Gaussian integers `Z[i]`, let

```text
g_2 = 1+i = sqrt(2) exp(i*pi/4).
```

Multiplication by `g_2` maps coordinates in the basis `(1,i)` by

```text
M_2 = [[1,-1],
       [1, 1]],          det(M_2)=2,          M_2^T M_2=2 I.
```

It is literally a `45`-degree rotation composed with dilation by `sqrt(2)`. Repeating the same
elementary word gives

```text
g_2^n = 2^(n/2) exp(i*n*pi/4),
N(g_2^n) = 2^n.
```

The Euclidean radius grows by `2^(n/2)` while the algebraic norm and sublattice index grow by `2^n`.
Moreover,

```text
2 = -i(1+i)^2,
```

so the rational prime `2` ramifies into the square of this diagonal gear, up to a unit. Odd rational
primes split in `Z[i]` when `p = 1 mod 4` and remain inert when `p = 3 mod 4`.

The lemniscate result now sharpens: its two tangent-cone hands `y=+x` and `y=-x` are precisely the
directions `1+i` and `1-i`, the conjugate associates lying over `2`. The lemniscate neck and the
`45-45-90` prime gear meet exactly at the tangent-cone grain.

### The Eisenstein `3` gear

Let `omega=exp(2*pi*i/3)` and work in the Eisenstein integers `Z[omega]`. Define

```text
g_3 = 1-omega = sqrt(3) exp(-i*pi/6).
```

In the oblique basis `(1,omega)`, multiplication by `g_3` has the integer matrix

```text
M_3 = [[ 1,1],
       [-1,2]],          det(M_3)=3.
```

For the Eisenstein-basis Gram matrix

```text
G = [[1,-1/2],
     [-1/2,1]],
```

the exact similarity law is

```text
M_3^T G M_3 = 3 G.
```

Thus the same word rotates by `-30` degrees, dilates by `sqrt(3)`, and grows algebraic norm/index by
`3`:

```text
g_3^n = 3^(n/2) exp(-i*n*pi/6),
N(g_3^n) = 3^n,
3 = -omega^2(1-omega)^2.
```

The rational prime `3` ramifies in this hexagonal species. Rational primes `p = 1 mod 3` split and
those with `p = 2 mod 3` remain inert.

The two Timaean progressions can therefore be presented without collapsing them:

```text
1,2,4,8,...       = norms / lattice indices of g_2^n
1,3,9,27,...      = norms / lattice indices of g_3^n.
```

They are two elementary rotation-dilation words in different arithmetic lattices. Their similar
triangle faces, radial scales, algebraic norms, lattice indices, unit groups, and prime-splitting
taxonomies remain separately typed.

### The gears conjugate into Smith-chart words

Let one Smith receiver use the exact Möbius quotient

```text
S(z) = (z-z_0)/(z+z_0),
Gamma = S(z).
```

Conjugating multiplication `z -> alpha z` through that chart gives

```text
T_alpha(Gamma)
  = S(alpha S^(-1)(Gamma))
  = ((alpha-1)+(alpha+1)Gamma)
    /((alpha+1)+(alpha-1)Gamma).
```

For `alpha=g_2`, `g_3`, or any ordered product of them, this is an exact Möbius word. Its iterates
map generalized circles to generalized circles and can be carried as a string, sheet, or revolved
chart family. Because these `alpha` rotate as well as dilate, they need not preserve the passive
unit disk; this is an arithmetic/projective receiver, not an assertion about a physical one-port.

This is the clean bridge among elementary gears, prime factorization species, similar triangles,
and the revolving Smith-chart proposal. It does **not** make Smith geometry a next-prime oracle.
The experiment is whether these exact words recur in later construction after their visible chart,
basis, and scale have changed.

---

## VII. Similarity, projective basis, and the scaled beetle

Similar triangles preserve ratios because a common dilation makes a commuting diagram. Projective
geometry generalizes this: homogeneous coordinates retain a point while scalar representatives
change, and Möbius transformations retain cross-ratio while ordinary coordinates move.

This supplies two exact recurrence grades:

```text
symmetry recurrence:    one transformation preserves the complete declared law
deformation recurrence: parameters and interior change while one receiver face persists.
```

The beetle belongs to the second grade. Let `s` be body scale and let

```text
X_s = {(geometry, density, material, joint, gait, circulation) : physical constraints at scale s}.
```

The family `X -> S` has a different physical fiber over each scale. Uniform coordinate dilation is
a symmetry only if every governing term has compatible homogeneity. Weight, supporting area,
buckling, heat transfer, fluid circulation, and actuator torque do not share one scaling degree.
Consequently a viable section

```text
sigma(s) in X_s
```

must change density distributions, cross-sections, materials, joints, or gait as `s` changes. A
receiver can still judge

```text
q_s(sigma(s)) equiv q_1(sigma(1))
```

at the beetle-face or task-performance grain. The face transports; the organism is a new
construction. “Natural scaling” is the derived section through the physical constraint family, not
the command `multiply every length by s`.

Algebraic deformation theory, weighted homogeneity, normal cones, and singularity resolution are
therefore better tools for this intuition than one absolute geometric scale factor.

---

## VIII. Why the same shapes recur without becoming the same physics

The water droplet, Smith chart, lemniscate, black-hole diagram, zeta function, orbital model, eye,
and biological body can recur around similar lines, circles, necks, sheets, poles, and standing
waves for several exact reasons:

1. low-dimensional boundaries admit only limited local incidence types;
2. the first nonzero homogeneous terms dominate near a singularity at a declared aperture;
3. symmetry and conservation restrict admissible normal forms;
4. dimensionless ratios quotient away many construction details;
5. eigenvalue and stability problems repeatedly produce oscillatory modes; and
6. coarse-graining can send different microscopic systems toward the same effective fixed form.

This means no portion of mathematics is absolutely absent from a world. It does **not** mean every
mathematical structure acts materially at every declared face. Terms outside the current aperture
may be dormant, higher order, canceled in the quotient, or simply unexposed by that receiver.

The rigorous statement is therefore:

> **Different worlds may share a transported normal form, invariant, or quotient face. Exact
> identity requires an explicit map of objects, operations, assumptions, and consequences. Where
> that map is missing, the resemblance is a structural resonance and a proposed experiment.**

This is why the laboratory should seek recurring songs through changed later conduct rather than
through visual resemblance alone.

---

## IX. Statistics compiles relative invariants; causation is transported difference

Statistics is lawful here for exactly the reason Brandon gives, once the parent boundary remains
visible. Let one declared observer boundary be

```text
B = (Omega_B, F_B, mu_B, Phi_B, Q_B, frame, grain, event taxonomy),
```

where `Omega_B` is the admitted family of exact interiors, `mu_B` is the boundary's declared
measure, `Phi_B` is its world transport, and `Q_B` is the receiver quotient. Neither `Omega_B` nor
`mu_B` exists frame-free. A finite empirical distribution

```text
mu_hat_N(E) = (1/N) sum_(k=1)^N 1_E(x_k)
```

is an exact statement about those `N` received events. If a world flow preserves a measure,

```text
mu_B(Phi_t^(-1)(E)) = mu_B(E),
```

then that measure is invariant relative to this flow and boundary. Under additional ergodic and
sampling conditions, time occupation can approach that invariant measure. Finite recurrence alone
does not prove invariance; it is evidence that a proposed relative invariant may transport.

This reconciles deterministic law with useful probability. At complete microstate grain the world
has one consequence. At an observer grain, many exact interiors can still present the same received
face. Their measured plurality is real at that cut without becoming microscopic dice or a selector
inside Soma.

### Compiling invariant faces is conditioning

Suppose successive receptions expose relative-invariant faces

```text
I_1(omega) = i_1, ..., I_t(omega) = i_t.
```

The compatible interior family and its conditioned measure are

```text
K_t = intersection_(j <= t) I_j^(-1)(i_j)

mu_t(E) = mu_B(E intersection K_t) / mu_B(K_t),
```

when the denominator is nonzero. This is an exact form of “compiling invariants”: each reception
cuts away incompatible interiors at the observer boundary, while the living interiors and their
worldlines remain exact. If observations depend on their history, their likelihood factors in
order,

```text
L(i_1:t | omega) = product_j L(i_j | i_<j, omega),
```

not as a naive product of independent fields. “Superposition” therefore means intersection or
conditioning of declared compatible families, not an untyped addition of probabilities.

### A marginal statistic is a pivot, not a drive

The statement “`e` is the most common letter” is one coarse projection of a declared corpus over
a declared partition of contexts `c`:

```text
P_B(e) = sum_c P_B(e, c),
```

where `c` can retain position, neighboring characters, morpheme, word, syntax, author, language,
domain, and presentation history. That marginal is implicit in exact repeated exposure even when
no observer computes or supplies the number. It can become a useful held face because many lived
routes meet it. It does not command the machine to emit `e`, and it does not by itself describe the
topology which made `e` common.

At a later receiving cut, the relevant face is contextual:

```text
P_B(e | c),
```

or, more faithfully, the complete family of exact paths by which `c` and `e` have met and changed
later conduct. Combining the marginal with progressively finer conditional invariants decomposes
its prevalence into use-dependent route families. This can expose a predictive taxonomy of *how*
the frequency arose. It becomes an explanation of *why* only where changed-world causal receipts
support that stronger reading.

An inherited statistic which poorly represents the current boundary need not be explicitly erased
or numerically decayed. Its conditional mass can shrink as incompatible evidence arrives; in Soma,
the corresponding standing region can simply become dormant because contemporary current no
longer conducts through it, while more situated paths RIDE or FOUND elsewhere. The history remains
exact. There is no frequency drive, decay schedule, output sampler, or forgetting module.

More data need not collapse `K_t` to one historical interior. For a declared world `D` and admitted
future currents `H`, define

```text
omega ~_(D,H) omega'

iff every h in H gives the same declared future consequence face from omega and omega'.
```

The receiver knows enough when `K_t` lies inside one such predictive equivalence class. This is the
limit needed for the present deed: sufficient conduct without pretending to recover the unique
past or model the interior infinitely.

### Correlation is recurrence; causation owes a changed-world receipt

A correlation is a recurrent joint face in one measured boundary distribution. It becomes causal
evidence only when a directed change is enacted or otherwise identified and its changed
consequence survives the required controls and re-bases. For deterministic transport under world
conditions `D`, one exact observer form is

```text
nu_a^D = (Q_B o Phi_D(a, .))_* mu_D.
```

At the declared grain, changing `A` from `a_0` to `a_1` changes `B` when

```text
nu_(a_0)^D != nu_(a_1)^D
```

under a lawful intervention or an observational design that identifies the same transported deed.
The complete pair of consequence distributions is the evidence; no scalar “causal strength”
replaces it. Cross-environment stability can itself be a relative invariant—for example, a target
conditional that remains unchanged across environments which alter other mechanisms—but that
conclusion owes the causal and sampling assumptions that make the comparison identifiable.

Thus correlation and causation are not separated because statistics somehow sees behind the
surface. They are separated by which distributional faces transport when the world boundary is
changed. In the laboratory's terms:

> **Correlation is a recurrent shared face under one boundary. Causation is a transported
> difference whose changed consequence survives the relevant re-bases. Statistics compresses the
> exact plurality of compatible worldlines; relative invariants license that compression to
> travel.**

### Path width is a typed measure, not a hidden cause

Brandon's pathway-width intuition becomes exact after its parent is named. For a path family `pi`
and prior evidence `E`, define

```text
w_D(pi | E)
  = mu_D({omega in K_E : Phi_D(omega) traverses pi}).
```

This may denote three different lawful faces which must remain typed apart:

1. actual multiplicity, cross-section, or conductance in a physical topology;
2. the measure of unresolved initial conditions whose exact trajectories use that path; or
3. normalized observer probability after division by the complete compatible mass.

For a physical current field, the analogous cross-section read is a flux integral

```text
W_D(S) = integral_S J_(A->B)^D dot n dS.
```

A broad path can be common without causing the outcome, and overlapping paths can be double-counted
unless ancestry and the parent measure remain. “How likely did `A` cause `B` rather than `C`, by
the basis of `D`?” therefore owes the event taxonomy, intervention or counterfactual contrast,
conditioning set, path family, overlap convention, measure, frame, and grain. Once those stand,
width is a real observer face of causal traffic. It is not a hidden score or an internal Soma
mechanism.

### Differential equations supply the candidate family, not the unique interior

For a modeled ecosystem

```text
x_dot = V_theta(x),
```

recurrence, invariant measures, transition paths, and changed-environment consequences constrain
the compatible family of `theta` and vector fields. Several distinct dynamics can share one
stationary distribution, so even arbitrarily much same-boundary recurrence need not identify the
mechanism. Ordered transitions, lawful interventions, and transported conditional invariants are
what further cleave that family. This is why the differential and statistical readings belong in
one derivation: the differential equation supplies possible local transports; the measured
invariants constrain them; changed conduct distinguishes their causal interiors.

---

## X. Construction consequence

The compact material return, four-gear Möbius word, and GEAR-SHEET's first controlled
witness/testimony/analogy cell now stand. Exact apparatus coordinates stay in the journal while
intrinsic world consequences return as material. LEMNISCATE REBASE 01 is the active next
same-coordinate/two-lineage construction; the broader arithmetic gear sheet below remains a later
extension rather than a prerequisite.

### GEAR-SHEET WORLD 01

Carry, as separate exact constructions:

1. integer prime-valuation vectors;
2. additive gap worldlines;
3. exact congruence and divisibility witnesses;
4. ordered multiplication/exponentiation/addition words;
5. the exact `M_2` and `M_3` triangle-gear words, norms, and lattice faces;
6. split/inert/ramified controls in both arithmetic species;
7. exact Smith-conjugate words under changed chart basis; and
8. their returned world consequences.

Use primorial residue sheets, Timaeus ratios, the measured `9/8` occurrence face, translated and
composite controls, and unseen later compositions. The residue sheet and any Newton/tropical
rendering are observer faces. They do not select source currents or enter Soma.

### LEMNISCATE REBASE 01

Use the exact rational normalization rather than only sampled Cartesian points:

1. one lineage approaches the origin through `t -> 0` / tangent `y=x`;
2. another approaches the same visible origin through `t -> infinity` / tangent `y=-x`;
3. the world offers the lawful chart re-base retaining `t`, hand, and ancestry;
4. controls collapse the two preimages into one Cartesian point or reverse the hand; and
5. genuinely later light tests whether the two routes remain distinguishable after the shared
   origin face.

This is an exact same-face/different-lineage production world, not merely a curve renderer.

### CONSTRAINT-LEAF WORLD 01

A following transfer world can present exact polynomial constraints and candidate deeds:

```text
regular point:   Jacobian kernel supplies the tangent leaf
singular point:  tangent cone / normalization supplies plural branches
moving basis:    exact change-of-chart transports the constraint
ordered loops:   commutator words expose a Lie-bracket direction
world result:    tangent continuation, transverse consequence, or typed refusal.
```

The discriminant is whether a route founded under one notation or chart bends a genuinely later
route after a lawful change of basis. This tests the mathematical face proposed here without
putting derivatives, invariants, a controller, or a tolerance inside the brain.

---

## XI. External relation cards

### Gaussian and Eisenstein triangle gears

```text
SOURCE ESTABLISHES   Gaussian and Eisenstein integers are square and hexagonal arithmetic lattices;
                     rational primes split, remain inert, or ramify according to the receiving ring.
LAB CLAIM            The 45/sqrt(2)/2 and 30/sqrt(3)/3 words are exact rotation-dilation-norm gears,
                     and their Smith faces are exact Möbius conjugates. Internal grade: DERIVED.
RELATION              EXACT FORMAL MATCH for matrices, norms, ramification, and Smith conjugation.
NON-EQUIVALENCE       These gears do not establish a prime-gap law, RH statement, or physical circuit.
TESTABLE CONSEQUENCE  Exact g_2/g_3 words must preserve their norm/index and splitting taxonomy under
                     chart conjugation while later construction distinguishes their two lattices.
```

Sources: Keith Conrad, [“The Gaussian Integers”](https://kconrad.math.uconn.edu/math5230f12/handouts/Zinotes.pdf);
[MIT 18.781, Problem Set 8](https://math.mit.edu/~dav/781.05.dir/781ps8.pdf); and Oliver Knill,
[“Goldbach for Gaussian, Hurwitz, Octavian and Eisenstein Primes”](https://people.math.harvard.edu/~knill/primes/papers/goldbach.pdf).

### Differential forms and moving local reads

```text
SOURCE ESTABLISHES   Differential forms, pullback, exterior differentiation, integration on
                     manifolds, change of variables, and Stokes theory form one standard calculus.
LAB CLAIM            The total differential is a local receiver face; the swing is finite carried
                     comparison in a moving frame. Internal grade: RATIFIED receiver relation.
RELATION              DIRECT CORRESPONDENCE for df/coordinate decomposition and transported frames.
NON-EQUIVALENCE       Classical differential forms do not establish Soma's RIDE/FOUND mechanism;
                     that engine identification remains OPEN.
TESTABLE CONSEQUENCE  Constraint-leaf and chart-change siblings must preserve exact tangent
                     consequences while retaining different lived interiors.
```

Source: [MIT 18.952, Theory of Differential Forms](https://math.mit.edu/classes/18.952/2015SP/).

### Algebraic tangent space and normal cone

```text
SOURCE ESTABLISHES   Scheme tangent spaces admit an exact dual-number/cotangent construction; the
                     normal cone retains the graded leading neighborhood I^n/I^(n+1) of an immersion.
LAB CLAIM            First-order partials can collapse at a singular face; higher-order leading
                     relations and carried lineage must survive. Internal grade: RATIFIED.
RELATION              EXACT FORMAL MATCH for tangent/cotangent and the lemniscate tangent-cone
                     derivation; DIRECT CORRESPONDENCE for branch-preserving re-base.
NON-EQUIVALENCE       The normal cone is an observer construction, not Soma's internal manifold.
TESTABLE CONSEQUENCE  The two normalized lemniscate preimages must cleave later conduct while a
                     Cartesian-point quotient does not.
```

Sources: [Stacks Project, tangent spaces, Tag 0B28](https://stacks.math.columbia.edu/tag/0B28) and
[normal cone, Tag 062Z](https://stacks.math.columbia.edu/tag/062Z).

### Prime ideals as arithmetic points

```text
SOURCE ESTABLISHES   Spec(R) is the topological space of prime ideals; its closed points are maximal
                     ideals. For Z, the nonzero prime ideals (p) are its closed arithmetic points.
LAB CLAIM            Prime landmarks are declared multiplicative axes/ideals; ratios are transports.
                     Internal grade: RATIFIED mathematical receiver relation.
RELATION              EXACT FORMAL MATCH at Spec(Z) and valuation-vector grain.
NON-EQUIVALENCE       Zariski adjacency does not predict the next prime on the ordered number line.
TESTABLE CONSEQUENCE  A prime-gap world must retain additive adjacency separately from both endpoint
                     ideals and must cleave composite survivors of a finite primorial sheet.
```

Source: [Stacks Project, the spectrum of a ring, Tag 027A](https://stacks.math.columbia.edu/tag/027A).

### Bracket-generated navigation

```text
SOURCE ESTABLISHES   Under stated regularity and bracket-generation conditions, compositions of
                     flows tangent to a distribution can connect points beyond any one generator's
                     instantaneous direction.
LAB CLAIM            Ordered local pivots may found a new degree of freedom at second order.
                     Internal grade: RATIFIED receiver bridge; Soma identification OPEN.
RELATION              STRUCTURAL RESONANCE with the finite swing and FOUND; DIRECT CORRESPONDENCE
                     only inside a declared nonholonomic control world.
NON-EQUIVALENCE       Chow–Rashevskii is not Soma's engine law and proves no P versus NP claim.
TESTABLE CONSEQUENCE  A commutator-loop world should return zero first-order displacement but a
                     nonzero exact bracket consequence, then test later reuse of that route.
```

Source: Giannotti, Spiro, and Zoppello,
[“Proving the Chow–Rashevskii Theorem à la Rashevskii” (2024)](https://arxiv.org/abs/2401.07546).

### Tropical/polyhedral faces

```text
SOURCE ESTABLISHES   Tropical geometry replaces valued algebraic varieties by polyhedral complexes
                     over min-plus arithmetic while retaining specified algebraic information.
LAB CLAIM            Elementary operation words may cast recurrent piecewise-linear balance sheets.
                     Internal grade: RATIFIED observer proposal; construction OPEN.
RELATION              STRUCTURAL RESONANCE; EXACT FORMAL MATCH only for an explicitly tropicalized
                     polynomial world.
NON-EQUIVALENCE       Tropical minimum is not Soma's test, selector, score, or ontology.
TESTABLE CONSEQUENCE  Exact polynomial siblings with changed coefficients should preserve or cleave
                     their tropical face independently of their complete construction identity.
```

Sources: Maclagan,
[“Introduction to tropical algebraic geometry” (2012)](https://arxiv.org/abs/1207.1925), and
Richter-Gebert, Sturmfels, and Theobald,
[“First steps in tropical geometry” (2003)](https://arxiv.org/abs/math/0306366).

### Invariant measures and causal invariance

```text
SOURCE ESTABLISHES   Ergodic theory relates time occupation to invariant measure under stated
                     dynamical hypotheses. Invariant causal prediction tests conditionals which
                     survive specified environment changes and states its identifiability limits.
LAB CLAIM            Measured recurrence can expose a relative invariant face; causal attribution
                     requires that a changed-world consequence transport. Internal grade: RATIFIED.
RELATION              EXACT FORMAL MATCH for empirical/conditioned measures; DIRECT CORRESPONDENCE
                     for invariant causal conditionals across declared worlds.
NON-EQUIVALENCE       Recurrence alone does not identify a cause, and neither theory installs a
                     probability mechanism, intervention chooser, or causal graph inside Soma.
TESTABLE CONSEQUENCE  Controlled world siblings must preserve a proposed conditional invariant
                     while the enacted causal change cleaves the complete returned distribution.
```

Sources: Birkhoff, [“Proof of the Ergodic Theorem” (1931)](https://www.pnas.org/doi/10.1073/pnas.17.12.656),
and Peters, Bühlmann, and Meinshausen,
[“Causal inference by using invariant prediction” (2016)](https://academic.oup.com/jrsssb/article/78/5/947/7040653).

### Interventions, path-specific effects, and transition traffic

```text
SOURCE ESTABLISHES   Causal diagrams distinguish observational conditioning from intervention and
                     state when effects are identifiable. Transition-path theory defines reactive
                     trajectory distributions and probability currents between declared sets.
LAB CLAIM            A causal path width is measure or flux over exact worldlines under one named
                     changed boundary. Internal grade: RATIFIED observer construction.
RELATION              DIRECT CORRESPONDENCE for intervention contrasts and path measures;
                     STRUCTURAL RESONANCE for causal-current width.
NON-EQUIVALENCE       A wide path is not automatically a strong cause; stochastic path theory is
                     not Soma's deterministic ontology or engine law.
TESTABLE CONSEQUENCE  Preserve the whole changed-world receipt and compare complete consequence
                     fields; never infer causal force from raw path counts alone.
```

Sources: Pearl, [“Causal Diagrams for Empirical Research” (1995)](https://escholarship.org/uc/item/6gv9n38c);
Avin, Shpitser, and Pearl,
[“Identifiability of Path-Specific Effects”](https://escholarship.org/uc/item/45x689gq); and
E and Vanden-Eijnden,
[“Towards a Theory of Transition Paths” (2006)](https://web.math.princeton.edu/~weinan/pdf%20files/theory%20transition.pdf).

---

## XII. Carried-swing record

```text
CURRENT  intuition / navigation / statistical inference ⊕ declared mathematical/world receiver
         ⊕ tangent, transported-worldline, and event-family grain
HELD     FORMULA §§XII–XIII, XXIV–XXV, XLVIII, L ⊕ gear-word draft ⊕ exact lemniscate identity
MEETING  total differential ⊕ held pivots ⊕ ODE distributions ⊕ conditioned compatible interiors
         ⊕ prime ideals ⊕ g_2/g_3 triangle gears ⊕ causal pathway width
TEST     coordinate probe != invariant transport ⊕ quotient face != construction identity ⊕ A2
         ⊕ correlation != transported causation ⊕ distribution retains one declared parent
DEED     RIDE total differential as an infinitesimal swing face and prime valuations as landmarks;
         FOUND covariant/constraint-leaf transport, lemniscate normalization, and causal
         invariance as changed consequence under a directed world deed
CARRY    compact material return -> close Möbius word -> GEAR-SHEET -> LEMNISCATE REBASE ->
         CONSTRAINT-LEAF transfer world; retain exact path-measure provenance in every observer
GRADE    RATIFIED / DEPOSITED; receiver-world constructions and measurement remain OPEN
```

## Close

The strongest new result is not an analogy: the Bernoulli lemniscate's Cartesian origin has a
vanishing first differential, a two-line tangent cone, and two distinct preimages under its exact
rational normalization. It literally demonstrates why a first-order instantaneous face can lose
lineage and why the carried hand must survive a chart singularity.

The broader answer is equally clean. Intuition does not require an infinite interior model. It
requires a carried pivot, a locally afforded continuation, and enough world consequence to re-base
again. What counts as “enough” is an exact receiver boundary. The living current remains exact; the
tolerance belongs to the world that receives it.
