#import "schema.typ": entry

#let geometry-calculus = (
  entry(
    id: "H.0200",
    kind: "Definition",
    grade: "definition",
    title: [Axis, unit, coordinate, and ratio],
    depends: ("H.0002", "H.0003"),
    statement: [
      An axis is a typed oriented one-dimensional fiber $L$. A unit is a
      nonzero local frame $u in L$. The coordinate of $v in L$ relative to
      $u$ is the scalar $[v]_u$ defined by
      $
        v=[v]_u u.
      $
      A ratio compares two commensurable quantities after a transport into one
      common one-dimensional fiber.
    ],
    transformations: [
      If $u'=a u$ with $a != 0$, then
      $
        [v]_(u')=a^(-1)[v]_u.
      $
      Thus a receiver may normalize any nonzero $v$ to coordinate $1$ by
      selecting $u'=v$; the transition map retains the discarded scale.
    ],
    boundary: [
      The scalar $1/2$ is not meaningful without the two compared axes, their
      units, and orientation. Coordinate sign may change under orientation
      reversal while unsigned length does not.
    ],
    source: [Elementary one-dimensional linear algebra with holonic unit interpretation.],
  ),
  entry(
    id: "H.0201",
    kind: "Definition",
    grade: "definition",
    title: [Projective cross-ratio Swing],
    depends: ("H.0200", "H.0013"),
    statement: [
      For an ordered affine quadruple $(A,B,C,D)$ over a field, first retain
      the undivided pair
      $
        N=(C-A)(D-B),
        quad
        D_0=(C-B)(D-A),
        quad
        op("Swing")(A,B,C,D)=[N:D_0] in PP^1.
      $
      Projective pairs obey
      $
        [N:D_0]=[lambda N:lambda D_0]
        quad (lambda != 0).
      $
      Only on the chart $D_0 != 0$ may a quotient receiver report
      $chi=N/D_0$. The ordered points, pair, orientation, and chart remain the
      complete Swing carrier.
    ],
    transformations: [
      Three ordered distinct marks select a projective chart by
      $(A,B,C) mapsto (infinity,0,1)$; the fourth then has quotient coordinate
      $chi$ when that chart is admissible. Reordering the marks generally
      applies one of the six anharmonic transforms rather than preserving the
      reported quotient.
    ],
    boundary: [
      `chi` outside this projective carrier must declare its own arguments and
      invariance law. Equal quotient faces do not identify source occurrences or
      paths. Four is the local population of one cross-ratio, not a universal
      bound on receivers.
    ],
    source: [
      Classical projective geometry; Holobrochos conservation and Solve records
      supply the undivided ratio and path-retention requirement.
    ],
  ),
  entry(
    id: "H.0202",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Möbius invariance of the Swing],
    depends: ("H.0201",),
    statement: [
      For
      $
        g(z)=frac(alpha z+beta,gamma z+delta),
        quad
        alpha delta-beta gamma != 0,
      $
      and every admissible quadruple,
      $
        op("Swing")(g A,g B,g C,g D)=op("Swing")(A,B,C,D)
        quad "in " PP^1.
      $
    ],
    derivation: [
      Direct subtraction gives
      $
        g(x)-g(y)
        =
        frac((alpha delta-beta gamma)(x-y),
        (gamma x+delta)(gamma y+delta)).
      $
      Substitute this identity into the four differences defining the pair.
      Its two coordinates acquire one common nonzero multiplier: the
      determinant appears twice and every local chart denominator appears in
      both coordinates. Projectivization removes that common multiplier. The
      quotient equality follows only on an admissible denominator chart.
    ],
    transformations: [
      This is exact receiver covariance under $"PGL"_2$. It is the elementary
      model of a value retained while its coordinate chart changes.
    ],
    boundary: [
      Equal projective Swing classifies ordered distinct quadruples on the
      projective line up to projectivity; it does not classify arbitrary causal
      diagrams.
    ],
    source: [Classical projective-line theorem; independently rederived above.],
  ),
  entry(
    id: "H.0203",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Simplicial boundary squares to zero],
    depends: ("H.0010",),
    statement: [
      For an oriented $n$-simplex
      $[v_0,dots.c,v_n]$, define
      $
        partial [v_0,dots.c,v_n]
        =
        sum_(i=0)^n (-1)^i
        [v_0,dots.c,hat(v_i),dots.c,v_n].
      $
      Then $partial_(n-1) partial_n=0$.
    ],
    derivation: [
      Deleting vertices $i<j$ can be performed in two orders. The order
      $i$ then $j$ has sign $(-1)^(i+j-1)$; the order $j$ then $i$ has sign
      $(-1)^(i+j)$. Each codimension-two face therefore occurs exactly twice
      with opposite signs.
    ],
    transformations: [
      This is the exact algebraic carrier of internal-face cancellation.
    ],
    boundary: [
      The identity requires a chain complex and its orientation convention. It
      is not a universal law attached to every use of the word boundary.
    ],
    source: [Classical simplicial homology; independently rederived above.],
  ),
  entry(
    id: "H.0204",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Discrete fundamental theorem and causal parity],
    depends: ("H.0203", "H.0101"),
    statement: [
      For a path $v_0 arrow.r v_1 arrow.r dots.c arrow.r v_n$ and a potential
      $f$,
      $
        sum_(k=0)^(n-1) (f(v_(k+1))-f(v_k))
        =
        f(v_n)-f(v_0).
      $
      Every internal event appears once with positive and once with negative
      orientation.
    ],
    derivation: [
      Expand the sum. Terms $+f(v_k)$ and $-f(v_k)$ cancel for
      $0<k<n$, leaving only the oriented boundary values.
    ],
    transformations: [
      Reversing the path negates the boundary. Concatenating two paths cancels
      their shared endpoint. This is the elementary time/causal-parity carrier
      over orders of events.
    ],
    boundary: [
      Cancellation supplies conservation for exact differences. A physical
      constitutive law, storage term, or dissipative source must still be
      specified in its own domain.
    ],
    source: [Finite telescoping identity.],
  ),
  entry(
    id: "H.0205",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Kirchhoff cycle identity for exact potentials],
    depends: ("H.0204",),
    statement: [
      On a closed oriented path $v_n=v_0$,
      $
        sum_(k=0)^(n-1)
        (f(v_(k+1))-f(v_k))
        =
        0.
      $
      Equivalently, the integral of an exact discrete one-form around a cycle
      vanishes.
    ],
    derivation: [
      Apply H.0204 and use $f(v_n)=f(v_0)$.
    ],
    transformations: [
      This is the pure mathematical core of Kirchhoff's voltage law. A
      nonzero cycle integral witnesses a non-exact one-form, an enclosed flux,
      a singularity, or an incompletely represented source.
    ],
    boundary: [
      It does not assert instantaneous physical equilibrium. Storage and
      dissipation can make a subsystem's boundary flux nonzero over a finite
      interval while the enlarged closed accounting still balances.
    ],
    source: [Graph cohomology / telescoping identity.],
  ),
  entry(
    id: "H.0206",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Chain rule as transport composition],
    depends: ("H.0105",),
    statement: [
      If $f : U arrow.r V$ is differentiable at $x$ and
      $g : V arrow.r W$ is differentiable at $f(x)$, then
      $
        D(g circle f)_x
        =
        D g_(f(x)) circle D f_x.
      $
      In one dimension,
      $
        frac(d,d x) e^(k x)=k e^(k x).
      $
    ],
    derivation: [
      Write
      $
        f(x+h)=f(x)+D f_x h+r_f(h),
        quad
        norm(r_f(h))/norm(h) arrow.r 0,
      $
      and apply the corresponding expansion for $g$. The linear term is the
      composite derivative; every remaining term divided by $norm(h)$ tends
      to zero.
    ],
    transformations: [
      The factor $k$ records the inner reparameterization. Dropping it collapses
      the causal chart change.
    ],
    boundary: [
      Differentiability and the topological vector-space hypotheses are
      required. A symbolic substitution is not automatically differentiable.
    ],
    source: [Classical Fréchet chain rule; independently sketched above.],
  ),
  entry(
    id: "H.0207",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Change of variables carries the Jacobian],
    depends: ("H.0206",),
    statement: [
      For an orientation-preserving $C^1$ diffeomorphism
      $phi : U arrow.r V$ and integrable $f$,
      $
        integral_V f(y) dif y
        =
        integral_U f(phi(x)) abs(det D phi_x) dif x.
      $
    ],
    derivation: [
      Linear maps scale infinitesimal $n$-volume by $abs(det D phi_x)$.
      The derivative is the exact first-order limit of the increment quotient.
      Apply its determinant scaling to a refining partition and invoke the
      measure-theoretic change-of-variables theorem in the limit.
    ],
    transformations: [
      Cartesian-to-polar transport in two dimensions has
      $
        (x,y)=(r cos theta,r sin theta),
        quad
        abs(det D phi)=r,
      $
      hence $dif x dif y=r dif r dif theta$.
    ],
    boundary: [
      Noninjective maps require multiplicity; singular charts require an
      appropriate decomposition. Rebase is not measure-preserving unless the
      Jacobian says so.
    ],
    source: [Classical change-of-variables theorem.],
  ),
  entry(
    id: "H.0208",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Fundamental theorem of calculus],
    depends: ("H.0204", "H.0206"),
    statement: [
      If $f$ is continuous on $[a,b]$ and
      $
        F(x)=integral_a^x f(t) dif t,
      $
      then $F'(x)=f(x)$ in the interior and
      $
        integral_a^b f(x) dif x=F(b)-F(a).
      $
    ],
    derivation: [
      The difference quotient is
      $
        frac(F(x+h)-F(x),h)
        =
        frac(1,h) integral_x^(x+h) f(t) dif t.
      $
      Continuity squeezes this local average to $f(x)$. Summing local
      differences telescopes to the boundary values, the continuum face of
      H.0204.
    ],
    transformations: [
      Differentiation and integration are inverse only under the stated
      regularity and boundary conditions.
    ],
    boundary: [
      A “holonic limit” is not a new limit operation until its topology or
      convergence receiver is specified.
    ],
    source: [Classical FTC, reconstructed from local average plus telescoping.],
  ),
  entry(
    id: "H.0209",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Mean-value and squeeze carriers],
    depends: ("H.0206", "H.0208"),
    statement: [
      If $f$ is continuous on $[a,b]$ and differentiable on $(a,b)$, then
      some $c in (a,b)$ satisfies
      $
        f'(c)=frac(f(b)-f(a),b-a).
      $
      If $g(x)<=f(x)<=h(x)$ near $a$ and both outer functions tend to $L$,
      then $f(x) arrow.r L$.
    ],
    derivation: [
      Subtract the secant line from $f$; the resulting function has equal
      endpoint values, so Rolle's theorem gives a zero derivative. For squeeze,
      every neighborhood of $L$ eventually contains both bounds and therefore
      the middle value.
    ],
    transformations: [
      On a Riemannian manifold the direct MVT equality generally becomes a
      geodesic integral or norm inequality after parallel transport. Coordinate
      values from distinct tangent spaces cannot be subtracted without that
      transport.
    ],
    boundary: [
      Neither theorem produces a global invariant from local bounds without
      connectedness, regularity, and receiver compatibility.
    ],
    source: [Classical MVT and squeeze theorem.],
  ),
  entry(
    id: "H.0210",
    kind: "Definition",
    grade: "definition",
    title: [Connection, curvature, and holonomy],
    depends: ("H.0018", "H.0206"),
    statement: [
      A connection $nabla$ compares neighboring fibers by covariant
      differentiation or parallel transport. Its curvature is
      $
        R(X,Y)
        =
        [nabla_X,nabla_Y]-nabla_([X,Y]).
      $
      Holonomy is the automorphism obtained by parallel transport around a
      closed loop.
    ],
    transformations: [
      Curvature is the infinitesimal residual between two ordered transport
      paths. Under a change of frame it transforms covariantly; scalar
      invariants such as traces require additional contraction.
    ],
    boundary: [
      One projected receiver path supplies order, not intrinsic curvature.
      Curvature requires a connection and comparison of alternate transports.
    ],
    source: [Standard differential geometry with comparison-cell interpretation.],
  ),
  entry(
    id: "H.0211",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Finite and convergent geometric series],
    depends: ("H.0109",),
    statement: [
      For every $r$ and integer $N>=0$,
      $
        (1-r) sum_(n=0)^N r^n
        =
        1-r^(N+1).
      $
      If $abs(r)<1$ in a complete normed field, then
      $
        sum_(n=0)^infinity r^n=frac(1,1-r).
      $
    ],
    derivation: [
      Multiply the finite sum by $1-r$; adjacent powers cancel. Under
      $abs(r)<1$, the residual $r^(N+1)$ tends to zero, so the finite identity
      has the stated limit.
    ],
    transformations: [
      For $r=1/2$ the remainder after $N$ terms is exactly
      $2^(-(N+1))$. Zeno's sequence converges because the topology admits this
      vanishing remainder; no step is erased.
    ],
    boundary: [
      The rational face $1/(1-r)$ does not replace the partial-sum lineage or
      license convergence when $abs(r)>=1$.
    ],
    source: [Elementary algebra and limit.],
  ),
  entry(
    id: "H.0212",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Exponential series, Euler transport, and logarithmic rebase],
    depends: ("H.0109", "H.0206", "H.0211"),
    statement: [
      The entire series
      $
        exp(z)=sum_(n=0)^infinity frac(z^n,n!)
      $
      satisfies $exp'(z)=exp(z)$ and
      $exp(z+w)=exp(z)exp(w)$. Defining sine and cosine by their power
      series gives
      $
        exp(i theta)=cos theta+i sin theta.
      $
      The positive real value $e$ is $exp(1)$; $pi$ is the least positive
      $theta$ with $exp(i theta)=-1$ under the standard orientation, and
      $2 pi$ is the least positive period.
    ],
    derivation: [
      Termwise differentiation is justified by infinite radius of convergence.
      The Cauchy product and the binomial theorem give the addition law.
      Separating even and odd powers of $exp(i theta)$ yields the cosine and
      sine series.
    ],
    transformations: [
      For a logarithm branch,
      $
        log_b x=frac(ln x,ln b).
      $
      Changing base is a ratio of two axis coordinates. Complex logarithms are
      multivalued by $2 pi i$ until a branch cut is selected.
    ],
    boundary: [
      $pi$ and $e$ are invariants with many lawful presentations; no one series
      is their complete identity. Euler's identity is a junction of the
      exponential, circular, complex, and additive/multiplicative structures,
      not proof that their constructions are identical.
    ],
    source: [Classical power-series construction of exponential and trigonometry.],
  ),
  entry(
    id: "H.0213",
    kind: "Definition",
    grade: "definition",
    title: [Receiver-relative configuration ecology],
    depends: ("H.0003", "H.0018", "H.0201", "H.0210"),
    statement: [
      Let actual co-presence be an incidence object
      $
        E arrow.r B_1 times dots.c times B_m
      $
      and let $X_e$ be the configuration participating at $e in E$. A joint
      receiver $q_e:X_e arrow.r product_i Y_(i,e)$ and typed comparison laws
      $b_a(e,q_e(x)) bowtie_a 0$ define
      $
        Omega_e
        =
        {x in X_e:
          b_a(e,q_e(x)) bowtie_a 0
          " for every active "a}.
      $
      Boundary equalities stratify
      $
        cal(X)={(e,x):e in E, x in X_e}.
      $
      Their discriminant is where the active boundary differentials fail their
      expected rank.

      A receiver-$i$ partial exists only for
      $V_i in T_e E$ with $D tau_j(V_i)=0$ for $j != i$. If an active boundary
      system $B(e,x)=0$ is regular on a chosen horizontal fiber, its
      continuation obeys
      $
        D_x B nabla_(V_i) x=-(D_e B)[V_i].
      $
    ],
    transformations: [
      On an admissible affine chart the Swing satisfies
      $
        frac(dif chi,chi)
        =
        frac(dif A-dif C,A-C)
        +frac(dif B-dif D,B-D)
        -frac(dif A-dif D,A-D)
        -frac(dif B-dif C,B-C).
      $
      This covector vanishes on common projective rechart motion, retaining
      only relative four-member change.
    ],
    boundary: [
      $E$ is not completed to the full product, so entangled receivers need not
      admit independent partials. Comparison laws and admissible transports
      come from the studied ecology; the calculus is agnostic, not lawless.
    ],
    source: [
      Laboratory receiver synthesis in standard incidence, stratification,
      implicit-function, and projective-differential language.
    ],
  ),
  entry(
    id: "H.0214",
    kind: "Theorem",
    grade: "proved-derived",
    title: [Receiver-stratified fundamental theorem],
    depends: ("H.0208", "H.0213"),
    statement: [
      Let a receiver path $gamma:[0,1] arrow.r E$ cross finitely many seams
      $t_k$ and carry chamber transport $cal(P)$. For a transported section
      $S$, define the exact seam jump
      $
        Delta_k S=S_(t_k^+)-J_k S_(t_k^-)
      $
      using the declared seam map $J_k$. Then
      $
        S_1-cal(P)_(0 arrow.r 1) S_0
        =
        integral_0^1
        cal(P)_(t arrow.r 1) nabla_(dot(gamma)) S_t dif t
        +
        sum_k cal(P)_(t_k^+ arrow.r 1) Delta_k S.
      $
    ],
    derivation: [
      Apply the transported fundamental theorem on each smooth chamber,
      transport every equality into the final fiber, and sum. Interior
      one-sided terms telescope except for their declared seam differences.
    ],
    transformations: [
      A wholly discrete path has only the exact jump sum. A seam-free path has
      only covariant transport. Mixed systems retain both without turning
      discrete events into false infinitesimal instants.
    ],
    boundary: [
      The theorem does not invent seam maps or convergence for infinitely many
      crossings. A scalar count is a later augmentation which forgets the
      crossing carrier.
    ],
    source: [Piecewise covariant FTC, independently assembled for the receiver ecology.],
  ),
  entry(
    id: "H.0215",
    kind: "Theorem",
    grade: "proved-derived",
    title: [Joint incidence and ordered curvature are distinct second faces],
    depends: ("H.0013", "H.0210", "H.0213", "H.0214"),
    statement: [
      For a receiver square carried into one comparison fiber, the joint
      second difference is
      $
        H_(i j) S
        =
        S_(11)-S_(10)-S_(01)+S_(00).
      $
      With ordered edge transports its curvature residual is
      $
        cal(R)_(i j)
        =
        U_(10,11) U_(00,10)
        -
        U_(01,11) U_(00,01).
      $
      In the smooth limit,
      $
        R(V_i,V_j)
        =
        [nabla_(V_i),nabla_(V_j)]-nabla_([V_i,V_j]).
      $
    ],
    derivation: [
      The first formula is finite inclusion--exclusion; the second subtracts
      the two paths around the comparison square. The example
      $S_(a b)=a b$ with identity transports has $H_(i j) S=1$ and
      $cal(R)_(i j)=0$, so joint interaction survives even when order commutes.
    ],
    transformations: [
      If $Delta_p$ is an arithmetic place difference, the mixed commutator
      $
        cal(C)_(i,p)
        =
        nabla_(V_i) Delta_p-Delta_p nabla_(V_i)
      $
      compares receiver motion with arithmetic admission.
    ],
    boundary: [
      Nonzero Hessian is not curvature, and zero curvature is not absence of
      interaction. Both require an actual admitted square; false independent
      axes may not be added to an entangled incidence base.
    ],
    source: [Finite-difference inclusion--exclusion and standard connection curvature.],
  ),
  entry(
    id: "H.0216",
    kind: "Identity",
    grade: "proved-standard",
    title: [The cosine cross term, the interference cross term, and the vertex are one term],
    depends: ("H.0201", "H.0212"),
    statement: [
      $
        c^2=a^2+b^2-2 a b cos gamma
          =(a-b e^(i gamma))(a-b e^(-i gamma))
          =abs(a-b e^(i gamma))^2,
      $
      and
      $
        abs(alpha_1+alpha_2)^2
        =abs(alpha_1)^2+abs(alpha_2)^2+2 op("Re")(alpha_1 overline(alpha_2)).
      $
      Setting $alpha_1=a$ and $alpha_2=-b e^(i gamma)$ carries the second to the
      first term by term, with
      $2 op("Re")(alpha_1 overline(alpha_2))=-2 a b cos gamma$ the single cross
      term of both.
    ],
    derivation: [
      Expand the conjugate product and apply
      $e^(i gamma)+e^(-i gamma)=2cos gamma$ (H.0212). Expand
      $abs(alpha_1+alpha_2)^2=(alpha_1+alpha_2)overline((alpha_1+alpha_2))$ and
      pair the two conjugate mixed terms.
    ],
    transformations: [
      Pythagoras is this identity with the relation switched off: at
      $gamma=pi\/2$ the cross term vanishes and the two legs return nothing about
      each other. A three-line vertex $A,B arrow.r C$ states that $C$ is returned
      *in the frame of* ${A,B}$, and the term depending on both is exactly the
      term depending on their relative turn. At $gamma=pi\/2$ the factorization is
      the Gaussian norm, so an odd prime that is the hypotenuse of a primitive
      integer right triangle splits in $ZZ[i]$ and is $1 mod 4$.
    ],
    boundary: [
      An identity of carried magnitudes across one turn. It does not assert that
      an ecology's relating is metric, that its returns are complex scalars, or
      that a diagram of an interaction is a Feynman diagram with a propagator,
      coupling, or perturbative expansion. In curved ambient geometry the
      composition law differs and recovers this only to first nonconstant order.
    ],
    source: [Classical; the identification is the laboratory's, 2026-06-14 onward.],
  ),
  entry(
    id: "H.0217",
    kind: "Boundary",
    grade: "proved-derived",
    title: [The squared modulus is the quotient, and the deletion is what makes it one],
    depends: ("H.0216", "H.0019"),
    statement: [
      For $alpha in CC$, $abs(alpha)^2=alpha overline(alpha)$ retains the
      magnitude and discards the argument. The map
      $
        CC arrow.r RR_(&gt;=0), quad alpha |-> abs(alpha)^2
      $
      is therefore a quotient by the phase circle $U(1)$, and its fibers are the
      orbits of that action.
    ],
    derivation: [
      $abs(e^(i theta)alpha)^2=abs(alpha)^2$ for every $theta$, so the map is
      constant on $U(1)$-orbits; conversely equal moduli give
      $alpha'=e^(i theta)alpha$ for some $theta$. The fibers are exactly the
      orbits.
    ],
    transformations: [
      Two consequences that are usually stated as opposites are one statement.
      *The modulus destroys information*: two routes to one consequence add as
      amplitudes and not as counts, so by H.0216 a magnitude census cannot
      distinguish reinforcement from cancellation -- the cross term is precisely
      what the quotient discards. *And that destruction is what makes the return a
      probability*: a probability is a receiver quotient (H.0019), and this is the
      quotient map. The same deletion appears at other carriers -- a truncated
      binary expansion discards the tail, a bare sign discards the turn -- and the
      phase is its fourth.
    ],
    boundary: [
      This says nothing about which quotient any application should take, and
      does not assert that a physical Born rule follows from the algebra. It also
      does not license reading $abs(dot)$ as harmless: outside a declared
      quotient, taking a modulus is a loss with no receipt.
    ],
    source: [Elementary; the reading joins H.0019's quotient to H.0216's cross term.],
  ),
  entry(
    id: "H.0218",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Divergence, continuity with storage, and Kirchhoff as a special case],
    depends: ("H.0204", "H.0205", "H.0207", "H.0208"),
    statement: [
      For compact $V$ with piecewise-smooth boundary and $C^1$ field $F$,
      $
        integral_V nabla dot F dif v = integral.cont_(partial V) F dot n dif a.
      $
      Conservation is the continuity relation
      $(partial rho)/(partial t)+nabla dot J=s$, whose discrete form is
      $q_(k+1)-q_k+B j_k=r_k$ with $B$ the oriented incidence. Kirchhoff's
      current law is the case $(partial rho)/(partial t)=0$.
    ],
    derivation: [
      The divergence theorem is generalized Stokes for the $(n-1)$-form
      $iota_F dif v$, i.e. H.0208 at top degree; continuity is its integral form
      on a fixed region, and the discrete statement is the chain law over the
      incidence complex.
    ],
    transformations: [
      Instantaneous balance is a declared regime, not a law: a node with
      $(partial rho)/(partial t) != 0$ stores, and a capacitor is exactly such a
      node. The general statement is the telescoping identity over orders of
      time, and the boundary pairing is the only channel through which an
      interior speaks.
    ],
    boundary: [
      Requires the stated regularity and fails for non-integrable divergence. A
      discrete complex must supply its own incidence rather than inherit one.
    ],
    source: [Classical vector calculus; the storage reading is the spine's chain law.],
  ),
  entry(
    id: "H.0219",
    kind: "Boundary",
    grade: "proved-derived",
    title: [Flux locality licenses a decomposition; a global constraint is a barrier],
    depends: ("H.0207", "H.0218"),
    statement: [
      Partition a region into subdomains. By H.0218 the coupling between a
      subdomain and its complement is entirely the flux through its boundary, so
      a computation over the partition decouples exactly to the extent that its
      terms are boundary fluxes; every term that is not a flux is a barrier. For
      a discrete transport operator ordered as interior and interface,
      $
        S=M_(partial partial)-M_(partial I)M_(I I)^(-1)M_(I partial),
      $
      where $M_(I I)$ is block diagonal over subdomains, so interior
      eliminations are independent and the interface solve is the only meeting.
    ],
    derivation: [
      Block elimination gives $S$; $M_(I I)$ is block diagonal because any
      interior--interior coupling across subdomains would lie on no interface,
      and the partition places every such term on the interface.
    ],
    transformations: [
      In incompressible flow, advection and diffusion are local stencils while
      $nabla dot u=0$ determines the pressure through an elliptic solve whose
      Green's function has global support: the projection is the barrier, and it
      is one because incompressibility is a statement about the domain rather
      than about any cell. The chart-transport weight is the Jacobian of H.0207,
      and the weight under which transport is unitary with no preferred measure
      is its square root.
    ],
    boundary: [
      A statement about coupling, never about cost: it says which terms need no
      communication, not that evaluating them is faster, that the interface solve
      is cheap, or that a partition is balanced. Load, latency and residency are
      apparatus testimony belonging to a measured receipt. It licenses a
      decomposition and *not* a schedule -- interchange of co-present events must
      be proved for the material at hand.
    ],
    source: [Classical domain decomposition; the barrier reading is the laboratory's.],
  ),
)
