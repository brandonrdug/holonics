#import "schema.typ": entry, bra, ket, braket, ketbra

#let topology-analysis-dynamics = (
  entry(
    id: "H.0220",
    kind: "Definition",
    grade: "definition",
    title: [Topological space and continuity],
    depends: ("H.0001", "H.0005"),
    statement: [
      A topology $tau$ on $X$ contains $emptyset,X$, arbitrary unions of its
      members, and finite intersections. A map $f:X arrow.r Y$ is continuous
      exactly when $f^(-1)(U)$ is open for every open $U subset.eq Y$.
    ],
    transformations: [
      Neighborhoods declare which local continuations a receiver can
      distinguish. Continuity preserves neighborhood incidence under pullback.
    ],
    boundary: [
      Topology alone supplies no metric, measure, causal order, or rate.
    ],
    source: [Standard general topology.],
  ),
  entry(
    id: "H.0221",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Subspace, product, and quotient topology],
    depends: ("H.0016", "H.0024", "H.0220"),
    statement: [
      The subspace topology is initial for an inclusion; the product topology
      is initial for coordinate projections; the quotient topology along a
      surjection $q:X arrow.r Q$ is final:
      $
        U subset.eq Q " is open"
        arrow.l.r
        q^(-1)(U) " is open".
      $
    ],
    transformations: [
      Restriction, co-presence, and factorization carry distinct universal
      topologies.
    ],
    boundary: [
      Quotients may fail separation properties; receiver-exact algebraic
      factorization does not automatically preserve Hausdorff geometry.
    ],
    source: [Standard initial and final topology constructions.],
  ),
  entry(
    id: "H.0222",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Compactness and connectedness],
    depends: ("H.0220",),
    statement: [
      A space is compact when every open cover has a finite subcover and
      connected when it has no separation into two nonempty disjoint open sets.
      Continuous images of compact spaces are compact; continuous images of
      connected spaces are connected.
    ],
    transformations: [
      Compactness can turn an open family of local obligations into a finite
      subfamily. Connectedness prevents a continuous receiver from splitting
      one region into a discrete two-face image.
    ],
    boundary: [
      Neither property creates a metric estimate, induction law, or analytic
      continuation without additional hypotheses.
    ],
    source: [Standard topology.],
  ),
  entry(
    id: "H.0223",
    kind: "Definition",
    grade: "definition",
    title: [Metric, Cauchy lineage, and completion],
    depends: ("H.0220",),
    statement: [
      A metric $d$ is nonnegative, symmetric, separates points, and obeys the
      triangle inequality. A Cauchy sequence satisfies
      $
        forall epsilon>0 exists N forall m,n>=N:
        d(x_m,x_n)<epsilon.
      $
      The completion adjoins equivalence classes of Cauchy sequences and is
      unique up to unique isometry over the original space.
    ],
    transformations: [
      Completion retains the complete eventual distance relation, not one
      terminal decimal face.
    ],
    boundary: [
      A metric is a declared receiver law. Different compatible metrics may
      have the same topology but different geometric scales.
    ],
    source: [Standard metric completion theorem.],
  ),
  entry(
    id: "H.0224",
    kind: "Definition",
    grade: "definition",
    title: [Paths, homotopy, and fundamental group],
    depends: ("H.0101", "H.0220"),
    statement: [
      A path is a continuous map $[0,1] arrow.r X$. Endpoint-fixed homotopy
      classes of loops at $x_0$, under concatenation, form
      $pi_1(X,x_0)$.
    ],
    transformations: [
      A returned lineage may be compared modulo continuous deformation while
      retaining its selected base occurrence.
    ],
    boundary: [
      Homotopy forgets timing, metric, embedding, and much interior geometry.
      Changing basepoint identifies groups only up to a chosen transport and
      conjugacy.
    ],
    source: [Standard algebraic topology.],
  ),
  entry(
    id: "H.0225",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Covering lift and monodromy],
    depends: ("H.0224",),
    statement: [
      For a covering $p:E arrow.r X$, every path $gamma$ and chosen
      $e_0 in p^(-1)(gamma(0))$ have a unique lift beginning at $e_0$. Loops
      induce an action of $pi_1(X,x_0)$ on the fiber $p^(-1)(x_0)$.
    ],
    transformations: [
      One received loop transports a constituent among sheets without
      identifying those sheets.
    ],
    boundary: [
      Branch points, singular seams, and arbitrary multivalued relations are
      not ordinary coverings.
    ],
    source: [Path-lifting theorem and covering monodromy.],
  ),
  entry(
    id: "H.0226",
    kind: "Definition",
    grade: "definition",
    title: [Homology, cohomology, and Euler characteristic],
    depends: ("H.0122", "H.0203"),
    statement: [
      A chain complex has $partial^2=0$ and
      $
        H_k(C)=ker partial_k / "im" partial_(k+1).
      $
      Dual cochains give $H^k(C;R)$. For a finite free chain complex,
      $
        chi(C)=sum_k(-1)^k "rank" C_k
        =sum_k(-1)^k "rank" H_k(C).
      $
    ],
    transformations: [
      Boundaries cancel while non-boundary cycles remain as homology classes;
      cohomology supplies compatible receivers of cycles.
    ],
    boundary: [
      The projective Swing and Euler characteristic are distinct invariants.
      Homologous chains need not be the same path, embedding, or lineage.
    ],
    source: [Standard homological algebra and Euler--Poincaré identity.],
  ),
  entry(
    id: "H.0227",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Relative homology and exact sequence of a pair],
    depends: ("H.0014", "H.0124", "H.0226"),
    statement: [
      For $A subset.eq X$,
      $
        C_*(X,A)=C_*(X)/C_*(A)
      $
      and there is a natural long exact sequence
      $
        dots.c arrow.r H_k(A) arrow.r H_k(X) arrow.r H_k(X,A)
        arrow^(partial) H_(k-1)(A) arrow.r dots.c.
      $
    ],
    transformations: [
      The pair separates an internally admitted body, its exposed subregion,
      and the relative class that remains.
    ],
    boundary: [
      Exactness records algebraic incidence; it supplies no physical flux or
      metric by itself.
    ],
    source: [Long exact sequence of a topological pair.],
  ),
  entry(
    id: "H.0240",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Measure, integral, and limit exchange],
    depends: ("H.0019", "H.0220"),
    statement: [
      A measure is countably additive on a sigma-algebra. Lebesgue integration
      extends nonnegative simple-function integration. Monotone convergence and
      dominated convergence give exact hypotheses under which a pointwise limit
      may pass through the integral.
    ],
    transformations: [
      Integration is a receiver aggregating occurrences while retaining the
      declared measure. Limit exchange is a theorem, not a symbolic move.
    ],
    boundary: [
      Without monotonicity, domination, uniform integrability, or another
      exchange theorem, the limit and integral need not commute.
    ],
    source: [Lebesgue integration; monotone and dominated convergence theorems.],
  ),
  entry(
    id: "H.0241",
    kind: "Definition",
    grade: "definition",
    title: [Normed, Banach, Hilbert, and Lp spaces],
    depends: ("H.0223", "H.0240"),
    statement: [
      A Banach space is a complete normed vector space. A Hilbert space is
      complete under a norm induced by an inner product. For $1<=p<infinity$,
      $L^p$ identifies functions equal almost everywhere under
      $
        norm(f)_p=(integral abs(f)^p)^(1/p).
      $
    ],
    transformations: [
      Choosing norm, weak, pointwise, or measure topology selects a different
      exact convergence receiver.
    ],
    boundary: [
      Almost-everywhere quotienting is exact for measure receivers but erases
      pointwise distinctions on null sets.
    ],
    source: [Standard functional analysis and measure theory.],
  ),
  entry(
    id: "H.0242",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Riesz representation in Hilbert space],
    depends: ("H.0241",),
    statement: [
      Every continuous linear functional $ell$ on a Hilbert space $H$ has a
      unique $y in H$ with
      $
        ell(x)=chevron.l x,y chevron.r,
        quad
        norm(ell)=norm(y).
      $
    ],
    transformations: [
      A continuous scalar receiver is represented by an internal carrier
      relative to the Hilbert metric.
    ],
    boundary: [
      This representation is Hilbert-specific; arbitrary Banach duals need not
      be represented by members of the original space.
    ],
    source: [Riesz representation theorem for Hilbert spaces.],
  ),
  entry(
    id: "H.0243",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Self-adjoint spectral theorem and positivity],
    depends: ("H.0242",),
    statement: [
      A bounded self-adjoint operator $A$ has a unique projection-valued measure
      $E$ such that
      $
        A=integral_(sigma(A)) lambda dif E(lambda).
      $
      Moreover $A>=0$ exactly when $sigma(A) subset.eq [0,infinity)$, exactly
      when $chevron.l A x,x chevron.r>=0$ for every $x$.
    ],
    transformations: [
      Spectrum and quadratic response are exact receiver faces of one
      self-adjoint operator.
    ],
    boundary: [
      Spectrum alone does not reconstruct a general nonnormal operator.
      Unbounded operators require explicit dense domains.
    ],
    source: [Spectral theorem for bounded self-adjoint operators.],
  ),
  entry(
    id: "H.0244",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Positive kernel and reproducing-kernel space],
    depends: ("H.0126", "H.0242"),
    statement: [
      A Hermitian kernel $K:X times X arrow.r CC$ is positive definite when
      $
        sum_(i,j) overline(c_i)c_j K(x_i,x_j)>=0
      $
      for every finite population. It determines a unique reproducing-kernel
      Hilbert space up to canonical isometry.
    ],
    transformations: [
      Pair relations become a Gram geometry in which evaluation is represented
      internally.
    ],
    boundary: [
      Sampled positivity or finitely many matrix orders does not establish the
      all-populations condition.
    ],
    source: [Moore--Aronszajn theorem.],
  ),
  entry(
    id: "H.0245",
    kind: "Definition",
    grade: "definition",
    title: [Distributions and weak derivatives],
    depends: ("H.0240",),
    statement: [
      A distribution is a continuous linear functional on a test-function
      space. Its derivative is defined by
      $
        chevron.l partial_i T,phi chevron.r
        =-chevron.l T,partial_i phi chevron.r.
      $
    ],
    transformations: [
      Differentiation transfers across the pairing, allowing singular or
      nonsmooth currents to retain exact differential incidence.
    ],
    boundary: [
      A distribution need not be a pointwise function or a positive measure.
    ],
    source: [Schwartz distribution theory.],
  ),
  entry(
    id: "H.0246",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Fourier--Plancherel and convolution transport],
    depends: ("H.0143", "H.0207", "H.0241"),
    statement: [
      With a fixed normalization, the Fourier transform extends uniquely to a
      unitary map on $L^2(RR^n)$:
      $
        norm(hat(f))_2=norm(f)_2.
      $
      If $f,g in L^1(RR^n)$,
      $hat(f star g)=hat(f)hat(g)$.
    ],
    transformations: [
      Spatial occurrence and frequency occurrence are exact dual receiver
      faces; convolution becomes pointwise composition.
    ],
    boundary: [
      A sampled discrete transform or floating array is not the complete
      transform of the source function.
    ],
    source: [Plancherel theorem and Fourier convolution theorem.],
  ),
  entry(
    id: "H.0247",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Poisson summation],
    depends: ("H.0246",),
    statement: [
      For a Schwartz function $f$ on $RR$ and the compatible Fourier
      normalization,
      $
        sum_(n in ZZ) f(n)
        =
        sum_(k in ZZ) hat(f)(k).
      $
    ],
    transformations: [
      A lattice population and its reciprocal-lattice spectrum are exact dual
      sums. Scaling the lattice transports the dual scale reciprocally.
    ],
    boundary: [
      Weaker functions require explicit summability or distributional
      hypotheses.
    ],
    source: [Poisson summation formula.],
  ),
  entry(
    id: "H.0248",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Bochner spectral representation],
    depends: ("H.0244", "H.0246"),
    statement: [
      A continuous positive-definite function
      $phi:RR^n arrow.r CC$ is exactly the Fourier--Stieltjes transform of a
      finite positive Borel measure:
      $
        phi(x)=integral exp(i x dot xi) dif mu(xi).
      $
    ],
    transformations: [
      A translation-covariant recurrence field has a positive spectral
      population precisely when its complete kernel is positive definite.
    ],
    boundary: [
      Positivity on selected displacements or finite samples does not establish
      global positive definiteness.
    ],
    source: [Bochner's theorem.],
  ),
  entry(
    id: "H.0249",
    kind: "Definition",
    grade: "definition",
    title: [Laplace and Mellin receivers],
    depends: ("H.0207", "H.0240"),
    statement: [
      Where the integrals converge,
      $
        cal(L)f(s)=integral_0^infinity exp(-s t)f(t)dif t,
        quad
        cal(M)f(s)=integral_0^infinity f(x)x^(s-1)dif x.
      $
      In particular,
      $
        Gamma(s)=cal(M)(exp(-x))(s)
        quad (op("Re")s>0).
      $
      The logarithmic substitution $x=exp(u)$ turns Mellin transport into a
      two-sided Laplace/Fourier-type transport with its Jacobian.
    ],
    transformations: [
      Laplace receives additive time; Mellin receives multiplicative scale.
      Their domains of convergence are part of the face.
    ],
    boundary: [
      Formal symbolic transforms do not establish convergence, inversion, or
      analytic continuation.
    ],
    source: [Classical Laplace and Mellin transform theory.],
  ),
  entry(
    id: "H.0250",
    kind: "Boundary",
    grade: "proved-derived",
    title: [Exact convergence and closure taxonomy],
    depends: ("H.0005", "H.0109", "H.0220", "H.0241"),
    statement: [
      Keep distinct coefficientwise equality of formal series; pointwise,
      uniform, metric, norm, weak, measure, and operator convergence; topological
      closure; asymptotic expansion; and certified enclosure. Each is an exact
      relation with its own quantifiers.
    ],
    transformations: [
      A theorem may transport one convergence species to another only under
      stated hypotheses, such as domination, compactness, boundedness, or
      uniformity.
    ],
    boundary: [
      Matching digits, sampled agreement, and visual stability imply none of
      these relations without a sound certificate.
    ],
    source: [Standard analysis taxonomy under the laboratory exactness boundary.],
  ),
  entry(
    id: "H.0251",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Nested exact enclosures],
    depends: ("H.0222", "H.0223", "H.0250"),
    statement: [
      If rational closed intervals $I_n=[a_n,b_n]$ satisfy
      $I_(n+1) subset.eq I_n$, every $I_n$ contains $x$, and
      $b_n-a_n arrow.r 0$, then
      $
        {y:forall n, y in I_n}={x}.
      $
    ],
    transformations: [
      Each finite enclosure is a certified face; nestedness and vanishing width
      retain the exact law connecting those faces to one real value.
    ],
    boundary: [
      Printing a floating midpoint without the interval and proof discards the
      certificate.
    ],
    source: [Nested-interval theorem.],
  ),
  entry(
    id: "H.0252",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Picard--Lindelöf and local flow],
    depends: ("H.0206", "H.0223",),
    statement: [
      If $f(t,x)$ is continuous in $t$ and locally Lipschitz in $x$, then
      $
        dot(x)=f(t,x),
        quad
        x(t_0)=x_0
      $
      has a unique local solution with continuous dependence on initial data.
      An autonomous law gives $phi_(t+s)=phi_t compose phi_s$ where defined.
    ],
    transformations: [
      Law, initial occurrence, and elapsed parameter jointly determine the
      local lineage.
    ],
    boundary: [
      Non-Lipschitz seams may branch; local existence does not imply global
      completeness.
    ],
    source: [Picard--Lindelöf theorem.],
  ),
  entry(
    id: "H.0253",
    kind: "Definition",
    grade: "definition",
    title: [Dynamical system, orbit, conjugacy, and factor],
    depends: ("H.0106", "H.0220"),
    statement: [
      A discrete dynamical system is $(X,T)$ with iterates $T^n$. A conjugacy
      $h$ is a homeomorphism satisfying $h T=S h$. A factor map is a continuous
      surjection $q$ with $q T=S q$.
    ],
    transformations: [
      Conjugacy is invertible rebase of complete orbit structure; a factor is a
      quotient receiver and may discard distinctions.
    ],
    boundary: [
      Matching some orbit statistics does not prove conjugacy or factorhood.
    ],
    source: [Standard topological dynamics.],
  ),
  entry(
    id: "H.0254",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Poincaré recurrence],
    depends: ("H.0019", "H.0240", "H.0253"),
    statement: [
      If $T$ preserves a finite measure $mu$, then for every measurable
      $A$, almost every $x in A$ returns to $A$ infinitely often.
    ],
    transformations: [
      Recurrence is conditioned by a finite invariant measure; it is not
      ontological chance.
    ],
    boundary: [
      The theorem supplies no return-time bound, convergence, periodicity, or
      mixing.
    ],
    source: [Poincaré recurrence theorem.],
  ),
  entry(
    id: "H.0255",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Birkhoff ergodic theorem],
    depends: ("H.0109", "H.0254"),
    statement: [
      For a measure-preserving $T$ on a probability space and $f in L^1$,
      $
        frac(1,N)sum_(k=0)^(N-1)f compose T^k
        arrow.r
        EE[f " | " cal(I)]
      $
      almost everywhere, where $cal(I)$ is the invariant sigma-algebra. Under
      ergodicity the limit is $integral f dif mu$.
    ],
    transformations: [
      A long recurrence lineage may have an exact conditional-invariant
      aggregate face.
    ],
    boundary: [
      The aggregate erases order and implies neither mixing nor finite-time
      predictability.
    ],
    source: [Birkhoff pointwise ergodic theorem.],
  ),
  entry(
    id: "H.0256",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Contraction fixed point and self-similar attractor],
    depends: ("H.0108", "H.0223"),
    statement: [
      A contraction on a complete metric space has a unique fixed point and all
      iterates converge to it. For finitely many contractions $f_i$, the
      Hutchinson map
      $
        cal(F)(K)=union_i f_i(K)
      $
      is a contraction on nonempty compact sets in Hausdorff distance and has a
      unique fixed compact set.
    ],
    transformations: [
      Exact self-similarity consists of named rebase maps, a return law, and
      convergence in a declared hyperspace metric.
    ],
    boundary: [
      Visual recurrence does not establish a contraction system. Dimension
      formulas require separation hypotheses.
    ],
    source: [Banach fixed-point theorem; Hutchinson self-similarity theorem.],
  ),
  entry(
    id: "H.0257",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Fatou--Julia partition and critical orbit],
    depends: ("H.0220", "H.0253"),
    statement: [
      For a rational map $R$ of degree at least $2$, the Fatou set is the
      maximal normality region and the Julia set its completely invariant
      perfect complement; repelling periodic points are dense in the Julia
      set. For $z^2+c$, the Julia set is connected exactly when the critical
      orbit of $0$ is bounded.
    ],
    transformations: [
      Orbit, stability region, critical seam, and parameter world are distinct
      linked receivers.
    ],
    boundary: [
      A fractal rendering supplies no arithmetic theorem without a proved
      conjugacy or invariant map.
    ],
    source: [Classical Fatou--Julia theory.],
  ),
  entry(
    id: "H.0258",
    kind: "Definition",
    grade: "definition",
    title: [Partial differential operator and weak solution],
    depends: ("H.0245",),
    statement: [
      A linear second-order scalar PDE has principal symbol determined by its
      highest derivatives; its elliptic, hyperbolic, or parabolic type is
      classified from that symbol under the corresponding nondegeneracy
      hypotheses. A weak solution satisfies the equation after transport of
      derivatives onto test functions.
    ],
    transformations: [
      The principal symbol determines local characteristic geometry; the weak
      receiver retains boundary and incidence without requiring pointwise
      differentiability.
    ],
    boundary: [
      Classification does not itself supply existence, uniqueness, regularity,
      or boundary conditions.
    ],
    source: [Standard PDE and distribution theory.],
  ),
  entry(
    id: "H.0259",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Heat semigroup and exact dissipation],
    depends: ("H.0243", "H.0258"),
    statement: [
      For a sufficiently regular square-integrable field on Euclidean
      $RR^n$ with decay sufficient for integration by parts,
      $
        partial_t u=Delta u,
        quad
        u(t)=exp(t Delta)u_0,
      $
      and
      $
        frac(d,dif t)norm(u(t))_2^2=-2 norm(nabla u(t))_2^2.
      $
    ],
    transformations: [
      Diffusion is geometry-conditioned transport with one exact monotone
      energy receiver.
    ],
    boundary: [
      A manifold version additionally depends on its metric and boundary
      conditions. The semigroup generally does not preserve reconstructible
      high-frequency detail backward in time.
    ],
    source: [Spectral heat-semigroup theory and integration by parts.],
  ),
  entry(
    id: "H.0260",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Wave energy and finite propagation],
    depends: ("H.0246", "H.0258"),
    statement: [
      For sufficiently regular compactly supported solutions of
      $
        u_(t t)-c^2 Delta u=0,
      $
      the energy
      $
        E(t)=frac(1,2)integral (abs(u_t)^2+c^2 abs(nabla u)^2)dif x
      $
      is constant, and the value at $(t,x)$ depends only on initial data within
      $abs(y-x)<=c abs(t)$.
    ],
    transformations: [
      The light cone is the exact domain of dependence of this hyperbolic law;
      conservation belongs to the complete evolving solution.
    ],
    boundary: [
      Finite propagation is not universal: heat transport has a different
      support law, and changing the operator changes the cone.
    ],
    source: [Classical wave-equation energy identity and domain of dependence.],
  ),
  entry(
    id: "H.0261",
    kind: "Definition",
    grade: "definition",
    title: [Exact asymptotic relation],
    depends: ("H.0005", "H.0250"),
    statement: [
      $f(x)=O(g(x))$ as $x arrow.r a$ means that there exist exact constants
      $C>0$ and a neighborhood on which $abs(f(x))<=C abs(g(x))$.
      $f=o(g)$ means
      $
        forall epsilon>0 exists U forall x in U:
        abs(f(x))<=epsilon abs(g(x)).
      $
    ],
    transformations: [
      Asymptotic notation is a quantified bound receiver, not a floating fit.
    ],
    boundary: [
      It does not identify leading coefficients or preserve signs unless those
      properties are separately proved.
    ],
    source: [Standard asymptotic notation.],
  ),
  entry(
    id: "H.0262",
    kind: "Definition",
    grade: "definition",
    title: [Receiver-indexed convergence],
    depends: ("H.0003", "H.0012", "H.0220", "H.0250"),
    statement: [
      Let $q_rho:X arrow.r Y_rho$ be a receiver which additionally declares a
      separating family $cal(D)_rho$ of tests $d$ with $d(y,y)=0$, valued in
      ordered objects with declared grains. A net $(x_i)$ in $X$ *converges at
      $rho$* to $x$, written $x_i arrow.r_rho x$, when
      $
        forall d in cal(D)_rho forall g succ 0 exists i_0 forall i succ.eq i_0:
        d(q_rho (x_i),q_rho (x)) prec g.
      $
      Equivalently, continued transport no longer contributes a difference this
      receiver can experience.
    ],
    transformations: [
      This is ordinary convergence in $Y_rho$ pulled back along $q_rho$; the
      content is the index. It supplies the convergence receiver H.0208 names as
      the admission condition for calling a limit holonic, and it makes the
      species enumerated in H.0250 the *values* of an index rather than a list.
    ],
    boundary: [
      No new limit operation is defined and no classical theorem is displaced.
      A separating family is supplied by the receiver, not derived from $X$; two
      receivers sharing a map but not a test family are different receivers.
      Transport between indices is not licensed here.
    ],
    source: [Laboratory definition over standard convergence; see H.0208, H.0250.],
  ),
  entry(
    id: "H.0263",
    kind: "Definition",
    grade: "definition",
    title: [Modulus of transport, and the two grains of an epsilon--delta statement],
    depends: ("H.0003", "H.0262"),
    statement: [
      For $f:X arrow.r Z$ between a source receiver $q_rho$ with grains $G_rho$
      and an observing receiver $q_sigma$ with grains $G_sigma$, continuity at
      $a$ relative to $(rho,sigma)$ is the existence of
      $
        omega_a:G_sigma arrow.r G_rho
      $
      with
      $
        d_rho (q_rho (x),q_rho (a)) prec omega_a (epsilon)
        arrow.r.double
        d_sigma (q_sigma (f x),q_sigma (f a)) prec epsilon
      $
      for every $epsilon in G_sigma$.
    ],
    transformations: [
      The alternation $forall epsilon exists delta$ *is* the assertion that
      $omega_a$ exists, and $omega_a$ runs contravariantly: it carries the
      observing grain back to the source grain, opposite to $f$. Uniform
      continuity is $omega_a$ independent of $a$; Lipschitz is $omega_a$ linear.
      The classical statement is this one with $rho=sigma$ and the two grain
      families silently identified.
    ],
    boundary: [
      Existence of $omega_a$ is a hypothesis about the receiver pair, not a
      property of $f$ alone. A construction that cannot exhibit $omega_a$ returns
      OPEN and has not established discontinuity.
    ],
    source: [Standard modulus of continuity, re-indexed by its two receivers.],
  ),
  entry(
    id: "H.0264",
    kind: "Theorem",
    grade: "proved-derived",
    title: [A limit transports between receivers only through a continuous factorization],
    depends: ("H.0012", "H.0262"),
    statement: [
      If $q_sigma=h compose q_rho$ with $h$ continuous, then
      $x_i arrow.r_rho x$ implies $x_i arrow.r_sigma x$. Consequently, a net
      converging at $rho$ and not at $sigma$ *witnesses* that no such $h$ exists.
    ],
    derivation: [
      Continuity of $h$ carries a convergent net to a convergent net; the second
      claim is the contrapositive.
    ],
    transformations: [
      Disagreement between two receivers about a limit is an obstruction to
      factorization with an exhibited witness, not an inconsistency. This is
      H.0012's non-reconstruction at the level of limits: agreement of one face
      does not transport to another face it does not determine.
    ],
    boundary: [
      The theorem supplies a criterion, not a construction. Exhibiting $h$ when
      it exists, and exhibiting a separating net when it does not, remain work
      for the particular pair.
    ],
    source: [Laboratory derivation; witness at C.0009.],
  ),
  entry(
    id: "H.0265",
    kind: "Theorem",
    grade: "proved-derived",
    title: [An undefined two-sided limit is an empty equalizer under a declared target],
    depends: ("H.0262", "H.0264"),
    statement: [
      For $f(x)=1\/x$ at $0$, the approach side belongs to the receiver. With
      the two-sided receiver defined as the equalizer of the one-sided receivers,
      the target decides the return: on $RR$ all three return OPEN; on
      $RR union {plus.minus infinity}$ the one-sided returns are
      $minus infinity$ and $plus infinity$ and the equalizer is empty; on the
      one-point $RR union {infinity}$ both one-sided returns are $infinity$ and
      the equalizer returns $infinity$.
    ],
    derivation: [
      Each row is the ordinary limit in the named target. The quotient
      identifying $plus.minus infinity$ is the map under which the two
      disagreeing returns become one.
    ],
    transformations: [
      "Undefined" is a receiver return that must name its target before it can be
      read as a fact about the expression. On the Riemann sphere the expression
      has no sides at $infinity$ and no discrepancy arises.
    ],
    boundary: [
      This does not make every undefined limit definable, and OPEN is not a
      licence to choose a side. Adopting $RR union {infinity}$ closes this
      equalizer and destroys the order; a construction needing
      $minus infinity < plus infinity$ may not adopt it.
    ],
    source: [Standard compactifications; laboratory receiver reading.],
  ),
  entry(
    id: "H.0266",
    kind: "Definition",
    grade: "definition",
    title: [Dirac notation: the ket is the construction, the bra is the receiver],
    depends: ("H.0003", "H.0012", "H.0241"),
    statement: [
      In a complex Hilbert space $cal(H)$ with dual $cal(H)^*$,
      $
        ket(psi) in cal(H) " the construction",
        quad
        bra(a) in cal(H)^* " the receiver",
        quad
        braket(a, psi) " the face",
      $
      with $q_(bra(a))=braket(a, dot)$ a receiver in the sense of H.0003. The
      outer product $ketbra(phi, a)$ is transport: it receives with $bra(a)$ and
      emits with $ket(phi)$, in that order.
    ],
    transformations: [
      A declared receiver family is complete exactly when it resolves the
      identity, $sum_i ketbra(a_i, a_i)=I$; when the sum is a proper projection
      $P$, the defect $I-P$ is what the family cannot see, so H.0012's
      non-reconstruction is the statement $sum_i ketbra(a_i, a_i) != I$ written in
      this notation. A POVM is a complete family whose faces are quotients
      $p(i)=braket(psi, E_i, psi)$.
    ],
    boundary: [
      The symmetric form $chevron.l psi,phi chevron.r$ computes the same number
      and makes the two arguments look like one species. Riesz gives
      $cal(H) tilde.eq cal(H)^*$, so the conflation is harmless for the value and
      lossy for the reading -- the isomorphism is antilinear and depends on the
      inner product. This is notation: it asserts no Born rule, no measurement
      postulate, and no claim that any ecology's constructions are Hilbert
      vectors.
    ],
    source: [Standard Dirac notation, adopted for the role typing it makes visible.],
  ),
)
