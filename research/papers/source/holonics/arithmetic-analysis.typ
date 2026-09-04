#import "schema.typ": entry

#let arithmetic-analysis = (
  entry(
    id: "H.0300",
    kind: "Definition",
    grade: "definition",
    title: [Divisibility, unit, irreducible, and prime],
    depends: ("H.0001",),
    statement: [
      In an integral domain $R$, $a$ divides $b$ when $b=a c$ for some
      $c in R$. A unit has a multiplicative inverse. A nonzero nonunit $p$ is
      irreducible when $p=a b$ implies that $a$ or $b$ is a unit. It is prime
      when $p$ divides $a b$ implies $p$ divides $a$ or $p$ divides $b$.
    ],
    transformations: [
      In the integers, primes and irreducibles agree. In a general integral
      domain they need not; prime always implies irreducible, while the converse
      requires additional structure such as a unique factorization domain.
    ],
    boundary: [
      Prime is relative to the multiplication and units of the ambient domain.
      A prime integer, prime ideal, prime knot, and primitive closed orbit are
      distinct irreducibility species.
    ],
    source: [Standard commutative algebra.],
  ),
  entry(
    id: "H.0301",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Euclid's lemma],
    depends: ("H.0300",),
    statement: [
      For a prime integer $p$, if $p$ divides $a b$, then $p$ divides $a$ or
      $p$ divides $b$.
    ],
    derivation: [
      If $p$ does not divide $a$, then $gcd(p,a)=1$. Bézout gives
      $u p+v a=1$. Multiplying by $b$ yields
      $
        u b p+v a b=b.
      $
      Both terms on the left are divisible by $p$, so $p$ divides $b$.
    ],
    source: [Classical elementary number theory.],
    boundary: [
      The Bézout step uses the Euclidean/PID structure of the integers.
    ],
  ),
  entry(
    id: "H.0302",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Fundamental theorem of arithmetic],
    depends: ("H.0301",),
    statement: [
      Every integer $n>1$ has a factorization
      $
        n=product_p p^(v_p(n))
      $
      with finite support, unique up to ordering.
    ],
    derivation: [
      Existence follows by strong induction: if $n$ is not prime, write
      $n=a b$ with $1<a,b<n$ and factor both. For uniqueness, if
      $p_1 dots.c p_r=q_1 dots.c q_s$, Euclid's lemma makes $p_1$ divide some
      $q_j$; primality forces equality. Cancel and induct.
    ],
    transformations: [
      The map $n mapsto (v_p(n))_p$ identifies positive rational numbers with
      the direct sum of integer valuation axes:
      $
        v_p(x y)=v_p(x)+v_p(y).
      $
    ],
    boundary: [
      The valuation vector is exact for multiplicative arithmetic. Decimal
      digits and radix endings are receiver charts, not prime ontology.
    ],
    source: [Classical fundamental theorem of arithmetic.],
  ),
  entry(
    id: "H.0303",
    kind: "Definition",
    grade: "definition",
    title: [Arithmetic convolution and Möbius function],
    depends: ("H.0302",),
    statement: [
      For arithmetic functions $f,g$ define Dirichlet convolution
      $
        (f star g)(n)=sum_(d divides n) f(d)g(n/d).
      $
      Its identity is $epsilon(1)=1$, $epsilon(n)=0$ for $n>1$. The Möbius
      function is
      $
        mu(n)=
        cases(
          0 & "if a square prime divides " n,
          (-1)^r & "if " n " is a product of " r " distinct primes".
        )
      $
    ],
    boundary: [
      Arithmetic Möbius inversion, incidence-algebra Möbius inversion, and a
      Möbius fractional-linear transformation are different objects.
    ],
    source: [Standard multiplicative number theory.],
  ),
  entry(
    id: "H.0304",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Möbius inversion],
    depends: ("H.0303",),
    statement: [
      Let $u(n)=1$. Then
      $
        mu star u=epsilon.
      $
      Consequently,
      $
        F(n)=sum_(d divides n) f(d)
        arrow.l.r
        f(n)=sum_(d divides n) mu(d)F(n/d).
      $
    ],
    derivation: [
      By multiplicativity it suffices to evaluate a prime power:
      $
        sum_(d divides p^k) mu(d)=mu(1)+mu(p)=0
      $
      for $k>=1$, while the sum is $1$ at $n=1$. Convolving
      $F=f star u$ with $mu$ gives
      $
        F star mu=f star (u star mu)=f.
      $
    ],
    transformations: [
      This is exact inclusion--exclusion on the divisor poset. It is the
      arithmetic carrier for reversing “all factor ancestors contributed.”
    ],
    source: [Classical Möbius inversion, independently rederived above.],
    boundary: [
      Cancellation in one finite divisor fiber does not imply square-root
      cancellation of the cumulative Mertens function.
    ],
  ),
  entry(
    id: "H.0305",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Dirichlet-series multiplication],
    depends: ("H.0303",),
    statement: [
      Where both series are absolutely convergent,
      $
        (sum_(n>=1) frac(f(n),n^s))
        (sum_(n>=1) frac(g(n),n^s))
        =
        sum_(n>=1) frac((f star g)(n),n^s).
      $
    ],
    derivation: [
      Absolute convergence permits rearrangement:
      $
        sum_(a,b>=1) frac(f(a)g(b),(a b)^s)
        =
        sum_(n>=1) frac(1,n^s)
        sum_(a b=n) f(a)g(b).
      $
      The inner sum is Dirichlet convolution.
    ],
    boundary: [
      Outside absolute convergence, rearrangement and analytic continuation
      require separate theorems.
    ],
    source: [Classical Dirichlet-series product identity.],
  ),
  entry(
    id: "H.0306",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Euler product],
    depends: ("H.0302", "H.0305"),
    statement: [
      For $op("Re")s>1$,
      $
        zeta(s)
        =
        sum_(n>=1) n^(-s)
        =
        product_p (1-p^(-s))^(-1).
      $
    ],
    derivation: [
      Expand each local factor as the convergent geometric series
      $sum_(k>=0)p^(-k s)$. Multiplying a finite prime set gives one term for
      every valuation vector supported on that set. Unique factorization makes
      these terms exactly the integers composed from those primes. Absolute
      convergence lets the finite products exhaust all primes and integers.
    ],
    transformations: [
      The Euler product is the exact junction between integer succession and
      independent prime-valuation axes.
    ],
    boundary: [
      The product does not converge as such throughout the critical strip.
      Analytic continuation is a new receiver, not termwise continuation of
      every local product.
    ],
    source: [
      Euler; see Bombieri's Clay RH account and standard analytic number theory.
    ],
  ),
  entry(
    id: "H.0307",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Prime-power logarithmic current],
    depends: ("H.0306",),
    statement: [
      For $op("Re")s>1$,
      $
        -frac(zeta'(s),zeta(s))
        =
        sum_p sum_(k>=1) frac(log p,p^(k s))
        =
        sum_(n>=1) frac(Lambda(n),n^s),
      $
      where $Lambda(p^k)=log p$ and $Lambda(n)=0$ otherwise.
    ],
    derivation: [
      Take logarithms of the absolutely convergent Euler product:
      $
        log zeta(s)
        =
        sum_p sum_(k>=1) frac(p^(-k s),k).
      $
      Differentiate termwise; the factor $-k log p$ cancels $1/k$.
    ],
    transformations: [
      Primes are primitive multiplicative returns; powers are their repeated
      traversals. The logarithmic derivative weights each repeat by the
      primitive length $log p$.
    ],
    boundary: [
      This identity alone gives no sign or location for analytically continued
      zeros.
    ],
    source: [Classical logarithmic derivative of the Euler product.],
  ),
  entry(
    id: "H.0308",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Theta inversion by Poisson summation],
    depends: ("H.0207", "H.0212", "H.0247"),
    statement: [
      For $t>0$, let
      $
        theta(t)=sum_(n in ZZ) exp(-pi n^2 t).
      $
      Then
      $
        theta(t)=t^(-1/2)theta(1/t).
      $
    ],
    derivation: [
      The Fourier transform of $x mapsto exp(-pi t x^2)$ is
      $xi mapsto t^(-1/2)exp(-pi xi^2/t)$. Poisson summation equates the
      sums of a Schwartz function and its Fourier transform over $ZZ$,
      yielding the identity.
    ],
    transformations: [
      The factor $t^(-1/2)$ is the one-dimensional half-density Jacobian of
      reciprocal scale. It is the analytic source of the centered
      $s mapsto 1-s$ symmetry after Mellin transport.
    ],
    boundary: [
      Poisson summation and the Gaussian Fourier transform are substantial
      imported theorems; this entry gives their exact composition, not a new
      proof of all Fourier analysis.
    ],
    source: [Jacobi theta transformation via Poisson summation.],
  ),
  entry(
    id: "H.0309",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Mellin completion and zeta functional equation],
    depends: ("H.0249", "H.0308"),
    statement: [
      For $op("Re")s>1$,
      $
        pi^(-s/2)Gamma(s/2)zeta(s)
        =
        frac(1,2)
        integral_0^infinity (theta(t)-1)t^(s/2-1) dif t.
      $
      Splitting at $1$ and applying H.0308 continues the completed expression
      meromorphically and yields the entire function
      $
        xi(s)=frac(1,2)s(s-1)pi^(-s/2)Gamma(s/2)zeta(s)
      $
      with
      $
        xi(s)=xi(1-s).
      $
    ],
    derivation: [
      Integrate each Gaussian term using
      $
        integral_0^infinity exp(-pi n^2t)t^(s/2-1) dif t
        =
        (pi n^2)^(-s/2)Gamma(s/2).
      $
      Absolute convergence permits summation. Split the theta integral at
      $1$; in $(0,1)$ substitute $t=1/u$ and use
      $theta(t)=t^(-1/2)theta(1/t)$. The paired integrals are invariant under
      $s mapsto 1-s$; the elementary endpoint terms are cancelled by
      $s(s-1)/2$.
    ],
    transformations: [
      Euler prime factors, the Gamma/archimedean factor, and endpoint factors
      become one completed receiver. The critical seam is the fixed set of the
      involution $s mapsto 1-s$.
    ],
    boundary: [
      The functional equation gives symmetry of zeros about the seam; it does
      not put every zero on the seam.
    ],
    source: [
      Riemann's theta--Mellin continuation; formula normalized as in NIST DLMF
      §25.4.
    ],
  ),
  entry(
    id: "H.0310",
    kind: "Definition",
    grade: "definition",
    title: [Centered completed function and RH],
    depends: ("H.0309",),
    statement: [
      Define
      $
        cal(X)(z)=xi(1/2+z).
      $
      Then $cal(X)$ is even:
      $
        cal(X)(-z)=cal(X)(z).
      $
      The Riemann Hypothesis is the proposition
      $
        forall z in CC:
        cal(X)(z)=0 arrow.r op("Re")z=0.
      $
    ],
    transformations: [
      In the traditional coordinate $s=1/2+z$, this is
      $op("Re")s=1/2$ for every nontrivial zero.
    ],
    boundary: [
      The definition is not a surrogate involving square roots, finite zero
      lists, or a renamed `OPEN` inhabitant.
    ],
    source: [Standard RH statement in centered coordinates.],
  ),
  entry(
    id: "H.0311",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Hadamard zero divisor of the completion],
    depends: ("H.0309", "H.0310"),
    statement: [
      The entire function $xi$ has order one and admits a canonical product
      over its zeros. In a conventional symmetric ordering,
      $
        xi(s)=xi(0) product_rho (1-s/rho),
      $
      with the convergence factor absorbed by pairing/symmetric summation;
      equivalently the genus-one Hadamard product carries explicit exponential
      factors.
    ],
    derivation: [
      Stirling bounds for $Gamma(s/2)$ and polynomial bounds for $zeta$ on
      vertical strips give order one. Hadamard's factorization theorem then
      represents an order-one entire function by its zero divisor and an
      exponential polynomial. The functional symmetry fixes the permitted
      exponential normalization under symmetric grouping.
    ],
    transformations: [
      Logarithmic differentiation turns the zero product into a sum of
      resolvents. This is the common entrance to Li, Pick, Stieltjes, and
      spectral receiver routes.
    ],
    boundary: [
      Grouping and convergence conventions must be explicit. A formal product
      over zeros without Hadamard control is not a proof object.
    ],
    source: [Hadamard factorization applied to Riemann's xi function.],
  ),
  entry(
    id: "H.0312",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Explicit formula as source/zero comparison],
    depends: ("H.0307", "H.0309", "H.0311"),
    statement: [
      For an admissible test function and its Mellin/Fourier transform, contour
      displacement of
      $
        -frac(zeta'(s),zeta(s))
      $
      equates a weighted sum over prime powers with a sum over nontrivial
      zeros, together with the Gamma and endpoint terms of the completion.
    ],
    derivation: [
      Start where H.0307 converges absolutely. Multiply by the transform of
      the test function and integrate on a vertical line. Shift the contour
      through the completed meromorphic function. The residue theorem records
      the pole at $1$, trivial zeros/Gamma poles, and every nontrivial zero.
      Mellin inversion returns the prime-power side.
    ],
    transformations: [
      The formula is one exact comparison cell:
      $
        "prime powers + archimedean terms + endpoints"
        =
        "completed zero divisor".
      $
    ],
    boundary: [
      The exact signs and endpoint conditions depend on the chosen test-space
      convention. The formula alone does not force the zero terms to have one
      sign.
    ],
    source: [
      Riemann--Weil explicit formula; see Bombieri's official Clay problem
      description.
    ],
  ),
  entry(
    id: "H.0313",
    kind: "Definition",
    grade: "definition",
    title: [Graded arithmetic accessibility current],
    depends: ("H.0213", "H.0302"),
    statement: [
      Let $C_e$ be an oriented finite or locally finite chain of arithmetic
      occurrences accessible to receiver incidence $e$, and let
      $nu_e:C_e arrow.r NN^(P_e)$ be its exact valuation address in a declared
      prime aperture. Define
      $
        frak(A)_e(bold(X))
        =
        sum_(alpha in NN^(P_e))
        [C_e|_(nu_e^(-1)(alpha))] bold(X)^alpha.
      $
      The coefficient is a chain or signed occurrence population. The degree
      decomposition by $abs(alpha)_1$ distinguishes primitive axes $X_p$,
      repeated degree-two traversal $X_p^2$, and cross-axis degree-two
      incidence $X_p X_q$.
    ],
    transformations: [
      An augmentation may return an exact count or generating series only
      after the occurrence, orientation, multiplicity, boundary, and valuation
      address have been retained.
    ],
    boundary: [
      This is not a prime probability scalar or universal taxonomy. A growing
      prime aperture carries unresolved support outside its present axes.
    ],
    source: [
      Laboratory chain-valued synthesis of H.0213 and the valuation atlas
      supplied by the fundamental theorem of arithmetic.
    ],
  ),
  entry(
    id: "H.0314",
    kind: "Theorem",
    grade: "proved-derived",
    title: [Prime-cut incidence calculus],
    depends: ("H.0215", "H.0302", "H.0313"),
    statement: [
      In a fixed finite aperture let $K_p$ restrict the current away from
      multiples of a newly admitted prime $p$, and put
      $Delta_p frak(A)=K_p frak(A)-frak(A)$. Then
      $
        Delta_p frak(A)
        =
        -sum_(p divides n) [n] bold(X)^(nu(n)).
      $
      For distinct new axes $p,q$,
      $
        Delta_q Delta_p frak(A)
        =
        Delta_p Delta_q frak(A)
        =
        sum_(p q divides n) [n] bold(X)^(nu(n)).
      $
    ],
    derivation: [
      The first difference is exact chain restriction. Applying the second cut
      restores with positive sign precisely the doubly removed population.
      Divisibility cuts commute, so their curvature commutator is zero while
      their joint Hessian may be nonzero.
    ],
    transformations: [
      The degree-two projection of the mixed difference selects $X_p X_q$.
      Prime squares instead occupy the valuation layer $v_p(n)=2$ and have
      face $X_p^2$; they are not a fictitious second admission of $p$.
    ],
    boundary: [
      Static divisibility cuts commute. Receiver-dependent apertures or
      transported coefficient laws may have nonzero mixed curvature and must
      be compared using H.0215.
    ],
    source: [Unique factorization and finite inclusion--exclusion.],
  ),
  entry(
    id: "H.0315",
    kind: "Theorem",
    grade: "computational-witness",
    title: [Exact wall current of the interval from 113 to 127],
    depends: ("H.0314",),
    statement: [
      Beginning with odd integers in $[113,127]$ and admitting
      $3,5,7,11$ successively gives
      $
        Delta_3 frak(A)=-(X_3^2 X_13+X_3 X_41),
      $
      $
        Delta_5 frak(A)=-(X_5 X_23+X_5^3),
      $
      $
        Delta_7 frak(A)=-X_7 X_17,
        quad
        Delta_11 frak(A)=-X_11^2.
      $
      The endpoint survivors are $113$ and $127$.
    ],
    derivation: [
      The six wall crossings are
      $
        117=3^2 dot 13,
        123=3 dot 41,
        115=5 dot 23,
        125=5^3,
        119=7 dot 17,
        121=11^2.
      $
      Therefore the endpoint gap $14$ is the augmentation of three mixed
      semiprime crossings, one prime-square crossing, and two degree-three
      crossings.
    ],
    transformations: [
      The place sets grow exactly as
      $
        {2},
        {2,3},
        {2,3,5},
        {2,3,5,7},
        {2,3,5,7,11}.
      $
      Each stage is an arithmetic boundary change, not a new absolute number
      line.
    ],
    boundary: [
      This finite witness exposes what the quotient gap forgets. It does not
      predict primes or establish a global distribution law.
    ],
    source: [
      `src/soma/observations/prime-spectral-world-01/RESULTS.md`, re-expressed
      exactly through H.0313--H.0314.
    ],
  ),
)
