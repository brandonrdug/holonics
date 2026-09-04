#import "schema.typ": entry

#let transcendence-special-functions = (
  entry(
    id: "H.0350",
    kind: "Definition",
    grade: "definition",
    title: [Algebraic and transcendental elements],
    depends: ("H.0130",),
    statement: [
      An element $alpha$ of an extension of $F$ is algebraic over $F$ when some
      nonzero polynomial in $F[x]$ vanishes at $alpha$. Otherwise it is
      transcendental. Algebraicity is therefore relative to the base field.
    ],
    transformations: [
      An algebraic element enters through a finite quotient by its minimal
      polynomial; a transcendental element admits no such finite algebraic
      relation over the chosen base.
    ],
    boundary: [
      Transcendental does not mean unconstructible, noncomputable, random, or
      inaccessible to exact series and integral receivers.
    ],
    source: [Standard field theory.],
  ),
  entry(
    id: "H.0351",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Exact exponential and e presentations],
    depends: ("H.0109", "H.0208", "H.0212", "H.0250"),
    statement: [
      The entire function
      $
        exp(z)=sum_(n=0)^infinity frac(z^n,n!)
      $
      is the unique solution of $y'=y$, $y(0)=1$, and obeys
      $exp(z+w)=exp(z)exp(w)$. Its value
      $
        e=exp(1)=sum_(n=0)^infinity frac(1,n!)
        =lim_(n arrow.r infinity)(1+1/n)^n.
      $
    ],
    transformations: [
      Differential equation, power series, additive-to-multiplicative
      homomorphism, and binomial-limit lineage are exact nonidentical
      presentations of one value.
    ],
    boundary: [
      A finite decimal or truncated sum is a receiver face, not $e$. Each
      equality above owes its convergence theorem.
    ],
    source: [Classical real and complex analysis of the exponential.],
  ),
  entry(
    id: "H.0352",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Exact pi presentations],
    depends: ("H.0109", "H.0208", "H.0240", "H.0250"),
    statement: [
      Euclidean $pi$ has exact connected presentations including
      $
        pi
        =4 integral_0^1 frac(1,1+x^2)dif x
        =4 sum_(n=0)^infinity frac((-1)^n,2n+1),
      $
      and
      $
        frac(pi,2)
        =
        product_(n=1)^infinity
        frac((2n)^2,(2n-1)(2n+1)).
      $
      The integral, conditionally convergent series, and Wallis product each
      carry their own exact hypotheses and proof.
    ],
    transformations: [
      Arc, integral, series, and product are receiver faces related by
      substitution, termwise integration on admitted regions, and product
      convergence.
    ],
    boundary: [
      No one formula is the identity of $pi$. The occurrence of a prime or
      semiprime in one coefficient pattern is presentation-relative until an
      invariant transport theorem connects it to other presentations.
    ],
    source: [Arctangent integral and series; Wallis product.],
  ),
  entry(
    id: "H.0353",
    kind: "Identity",
    grade: "proved-standard",
    title: [Euler transport between exponential and circular faces],
    depends: ("H.0212", "H.0351", "H.0352"),
    statement: [
      Absolute convergence of the exponential series permits separation into
      even and odd terms:
      $
        exp(i theta)=cos theta+i sin theta.
      $
      Hence
      $
        exp(i pi)+1=0.
      $
    ],
    transformations: [
      The imaginary-axis exponential trajectory re-presents additive angle as
      multiplicative unit-circle phase.
    ],
    boundary: [
      The identity relates declared complex-analytic presentations; it does not
      make $e$, $pi$, $i$, $1$, and $0$ the same occurrence.
    ],
    source: [Euler formula derived from the convergent power series.],
  ),
  entry(
    id: "H.0354",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Lindemann--Weierstrass transcendence],
    depends: ("H.0350", "H.0353"),
    statement: [
      If $alpha_1,dots.c,alpha_n$ are distinct algebraic numbers, then
      $exp(alpha_1),dots.c,exp(alpha_n)$ are linearly independent over the
      algebraic numbers. In particular $exp(alpha)$ is transcendental for
      nonzero algebraic $alpha$; therefore $e$ and $pi$ are transcendental.
    ],
    derivation: [
      $e=exp(1)$ gives the first consequence. If $pi$ were algebraic, then
      $i pi$ would be nonzero algebraic while
      $exp(i pi)=-1$ is algebraic, contradicting the theorem.
    ],
    boundary: [
      The theorem does not classify all algebraic relations among values of
      exponential and logarithmic functions.
    ],
    source: [Lindemann--Weierstrass theorem.],
  ),
  entry(
    id: "H.0355",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Gamma and beta continuation],
    depends: ("H.0249", "H.0283", "H.0352"),
    statement: [
      For $op("Re")(s)>0$,
      $
        Gamma(s)=integral_0^infinity t^(s-1)exp(-t)dif t,
        quad
        Gamma(s+1)=s Gamma(s),
        quad
        Gamma(1/2)=sqrt(pi).
      $
      The beta integral obeys
      $
        B(x,y)=frac(Gamma(x)Gamma(y),Gamma(x+y)).
      $
    ],
    transformations: [
      Mellin transport, recursion, Gaussian geometry, and simplex integration
      connect these exact faces.
    ],
    boundary: [
      Meromorphic continuation crosses poles and requires the continued
      function, not the original integral outside its domain.
    ],
    source: [Euler gamma and beta identities.],
  ),
  entry(
    id: "H.0356",
    kind: "Definition",
    grade: "definition",
    title: [Hypergeometric equation and transformation atlas],
    depends: ("H.0109", "H.0252", "H.0283"),
    statement: [
      For $abs(z)<1$ and $c$ not a nonpositive integer,
      $
        op("₂F₁")(a,b;c;z)
        =
        sum_(n=0)^infinity
        frac((a)_n(b)_n,(c)_n n!)z^n
      $
      and it solves
      $
        z(1-z)y''+[c-(a+b+1)z]y'-a b y=0.
      $
      Analytic continuation and parameter transformations relate local solution
      bases around its singular points $0,1,infinity$.
    ],
    transformations: [
      Coefficient recurrence, differential equation, singularity monodromy, and
      transformed series are exact faces of one local system.
    ],
    boundary: [
      A formal parameter substitution is not an identity unless its domain,
      branch, and continuation path are specified.
    ],
    source: [Gauss hypergeometric function theory.],
  ),
  entry(
    id: "H.0357",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Elliptic integral and arithmetic--geometric mean],
    depends: ("H.0250", "H.0356"),
    statement: [
      The complete elliptic integral
      $
        K(k)=integral_0^(pi/2)
        frac(dif theta,sqrt(1-k^2 sin^2 theta))
        =frac(pi,2) op("₂F₁")(1/2,1/2;1;k^2)
      $
      satisfies Gauss's exact identity
      $
        K(k)=frac(pi,2 "AGM"(1,sqrt(1-k^2))).
      $
    ],
    transformations: [
      A period integral, hypergeometric series, and quadratically convergent
      mean iteration are exact connected presentations.
    ],
    boundary: [
      Branches and parameter domain are part of the identity. Fast convergence
      does not erase the iteration lineage.
    ],
    source: [Gauss hypergeometric and AGM theorem for elliptic integrals.],
  ),
  entry(
    id: "H.0358",
    kind: "Definition",
    grade: "definition",
    title: [Modular forms and q-expansion],
    depends: ("H.0132", "H.0284",),
    statement: [
      A modular form of weight $k$ for a declared subgroup $Gamma$ obeys
      $
        f(frac(a z+b,c z+d))=(c z+d)^k f(z)
      $
      and the required holomorphy at cusps. If the width of the cusp
      $infinity$ is $h$, its exact local coordinate is
      $q=exp(2 pi i z/h)$ and
      $f(z)=sum_(n>=0)a_n q^n$.
    ],
    transformations: [
      Upper-half-plane geometry, group action, and coefficient lineage are
      connected through the cusp receiver.
    ],
    boundary: [
      Weight, level, multiplier, cusp conditions, and coefficient field must be
      declared; not every $q$-series is modular.
    ],
    source: [Standard modular-form definition and q-expansion principle.],
  ),
  entry(
    id: "H.0359",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Hecke eigenform Euler product],
    depends: ("H.0305", "H.0306", "H.0358"),
    statement: [
      A normalized cuspidal simultaneous Hecke eigenform of integral weight
      $k$, level $N$, and declared character has multiplicative Fourier
      coefficients and an $L$-series
      $
        L(f,s)=sum_(n>=1)frac(a_n,n^s)
      $
      with local Euler factors determined by its Hecke eigenvalues. Its
      completed $L$-function, with Gamma, conductor, and character factors
      fixed by $(k,N)$ and the chosen normalization, extends holomorphically and
      obeys the corresponding $s mapsto k-s$ functional equation.
    ],
    transformations: [
      Symmetry eigenchannels, coefficient recurrence, prime-local factors, and
      global analytic completion are exact related receivers.
    ],
    boundary: [
      Euler product and functional equation are not automatic for an arbitrary
      Dirichlet series.
    ],
    source: [Hecke theory of modular eigenforms.],
  ),
  entry(
    id: "H.0360",
    kind: "Theorem",
    grade: "proved-standard",
    title: [Continued-fraction path and determinant],
    depends: ("H.0148", "H.0223"),
    statement: [
      For a simple continued fraction with convergents $p_n/q_n$,
      $
        p_n q_(n-1)-p_(n-1)q_n=(-1)^(n-1).
      $
      Infinite simple continued fractions converge, and irrational real numbers
      have unique infinite expansions under the conventional terminal rule.
    ],
    transformations: [
      Each partial quotient selects a left or right fractional-linear step; the
      determinant retains neighboring orientation exactly.
    ],
    boundary: [
      A convergent is a rational presentation with an exact remainder relation,
      not the irrational value itself.
    ],
    source: [Classical continued-fraction theory.],
  ),
  entry(
    id: "H.0361",
    kind: "Definition",
    grade: "definition",
    title: [Period number],
    depends: ("H.0240", "H.0320", "H.0350"),
    statement: [
      A period is a complex number whose real and imaginary parts are absolutely
      convergent integrals of rational functions with algebraic coefficients
      over semialgebraic domains defined over the algebraic numbers.
    ],
    transformations: [
      Algebraic data, domain incidence, and exact integration form a finite
      presentation class containing algebraic numbers and $pi$.
    ],
    boundary: [
      It is open whether familiar constants such as $e$ belong to this class.
      “Transcendental” and “period” are nonidentical classifications.
    ],
    source: [Kontsevich--Zagier definition of periods.],
  ),
  entry(
    id: "H.0362",
    kind: "Definition",
    grade: "definition",
    title: [Transcendental formulation atlas],
    depends: (
      "H.0023",
      "H.0100",
      "H.0351",
      "H.0352",
      "H.0355",
      "H.0356",
      "H.0357",
      "H.0360",
      "H.0361",
    ),
    statement: [
      A formulation node is
      $
        (D,E,cal(H),v,rho),
      $
      where $D$ is the parameter domain, $E$ an exact expression or algorithm,
      $cal(H)$ its hypotheses and branch data, $v$ the denoted invariant, and
      $rho$ the receiver. An atlas edge is a proved transformation carrying one
      node to another while preserving $v$.
    ],
    transformations: [
      Substitution with Jacobian, analytic continuation, functional equation,
      recurrence, hypergeometric transformation, modular action, and exact
      algorithm conjugacy are distinct edge species.
    ],
    boundary: [
      Shared output does not supply an edge. The atlas is not complete merely
      because infinitely many formulas exist.
    ],
    source: [Laboratory pi/e/transcendental synthesis in standard atlas language.],
  ),
  entry(
    id: "H.0363",
    kind: "Definition",
    grade: "proved-derived",
    title: [Prime-valuation receiver of a formulation],
    depends: ("H.0302", "H.0362"),
    statement: [
      For a formulation whose rational coefficients are $a_n/b_n$ in lowest
      terms, choose a finite coefficient-index set $I$ and finite prime set
      $P$. Its prime-valuation face is
      $
        nu_(P,I)(E)
        =
        (v_p(a_n),v_p(b_n))_((p,n) in P times I).
      $
      Transformation edges act on this decorated coefficient lineage according
      to their exact algebraic identities.
    ],
    transformations: [
      This receiver can compare where primes, prime powers, and semiprimes enter
      coefficient numerators, denominators, recurrences, or modular levels.
    ],
    boundary: [
      The face is presentation-relative. No theorem here says that all formulas
      for one transcendental invariant share one prime distribution or that a
      local coefficient pattern determines zeta zeros.
    ],
    source: [Laboratory formulation-atlas receiver; valuation theory standard.],
  ),
  entry(
    id: "H.0364",
    kind: "Theorem",
    grade: "proved-derived",
    title: [Transcendental evaluation fibers carry changing arithmetic currents],
    depends: ("H.0313", "H.0351", "H.0352", "H.0362", "H.0363"),
    statement: [
      For an exact evaluation map
      $
        "ev":cal(F) arrow.r cal(V),
      $
      the fiber $cal(E)_tau="ev"^(-1)(tau)$ contains nonidentical
      formulations returning $tau$. A proved transport $T:F arrow.r G$ has
      arithmetic residual
      $
        op("Res")_T=T_* frak(A)_F-frak(A)_G.
      $
      It vanishes only when that transformation preserves the declared
      decorated accessibility current.

      Valuation specialization obeys
      $
        product_p p^(-s alpha_p)
        =
        exp(-s sum_p alpha_p log p),
      $
      while the factorial lineage of $e$ obeys
      $
        v_p((n+1)!)-v_p(n!)=v_p(n+1).
      $
    ],
    derivation: [
      For a real rational $x=u/v$ in lowest terms with $v != 0$ and
      $abs(u)<=abs(v)$, let
      $
        A(x)=sum_(n>=0)(-1)^n frac(x^(2n+1),2n+1)
      $
      be the exact arctangent series, conditionally at the endpoints. Then
      $
        frac(a_(n+1),a_n)
        =
        -frac(u^2(2n+1),v^2(2n+3)).
      $
      Thus every $p$ dividing $v$ meets the moving odd current on exact sheets
      $2n+1 equiv 0 mod p^k$ or $2n+3 equiv 0 mod p^k$. In the first twelve
      transitions of Machin's
      $pi=16A(1/5)-4A(1/239)$, the first arm crosses two $5$-sheets while the
      second crosses no $239$-sheet. Its Gaussian closures are nevertheless
      $
        1+5^2=2 dot 13,
        quad
        1+239^2=2 dot 13^4.
      $
    ],
    transformations: [
      Parameter axes $5,239$, Gaussian closure axes $2,13$, and the fixed
      Chudnovsky scale axes
      $
        640320=2^6 dot 3 dot 5 dot 23 dot 29
      $
      are related but nonidentical receiver faces of exact $pi$ formulations.
    ],
    boundary: [
      No invariant has one universal coefficient support. The twelve-step
      collision result is bounded but exact. These arithmetic/formulation
      currents supply a direction for completed zeta transport; they do not
      determine the nontrivial zero set.
    ],
    source: [
      Standard exponential, factorial, arctangent, and Gaussian identities;
      exact bounded evidence in
      `src/soma/observations/eros-transcendental-presentation-topology-01/RESULTS.md`.
    ],
  ),
)
