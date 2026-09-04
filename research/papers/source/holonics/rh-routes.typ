#import "schema.typ": entry

#let rh-routes = (
  entry(
    id: "RH.0000",
    kind: "Conjecture",
    grade: "conjecture",
    title: [Riemann Hypothesis],
    depends: ("H.0310",),
    statement: [
      $
        forall z in CC:
        cal(X)(z)=0 arrow.r op("Re")z=0,
        quad
        cal(X)(z)=xi(1/2+z).
      $
    ],
    transformations: [
      Every route below must prove both arrows between this proposition and its
      own criterion. The route is complete only when its source-side criterion
      is established without assuming the zero locations.
    ],
    boundary: [
      Unresolved. No laboratory entry in this registry proves RH.
    ],
    source: [
      #link("https://www.claymath.org/wp-content/uploads/2022/05/riemann.pdf")[
        Bombieri, official Clay problem description
      ].
    ],
  ),
  entry(
    id: "RH.0010",
    kind: "Equivalence",
    grade: "proved-standard",
    title: [Centered positive-real and Pick-kernel route],
    depends: ("H.0126", "H.0244", "H.0310", "H.0311", "RH.0000"),
    statement: [
      Put
      $
        F(z)=frac(cal(X)'(z),cal(X)(z)).
      $
      Then RH is equivalent to $F$ being holomorphic with
      $op("Re")F(z)>=0$ on $op("Re")z>0$. It is also equivalent to positive
      semidefiniteness, on that half-plane, of
      $
        K_F(p,q)
        =
        frac(F(p)+overline(F(q)),p+overline(q)).
      $
    ],
    derivation: [
      Under RH, pair the even zero divisor at $plus.minus i gamma$:
      $
        F(z)=sum_(gamma>0) m_gamma frac(2z,z^2+gamma^2).
      $
      For $z=x+i y$, $x>0$,
      $
        op("Re")frac(2z,z^2+gamma^2)
        =
        frac(2x(x^2+y^2+gamma^2),abs(z^2+gamma^2)^2)>0.
      $
      Conversely, holomorphy of $F=cal(X)'/cal(X)$ excludes zeros in the
      right half-plane; evenness excludes zeros in the left half-plane.
      For the kernel statement, apply the Cayley transform
      $S=(F-1)/(F+1)$. The Schur kernel of $S$ is a nonzero congruence of
      $K_F$; diagonal positivity recovers $op("Re")F>=0$.
    ],
    transformations: [
      Holonic face: $F$ is a normal logarithmic response; $K_F$ compares two
      receiver incidences. A proof may enter by constructing a source-native
      passive/Gram realization.
    ],
    boundary: [
      OPEN: derive $op("Re")F>=0$ or a Gram factorization of $K_F$ from the
      theta--Euler--Gamma source without first assuming RH. A finite kernel cut
      or a quotient realization is insufficient.
    ],
    source: [
      Hinkkanen's logarithmic-derivative criterion, indexed by the
      #link("https://www.aimath.org/WWN/rh/articles/html/108a/")[
        American Institute of Mathematics RH equivalent list
      ]; Hadamard product; classical positive-real/Schur kernel theorem.
    ],
  ),
  entry(
    id: "RH.0020",
    kind: "Equivalence",
    grade: "proved-standard",
    title: [Weil explicit-formula positivity],
    depends: ("H.0126", "H.0312", "RH.0000"),
    statement: [
      On Weil's admissible test space, the completed explicit-formula
      quadratic form is nonnegative for every test if and only if RH holds.
      With a Mellin test $g$, the spectral face has the form
      $
        Q(g)
        =
        sum_rho
        hat(g)(rho)
        overline(hat(g)(1-overline(rho))),
      $
      with the precise endpoint constraints and normalization of the chosen
      convention.
    ],
    derivation: [
      Under RH, $1-overline(rho)=rho$, so the spectral sum is a sum of squared
      moduli. Conversely, an off-seam zero and its functional-equation
      companions permit an admissible test concentrated on that finite
      spectral configuration, producing a negative direction. The explicit
      formula transports the same form to prime powers plus archimedean and
      endpoint terms.
    ],
    transformations: [
      This is the most complete established source/zero comparison cell.
      It is one route, not the definition of RH or holonics.
    ],
    boundary: [
      OPEN: prove the sign on the complete admissible test space. Positivity on
      finite support, one test family, one aperture, or an eventual parameter
      regime does not imply the universal form.
    ],
    source: [
      #link("https://www.claymath.org/wp-content/uploads/2022/05/riemann.pdf")[
        Bombieri, Clay RH account, explicit formula and Weil criterion
      ].
    ],
  ),
  entry(
    id: "RH.0030",
    kind: "Equivalence",
    grade: "proved-standard",
    title: [Li--Keiper recurrence coefficients],
    depends: ("H.0311", "H.0212", "RH.0000"),
    statement: [
      Define
      $
        lambda_n
        =
        frac(1,(n-1)!)
        [frac(d^n,d s^n)(s^(n-1)log xi(s))]_(s=1).
      $
      With symmetric zero summation,
      $
        lambda_n
        =
        sum_rho [1-(1-1/rho)^n].
      $
      Then
      $
        "RH" arrow.l.r forall n>=1: lambda_n>=0.
      $
    ],
    derivation: [
      The Möbius rebase $w=1-1/rho$ sends the critical line to the unit circle.
      Under RH, conjugate pairs contribute
      $
        2-2 cos(n theta)>=0.
      $
      Li's converse theorem shows that if every coefficient is nonnegative,
      no transformed zero can lie off the unit circle; an exterior member would
      eventually contribute exponentially growing oscillation.
    ],
    transformations: [
      Each $lambda_n$ is an $n$-fold recurrence receiver of the complete zero
      divisor. This route makes the projective/rebase logic explicit.
    ],
    boundary: [
      OPEN: derive positivity for every order $n$ from the arithmetic source.
      Finite or asymptotic positivity does not close the criterion.
    ],
    source: [
      #link("https://doi.org/10.1006/jnth.1997.2137")[
        X.-J. Li, The Positivity of a Sequence of Numbers and the Riemann Hypothesis
      ].
    ],
  ),
  entry(
    id: "RH.0040",
    kind: "Equivalence",
    grade: "conditional",
    title: [Squared-seam Stieltjes and connected Hankel route],
    depends: ("H.0126", "H.0248", "H.0311", "RH.0010"),
    statement: [
      Since $cal(X)$ is even, define the entire function
      $
        H(w)=frac(cal(X)(sqrt(w)),cal(X)(0)).
      $
      RH is equivalent to all zeros of $H$ lying on the negative real axis.
      The genus-zero logarithmic product of this order-$1/2$ entire function
      gives, under RH,
      $
        frac(H'(w),H(w))
        =
        integral_[0,infinity) frac(d mu(t),w+t)
        quad "with" quad
        mu=sum_(gamma>0)m_gamma delta_(gamma^2).
      $
      Expanding at $w=0$ gives
      $
        frac(H'(w),H(w))
        =
        sum_(n>=0)(-1)^n mu_n w^n,
        quad
        mu_n=integral t^(-n-1)dif mu(t).
      $
      If the resulting reciprocal moment representation is determinate and its
      Stieltjes transform analytically continues as $H'/H$, it exists exactly
      when both Hankel families
      $
        [mu_(i+j)]_(i,j=0)^N,
        quad
        [mu_(i+j+1)]_(i,j=0)^N
      $
      are positive semidefinite for every $N$.
    ],
    derivation: [
      Under RH, zeros $plus.minus i gamma$ fold to $-gamma^2$, and
      $
        H'/H=sum_(gamma>0) frac(m_gamma,w+gamma^2),
      $
      a positive atomic Stieltjes transform. Conversely, a meromorphic
      Stieltjes logarithmic derivative has poles only on the negative real
      axis with positive residues; analytic uniqueness then places the zero
      divisor of $H$ there. The Stieltjes moment theorem is equivalent to the
      two connected Hankel positivity families when its existence hypotheses
      are met.
    ],
    transformations: [
      The fold $w=z^2$ quotients the two seam orientations while retaining
      squared distance. Overlapping Hankel cells are finite receiver windows of
      one moment lineage.
    ],
    boundary: [
      OPEN: construct the positive source measure or Gram representation after
      the nonlinear logarithmic transform. Positive theta moments alone do not
      imply this. The exact analytic/moment determinacy hypotheses must remain
      visible.
    ],
    source: [Classical Stieltjes moment theorem applied to the centered Hadamard product.],
  ),
  entry(
    id: "RH.0050",
    kind: "Equivalence",
    grade: "proved-standard",
    title: [Nyman--Beurling--Báez-Duarte exact closure],
    depends: ("H.0250", "H.0306", "H.0309", "RH.0000"),
    statement: [
      Let $rho(x)=x-floor(x)$ and use the standard fractional-part dilation
      family
      $
        rho_a(x)=rho(1/(a x))
      $
      in $L^2(0,infinity)$. The Báez-Duarte strengthening states that RH is
      equivalent to the indicator of $(0,1)$ belonging to the closed linear
      span of $ {rho_a : a in NN} $.
    ],
    derivation: [
      Mellin--Plancherel transports each fractional-part dilation to a multiple
      of $zeta(s)/s$. Membership of the indicator, whose Mellin transform is
      $1/s$, in the exact Hilbert-space closure is therefore equivalent to a
      sequence of finite-span inverse faces converging in norm on the critical
      boundary. The zero-free half-plane and closure argument give the two
      directions.
    ],
    transformations: [
      Each dilation is a rebase face of the counting discontinuity. The route
      asks whether their finite composites converge to a receiver-exact inverse.
    ],
    boundary: [
      OPEN: construct a finite-span sequence whose global $L^2$ residual
      converges exactly to zero. Pointwise convergence, a formal Möbius inverse,
      or a finite dilation window does not establish norm closure.
    ],
    source: [
      #link("https://arxiv.org/abs/math/0202141")[
        L. Báez-Duarte, A strengthening of the Nyman--Beurling criterion
      ].
    ],
  ),
  entry(
    id: "RH.0060",
    kind: "Equivalence",
    grade: "proved-standard",
    title: [Laguerre--Pólya and Jensen-polynomial hyperbolicity],
    depends: ("H.0109", "H.0250", "H.0310", "RH.0000"),
    statement: [
      Let $gamma(n)$ be the Taylor-coefficient lineage of a standard real
      entire normalization of $Xi$, and define
      $
        J_(gamma)^(d,n)(X)
        =
        sum_(j=0)^d binom(d,j) gamma(n+j)X^j.
      $
      RH is equivalent to membership of $Xi$ in the Laguerre--Pólya class,
      equivalently to hyperbolicity of every $J_(gamma)^(d,n)$.
    ],
    derivation: [
      A real entire function is in the Laguerre--Pólya class exactly when it is
      a locally uniform limit of real-rooted polynomials. Jensen's theorem
      converts this property to real-rootedness of every Jensen polynomial.
      The real zeros of the centered $Xi$ correspond exactly to RH.
    ],
    transformations: [
      $(d,n)$ is a bifiltration: degree is receiver width; $n$ is lineage shift.
      Hyperbolicity means every crossing of that finite coefficient face remains
      on one real orientation.
    ],
    boundary: [
      OPEN: prove hyperbolicity for the complete two-parameter lattice.
      Hyperbolicity for every fixed degree at sufficiently large shift leaves
      an unbounded initial region as degree grows.
    ],
    source: [
      #link("https://arxiv.org/abs/1902.07321")[
        Griffin--Ono--Rolen--Zagier, Jensen polynomials for the Riemann zeta function
      ].
    ],
  ),
  entry(
    id: "RH.0070",
    kind: "Equivalence",
    grade: "proved-standard",
    title: [de Bruijn--Newman phase flow],
    depends: ("H.0018", "H.0253", "H.0308", "H.0310", "RH.0000"),
    statement: [
      A theta-derived Fourier kernel defines
      $
        H_t(z)
        =
        integral_0^infinity exp(t u^2)Phi(u)cos(z u) dif u.
      $
      There is a finite constant $Lambda_("DN")$ such that $H_t$ has only real
      zeros exactly for $t>=Lambda_("DN")$. RH is equivalent to
      $Lambda_("DN")<=0$. Rodgers and Tao proved
      $Lambda_("DN")>=0$, hence RH is equivalent to
      $Lambda_("DN")=0$.
    ],
    derivation: [
      At $t=0$, $H_0$ is a real-variable normalization of the completed zeta
      function. De Bruijn proves forward preservation above a threshold;
      Newman proves existence of the sharp threshold. The centered real-zero
      condition at $t=0$ is RH. Rodgers--Tao establish the opposite inequality.
    ],
    transformations: [
      $t$ is a true parameterized phase flow. The threshold is a discriminant
      at which off-axis conjugate zero pairs collide with or leave the real
      seam.
    ],
    boundary: [
      OPEN: prove real-rootedness at the undeformed face $t=0$. Positivity of
      $Phi$ does not by itself imply real zeros of its Fourier transform, and
      forward regularization does not automatically reverse.
    ],
    source: [
      #link("https://arxiv.org/abs/1801.05914")[
        Rodgers--Tao, The de Bruijn--Newman constant is non-negative
      ].
    ],
  ),
  entry(
    id: "RH.0080",
    kind: "Equivalence",
    grade: "proved-standard",
    title: [Hermite--Biehler, de Branges, and canonical systems],
    depends: ("H.0243", "H.0310", "RH.0000"),
    statement: [
      For entire $E$, let $E^sharp(z)=overline(E(overline(z)))$. The
      Hermite--Biehler inequality
      $
        abs(E(z))>abs(E^sharp(z))
        quad (op("Im")z>0)
      $
      forces the real and imaginary companions to have real interlacing zeros.
      In Suzuki's xi-derived family,
      $
        Theta_omega(z)
        =
        frac(xi(1/2-omega-i z),xi(1/2+omega-i z)),
      $
      RH is equivalent to meromorphic innerness for every $omega>0$.
    ],
    derivation: [
      The quotient $E^sharp/E$ is Schur/inner exactly when the
      Hermite--Biehler orientation holds. De Branges theory realizes such a
      function through a canonical system with a positive-semidefinite
      Hamiltonian. Suzuki identifies the zero-free half-plane
      $op("Re")s>1/2+omega_0$ with innerness for every
      $omega>omega_0$; setting $omega_0=0$ gives RH.
    ],
    transformations: [
      $E,E^sharp$ are opposed oriented faces; $Theta_omega$ is their boundary
      transport; the Hamiltonian is the local metric admitting continuation.
    ],
    boundary: [
      OPEN: construct the xi-derived positive Hamiltonian or innerness for every
      $omega>0$ without using the desired zero-free region. A safe parameter
      range, quotient, or assumed inner function is not the complete bridge.
    ],
    source: [
      #link("https://arxiv.org/abs/1204.1827")[
        M. Suzuki, A canonical system arising from the Riemann zeta-function
      ].
    ],
  ),
  entry(
    id: "RH.0090",
    kind: "Equivalence",
    grade: "proved-standard",
    title: [Speiser critical-point topology],
    depends: ("H.0210", "H.0283", "H.0309", "RH.0000"),
    statement: [
      RH is equivalent to the absence of nonreal zeros of $zeta'(s)$ in
      $
        0<op("Re")s<1/2.
      $
    ],
    derivation: [
      The argument principle and the functional symmetry relate off-seam zeros
      of $zeta$ to branch/critical events in its level-curve topology. Speiser's
      theorem proves both directions: an off-seam zero forces a derivative
      zero in the left half-strip, and such a derivative zero forces failure of
      the critical-line zero geometry.
    ],
    transformations: [
      Zeros of $zeta'$ are genuine inflection/branch events of the holomorphic
      receiver. This is the standard route closest to the laboratory intuition
      about kinks, folds, and receiver-visible critical crossings.
    ],
    boundary: [
      OPEN: exclude every such derivative zero. A visualization of some level
      curves or finite zero window does not supply the global argument.
    ],
    source: [
      Speiser's theorem; modern statement:
      #link("https://arxiv.org/abs/1902.03064")[
        Garunkštis--Tamošiūnas
      ].
    ],
  ),
  entry(
    id: "RH.0100",
    kind: "Programme",
    grade: "conjecture",
    title: [Hilbert--Pólya spectral determinant],
    depends: ("H.0243", "H.0311", "RH.0000"),
    statement: [
      Seek a noncircular Hilbert space and self-adjoint operator $A$ such that
      the complete spectral determinant satisfies
      $
        cal(X)(z)=exp(a+b z)det_*(z I-A)
      $
      with every zero and multiplicity represented.
    ],
    derivation: [
      If such an identity and self-adjointness are proved, spectral parameters
      are real, so zeros of the real-variable $Xi$ lie on its real axis,
      equivalently RH. A trace formula for $A$ must reproduce every prime-power,
      Gamma, and endpoint term in H.0312 to establish the determinant identity.
    ],
    transformations: [
      The spectrum is one receiver; periodic/closed source paths are another.
      The trace formula is the required comparison cell.
    ],
    boundary: [
      OPEN: construct $A$, prove self-adjointness, the exact determinant/trace
      identity, and exhaustivity. Matching zero counts, pair correlation,
      finitely many ordinates, or only the smooth asymptotic is insufficient.
    ],
    source: [
      Hilbert--Pólya programme; Berry--Keating supplies a counting-asymptotic
      model, not the complete determinant.
    ],
  ),
  entry(
    id: "RH.0110",
    kind: "Programme",
    grade: "conditional",
    title: [Trace formula and noncommutative geometry],
    depends: ("H.0312", "RH.0100"),
    statement: [
      Construct an arithmetic dynamical/noncommutative space whose geometric
      trace formula has primitive closed returns at lengths $log p$ and whose
      spectral side is the complete zero divisor of $xi$.
    ],
    derivation: [
      The Selberg trace formula demonstrates this mechanism for zeta functions
      of hyperbolic surfaces. Connes's adèle-class construction realizes
      critical zeros as absorption spectrum and possible off-seam zeros as
      resonances; an exact positive trace identity excluding those resonances
      would imply RH.
    ],
    transformations: [
      Primes are primitive closed source worldlines; prime powers are repeated
      returns; trace is a receiver summing fixed cycles.
    ],
    boundary: [
      OPEN: the complete global trace/positivity theorem with all local factors
      and no residual off-seam resonance.
    ],
    source: [
      #link("https://arxiv.org/abs/math/9811068")[
        A. Connes, Trace formula in noncommutative geometry and the zeros of zeta
      ].
    ],
  ),
  entry(
    id: "RH.0120",
    kind: "Analogue",
    grade: "proved-standard",
    title: [Function-field cohomology and Weil conjectures],
    depends: ("H.0312", "H.0330"),
    statement: [
      For a smooth projective variety $X$ over $FF_q$,
      $
        Z(X,T)
        =
        product_i
        det(1-T "Frob"_(H^i_("et")(X)))^((-1)^(i+1)).
      $
      Deligne's purity theorem places every Frobenius eigenvalue on
      $H^i$ at modulus $q^(i/2)$, proving the function-field RH.
    ],
    derivation: [
      Point counts are traces of Frobenius powers by the Lefschetz trace
      formula. The determinant identity packages those traces into $Z(X,T)$.
      Poincaré duality pairs reciprocal eigenvalues; Deligne's weight/purity
      theorem fixes their modulus, not duality alone.
    ],
    transformations: [
      Frobenius is causal transport; cohomological degree is a typed phase;
      duality pairs opposed faces; purity fixes the half-weight seam.
    ],
    boundary: [
      No accepted classical-number-field object supplies the required
      cohomology, Frobenius evolution, determinant identity, duality, and purity.
      The Weil conjectures are a proven analogue and design constraint, not the
      standard which every holonic proof must imitate.
    ],
    source: [
      #link("https://numdam.org/item/PMIHES_1974__43__273_0/")[
        P. Deligne, La conjecture de Weil I
      ].
    ],
  ),
  entry(
    id: "RH.0130",
    kind: "Equivalence",
    grade: "proved-standard",
    title: [Prime-counting and Möbius residuals],
    depends: ("H.0249", "H.0261", "H.0304", "H.0312", "RH.0000"),
    statement: [
      Standard equivalent forms include
      $
        pi(x)=op("Li")(x)+O(sqrt(x)log x),
      $
      $
        psi(x)=x+O(sqrt(x)log^2 x),
      $
      and
      $
        M(x)=sum_(n<=x)mu(n)
        =
        O_epsilon(x^(1/2+epsilon))
      $
      for every $epsilon>0$.
    ],
    derivation: [
      Perron/Mellin inversion writes counting functions as contour integrals of
      $-zeta'/zeta$ or $1/zeta$. Moving the contour to the seam yields the
      square-root scale under RH. Conversely, any zero with real part
      $beta>1/2$ contributes a residue of scale $x^beta$, contradicting the
      stated bounds.
    ],
    transformations: [
      This is the source residual before the zero receiver. The $1/2$ is the
      sharp scaling exponent forced by the centered zero boundary, not a base-10
      artifact.
    ],
    boundary: [
      OPEN: prove the uniform square-root-scale cancellation. Finite prime
      patterns, digit rotations, and local residue wheels can contribute exact
      source identities but do not alone supply the global bound.
    ],
    source: [
      #link("https://www.claymath.org/wp-content/uploads/2022/05/riemann.pdf")[
        Bombieri, Clay RH account
      ]; standard Möbius equivalence.
    ],
  ),
  entry(
    id: "RH.0140",
    kind: "Equivalence",
    grade: "proved-standard",
    title: [Robin--Lagarias divisor inequalities],
    depends: ("H.0302", "RH.0000"),
    statement: [
      Robin's criterion is
      $
        "RH" arrow.l.r
        sigma(n)<exp(gamma)n log log n
        quad "for every " n>5040.
      $
      Lagarias proved the equivalent elementary inequality
      $
        sigma(n)
        <=
        H_n+exp(H_n)log H_n
        quad "for every " n>=1,
      $
      with equality only at $n=1$.
    ],
    derivation: [
      The maximal order of $sigma(n)/n$ is governed by integers with dense
      small-prime valuation structure. Robin reduces a possible violation to
      the colossally abundant regime and relates its asymptotics to the
      zero-free boundary. Lagarias uses precise bounds comparing
      $H_n$ with $log n+gamma$ to obtain an all-$n$ equivalent form.
    ],
    transformations: [
      Each integer is a valuation/factor-incidence holon; $sigma(n)$ is an
      aggregate divisor receiver which has compressed the individual paths.
    ],
    boundary: [
      OPEN: prove the universal inequality. Checking integers, even extremely
      far, cannot exclude an arbitrarily late violation without an exact
      reduction.
    ],
    source: [
      #link("https://arxiv.org/abs/math/0008177")[
        J. Lagarias, An Elementary Problem Equivalent to the Riemann Hypothesis
      ].
    ],
  ),
  entry(
    id: "RH.0150",
    kind: "Equivalence",
    grade: "proved-standard",
    title: [Bagchi strong recurrence],
    depends: ("H.0019", "H.0250", "H.0254", "H.0309", "RH.0000"),
    statement: [
      On the strip $D={s:1/2<op("Re")s<1}$, RH is equivalent to positive-density
      strong self-recurrence: for every compact $K subset D$ with connected
      complement and every $epsilon>0$,
      $
        liminf_(T arrow.r infinity)
        frac(1,T)
        op("meas"){tau in [0,T]:
          sup_(s in K) abs(zeta(s+i tau)-zeta(s))<epsilon}
        >0.
      $
    ],
    derivation: [
      Voronin-type universality supplies arbitrarily close neighborhood returns
      for nonvanishing target functions. Under RH, $zeta$ is nonzero on $D$, so
      every declared neighborhood of its compact restriction recurs.
      Conversely, this exact recurrence property combined with Rouché/Hurwitz
      zero stability would reproduce any zero under vertical shifts; positive
      density is incompatible with the known zero geometry unless $D$ is
      zero-free.
    ],
    transformations: [
      This is exact self-similarity as recurrence after transport, not identity
      of occurrences. Vertical translation changes the occurrence while one
      compact receiver face enters every declared uniform neighborhood.
    ],
    boundary: [
      OPEN: establish the positive-density recurrence for every compact
      receiver. One numerical recurrence or one compact does not close it.
    ],
    source: [
      Bagchi's strong-recurrence theorem; original dissertation record:
      #link("https://digitalcommons.isical.ac.in/masters-dissertations/41/")[
        Statistical Behaviour and Universality Properties of the Riemann Zeta
        Function and Other Allied Dirichlet Series
      ].
    ],
  ),
  entry(
    id: "RH.0160",
    kind: "Boundary",
    grade: "proved-derived",
    title: [RH falsity is finitely witnessed; independence is a separate metatheorem],
    depends: ("H.0401", "H.0403", "H.0419", "RH.0000", "RH.0140"),
    statement: [
      Exact arithmetic criteria such as RH.0140 give a decidable predicate
      $R_"RH"(n)$ for which
      $
        "RH"
        arrow.l.r
        forall n in NN, R_"RH"(n).
      $
      Therefore an exact machine $M_"RH"$ may enumerate $n$, verify
      $R_"RH"(n)$, and halt at the first failure:
      $
        not "RH"
        arrow.l.r
        exists n, not R_"RH"(n)
        arrow.l.r
        M_"RH" " halts".
      $
      A disproof consequently has a finite checkable witness. A proof must
      carry the universal quantifier by an invariant, descent, spectral
      theorem, positivity theorem in a declared orientation, or another finite
      proof object; it need not enumerate every integer or zero.
    ],
    transformations: [
      In holonic language, the counterexample machine grows an exact causal
      current and stops only at a witnessed obstruction. Proving RH means
      proving that every admitted current preserves a law excluding that halt
      state. Proving independence from a theory $T$ instead concerns the
      topology of $T$'s proof relation: one must establish both
      $T$ does not prove RH and $T$ does not prove $not "RH"$.
    ],
    boundary: [
      As of this registry, there is no accepted proof of RH, counterexample to
      RH, or proof that RH is independent of PA, ZFC, or another named standard
      foundation. Gödel incompleteness alone supplies none of those conclusions.
      Infinite extent, late-emerging structure, fractal self-similarity, and
      computational complexity explain why finite-prefix evidence is
      insufficient; they do not establish formal independence.
    ],
    source: [
      #link("https://www.claymath.org/millennium/riemann-hypothesis/")[
        Clay Mathematics Institute, current RH status
      ];
      #link("https://arxiv.org/abs/math/0008177")[
        Lagarias, an elementary criterion equivalent to RH
      ];
      #link("https://arxiv.org/abs/1605.04343")[
        Yedidia and Aaronson, explicit Turing machines for open statements
      ]; Gödel incompleteness.
    ],
  ),
  entry(
    id: "RH.0900",
    kind: "Atlas",
    grade: "proved-derived",
    title: [Four nonidentical proof mechanisms],
    depends: (
      "RH.0010",
      "RH.0020",
      "RH.0030",
      "RH.0040",
      "RH.0050",
      "RH.0060",
      "RH.0070",
      "RH.0080",
      "RH.0090",
      "RH.0100",
      "RH.0110",
      "RH.0120",
      "RH.0130",
      "RH.0140",
      "RH.0150",
      "RH.0160",
    ),
    statement: [
      The routes separate into four mechanism classes:

      1. source-derived positive response: Weil, Pick, Stieltjes, de Branges;
      2. exact closure and cancellation: Nyman--Beurling, prime/Möbius residual,
         Bagchi;
      3. real-zero-preserving phase dynamics: Jensen, de Bruijn--Newman,
         Speiser;
      4. exact source--spectrum geometry: Hilbert--Pólya, trace formula,
         cohomology.
    ],
    transformations: [
      These are nonidentical receivers of the same completed arithmetic--analytic
      relation. A holonic contribution may construct natural transformations
      between them only when it proves that the route's proof-bearing property
      is preserved.
    ],
    boundary: [
      No route presently closes its universal source-side obligation in this
      registry. Moving an obstruction to another receiver is useful only when
      the transition reduces it, supplies a new invariant, or yields a
      counterexample.
    ],
    source: [Independent laboratory route audit against the cited primary sources.],
  ),
)
