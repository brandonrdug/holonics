#let transcendental-accessibility-transport = (
  key: "theorem:transcendental-accessibility-transport",
  kind: [Theorem],
  title: [A transcendental evaluation fiber carries nonidentical arithmetic accessibility currents],
  status: [Exact synthesis of standard series laws and the bounded presentation-topology cell],
  depends: (
    "definition:situated-formulation-family",
    "definition:graded-arithmetic-accessibility-current",
    "definition:prime-valuation-atlas",
  ),
  claim: [
    For a declared exact evaluation law
    $
      "ev":cal(F) arrow.r cal(V),
    $
    the fiber
    $
      cal(E)_tau="ev"^(-1)(tau)
    $
    contains the formulations returning the invariant $tau$.  Its members
    need not have one arithmetic accessibility current.  A proved
    formulation transport $T:F arrow.r G$ has the exact residual
    $
      op("Res")_T
      =
      T_* frak(A)_F-frak(A)_G.
      quad "(FORMULATION RESIDUAL)"
    $
    Vanishing means that this declared transport preserves the decorated
    arithmetic current.  Nonvanishing records entering, departing, or
    rebased axes without denying that $F$ and $G$ return the same $tau$.

    The exponential specialization of a valuation address is
    $
      Phi_s(alpha)
      =
      product_p p^(-s alpha_p)
      =
      exp(-s sum_p alpha_p log p).
      quad "(EXPONENTIAL SPECIALIZATION)"
    $
    For the factorial series of $e$,
    $
      v_p((n+1)!)-v_p(n!)=v_p(n+1),
    $
    so each successor transports the complete valuation current of $n+1$
    into the next denominator.

    For a real rational $x=u/v$ in lowest terms with $v != 0$ and
    $abs(u)<=abs(v)$, let
    $
      A(x)=sum_(n>=0)(-1)^n frac(x^(2n+1),2n+1).
    $
    This is the exact arctangent series, conditionally at its endpoints.  Its
    exact term transport is
    $
      frac(a_(n+1),a_n)
      =
      -frac(u^2(2n+1),v^2(2n+3)),
    $
    hence
    $
      "div"(a_(n+1))-"div"(a_n)
      =
      2"div"(u)-2"div"(v)
      +"div"(2n+1)-"div"(2n+3).
      quad "(ARCTANGENT CURRENT)"
    $
    If an odd prime $p$ divides $v$, collisions with the moving odd current
    lie on the exact modular sheets
    $
      2n+1 equiv 0 mod p^k
      quad "or" quad
      2n+3 equiv 0 mod p^k.
      quad "(COLLISION SHEETS)"
    $

    Thus the Machin presentation
    $
      pi=16A(1/5)-4A(1/239)
    $
    has parameter axes $5,239$, while its Gaussian norm closure uses
    $
      1+5^2=2 dot 13,
      quad
      1+239^2=2 dot 13^4.
    $
    These are two related receiver faces, not one fixed “prime support of
    $pi$.”  In the first twelve term transitions, the $1/5$ arm crosses two
    $5$-collision sheets and cancels $5^2$ internally; the $1/239$ arm
    crosses no $239$-sheet.  The fixed Chudnovsky scale similarly has exact
    support
    $
      640320=2^6 dot 3 dot 5 dot 23 dot 29.
    $
  ],
  proof: [
    The residual is the definition of comparing two decorated currents after
    transport.  The exponential identity follows by substituting the
    valuation factorization into $n^(-s)$.  The factorial identity follows
    from $(n+1)!=(n+1) n!$.  Dividing consecutive arctangent terms gives
    ("ARCTANGENT CURRENT"); taking prime valuations gives the collision
    congruences.  The two Gaussian norm factorizations and the factorization
    of $640320$ are direct integer identities.  Solving the displayed
    congruences in the bounded twelve-transition aperture gives the two
    $5$-sheet crossings and no $239$-sheet crossing recorded by the exact
    presentation-topology cell.
  ],
  boundary: [
    Equal evaluation is not a license to identify formulations, and unequal
    coefficient support is not a contradiction.  The bounded collision
    statement is exact only in its named aperture.  This theorem does not
    assign one universal prime taxonomy to a transcendental invariant or
    infer the Riemann zero set from coefficient supports.  It supplies the
    exact mixed arithmetic/formulation direction which such a global
    transport theorem would have to use.
  ],
)
