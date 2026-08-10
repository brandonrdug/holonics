#let tower-cross-term-identity = (
  key: "theorem:tower-cross-term-identity",
  kind: [Theorem],
  title: [The cosine cross term, the interference cross term, and the Feynman vertex are one term],
  status: [Exact algebraic identity; the reading is the project's, the algebra is classical],
  depends: (
    "definition:comparison-face",
    "theorem:exact-receiver-turn-return",
  ),
  claim: [
    Relate two carried magnitudes $a,b$ across a turn $gamma$. The returned
    magnitude satisfies
    $
      c^2
      =a^2+b^2-2 a b cos gamma
      =(a-b e^(i gamma))(a-b e^(-i gamma))
      =abs(a-b e^(i gamma))^2.
      quad "(TOWER)"
    $
    Independently, two oriented contributions $alpha_1,alpha_2$ meeting one
    consequence return
    $
      abs(alpha_1+alpha_2)^2
      =abs(alpha_1)^2+abs(alpha_2)^2+2 op("Re")(alpha_1 overline(alpha_2)).
      quad "(INTERFERENCE)"
    $

    *These are the same identity.* Writing $alpha_1=a$, $alpha_2=-b e^(i gamma)$
    carries ("INTERFERENCE") to ("TOWER") term by term, and
    $
      2 op("Re")(alpha_1 overline(alpha_2)) = -2 a b cos gamma
    $
    is the single cross term in both. Three consequences, and each is a
    identification rather than an analogy:

    + *Pythagoras is the tower with the relation switched off.* At
      $gamma=pi\/2$ the cross term vanishes, $c^2=a^2+b^2$, and the two legs
      return nothing about each other. The square corner carries no relating;
      the leaning corner is the relating.
    + *The cross term is the vertex.* A three-line diagram $A,B -> C$ states that
      $C$ is returned *in the frame of* ${A,B}$, and the term that depends on
      both is exactly the term that depends on their relative turn. Orthogonality
      is the vertex with zero coupling.
    + *The three rungs are three returns of one relating.* Sum returns something
      *similar* to its arguments, the cross returns something *orthogonal* to
      them, and the exponent returns something *diagonal*: for
      $A^B$ the axes of $A$ and of $B$ combine orthogonally and the rank climbs.

    At $gamma=pi\/2$ the factorization is the Gaussian norm $a^2+b^2=(a+i b)(a-i b)$,
    so an odd prime that is the hypotenuse of a primitive integer right triangle
    splits in $ZZ[i]$ and is $1 mod 4$: irreducibility is receiver-relative to the
    admitted arithmetic, and the turn is what admits it.
  ],
  proof: [
    Expand $(a-b e^(i gamma))(a-b e^(-i gamma)) = a^2 - a b(e^(i gamma)+e^(-i gamma)) + b^2 e^(i gamma)e^(-i gamma)$.
    Euler gives $e^(i gamma)+e^(-i gamma)=2cos gamma$ and $e^(i gamma)e^(-i gamma)=1$,
    so the product is $a^2+b^2-2 a b cos gamma$, which is the Law of Cosines, and
    it equals $abs(a-b e^(i gamma))^2$ because the two factors are conjugate.

    For ("INTERFERENCE"), $abs(alpha_1+alpha_2)^2=(alpha_1+alpha_2)overline((alpha_1+alpha_2))$
    expands to $abs(alpha_1)^2+abs(alpha_2)^2+alpha_1 overline(alpha_2)+overline(alpha_1)alpha_2$,
    and the last two are conjugates summing to $2op("Re")(alpha_1 overline(alpha_2))$.
    Substituting $alpha_1=a$, $alpha_2=-b e^(i gamma)$ gives
    $2op("Re")(-a b e^(-i gamma))=-2 a b cos gamma$.
  ],
  boundary: [
    This is an identity of *carried magnitudes across one turn*. It does not
    assert that any particular ecology's relating is metric, that its returns are
    complex scalars, or that a diagram of the interaction is a Feynman diagram in
    the physical sense with a propagator, a coupling constant, or a perturbative
    expansion. None of those is supplied here.

    The vertex reading fixes what the diagram *states* -- a return in the frame
    of its two arguments -- and nothing about how the return is computed. In
    curved ambient geometry the composition law is different: the hyperbolic
    counterpart is $cosh(c\/R)=cosh(a\/R)cosh(b\/R)-sinh(a\/R)sinh(b\/R)cos gamma$,
    which recovers ("TOWER") only at first nonconstant order in large $R$. The
    two are related charts and not interchangeable identities.

    The rung reading (sum, cross, exponent) is a *classification of returns*, not
    a theorem that every relating is one of three species.
  ],
)
