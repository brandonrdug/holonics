#let radix-residue-character-cell = (
  key: "definition:radix-residue-character-cell",
  kind: [Definition],
  title: [Radix, residue, and character faces of one bounded counting occurrence],
  status: [Classical finite arithmetic objects; laboratory incidence presentation],
  depends: (
    "definition:receiver",
    "definition:formulation-span-atlas",
  ),
  claim: [
    Fix integers $b,q>=2$ and a digit depth $K>=1$.  The radix word space,
    value map, and residue receiver are
    $
      D_(b,K)={0,1,...,b-1}^K,
      quad
      V_(b,K)(d)=sum_(k=0)^(K-1)d_k b^k,
    $
    $
      rho_(b,q,K)=pi_q compose V_(b,K):D_(b,K) arrow.r C_q,
      quad C_q=ZZ/q ZZ.
    $
    The *place-incidence word*
    $
      w_(b,q)(k)=b^k mod q
    $
    gives the receiver directly:
    $
      rho_(b,q,K)(d)
      =
      sum_(k=0)^(K-1)d_k w_(b,q)(k)
      quad "in" C_q.
      quad "(PLACE)"
    $

    Let $X$ denote the generator of the integral group algebra
    $ZZ[C_q]=ZZ[X]/(X^q-1)$.  The complete bounded population is
    $
      G_(b,q,K)(X)
      =
      product_(k=0)^(K-1)
      (
        sum_(d=0)^(b-1)X^(d w_(b,q)(k))
      )
      =
      sum_(a in C_q)c_a X^a.
      quad "(POPULATION)"
    $
    The coefficient $c_a$ is exactly the cardinality of the complete fiber
    $rho_(b,q,K)^(-1)(a)$.

    After extending scalars to a field containing a primitive $q$-th root
    $omega_q$, the character face and its inverse are
    $
      hat(G)(j)
      =
      G_(b,q,K)(omega_q^j)
      =
      sum_(a in C_q)c_a omega_q^(j a),
    $
    $
      c_a
      =
      1/q sum_(j in C_q)
      omega_q^(-j a)hat(G)(j).
      quad "(CHARACTER)"
    $

    For an actual bounded integer occurrence set $O$, a radix presentation
    is an injective map
    $
      r_b:O arrow.r D_(b,K)
    $
    satisfying $V_(b,K)r_b(n)=n$.  Two such radix maps $r_b,r_(b')$ are
    invertible recharts of the same occurrences through $O$.  The residue
    map $pi_q:O arrow.r C_q$ is instead a quotient receiver with complete
    fibers.  The coefficient-to-character transform in ("CHARACTER") is
    again invertible after the declared scalar extension.
  ],
  proof: none,
  boundary: [
    A radix presentation, a residue quotient, and a linear character basis
    are three different operations.  Calling all three a “basis change”
    erases whether the passage is invertible.  A change of radix is a rechart
    only on a common occurrence set and with enough digits to represent it.
    The factor $1/q$ is the inverse finite-character normalization; it is not
    caused by the radix and it does not identify all other occurrences of the
    same rational glyph.  For composite $q$, a cyclotomic scalar extension
    and its chosen basis must still be declared.
  ],
)
